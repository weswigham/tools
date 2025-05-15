// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package golang

import (
	"bytes"
	"context"
	"fmt"
	"go/ast"
	"go/format"
	"go/token"
	"path/filepath"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/gopls/internal/cache"
	"golang.org/x/tools/gopls/internal/cache/parsego"
	"golang.org/x/tools/gopls/internal/file"
	"golang.org/x/tools/gopls/internal/protocol"
	"golang.org/x/tools/gopls/internal/util/bug"
	"golang.org/x/tools/gopls/internal/util/safetoken"
	"golang.org/x/tools/internal/imports"
)

// This file defines the code action "Extract declarations to package X".
// canExtractToPackage reports whether the code in the given range can be extracted to a new file.
func canExtractToNewPackage(pgf *parsego.File, start, end token.Pos) bool {
	_, _, _, ok := selectedToplevelDecls(pgf, start, end) // defined in extracttofile.go
	return ok
}

// ExtractToPackage moves selected declarations into a new file.
// When you extract a set of declarations to a new package, it has two broad possible shapes to end in a correct state:
//
// 1. The new package is conceptually "upstream" of the source package
//   - The extracted declarations contain no references to the source package that are not also extracted
//   - All references to elements moved are updated to the new package from the old package
//
// 2. The new package is conceptually "downstream" of the source package
//   - There are no references to the moved elements outside the selection
//   - The selected elements can freely contain references to the old source's exports
//
// If neither case is true, the extraction will result in a circular import scenario that would need further work to fix.
func ExtractToPackage(ctx context.Context, snapshot *cache.Snapshot, fh file.Handle, rng protocol.Range, dest protocol.DocumentURI, destSpec string) ([]protocol.DocumentChange, error) {
	errorPrefix := "ExtractToPackage"

	pkg, pgf, err := NarrowestPackageForFile(ctx, snapshot, fh.URI())
	if err != nil {
		return nil, err
	}

	partialPkgName := destSpec
	if len(partialPkgName) == 0 {
		partialPkgName = dest.Path()
		vol := filepath.VolumeName(partialPkgName)
		if len(vol) > 0 {
			partialPkgName = partialPkgName[len(vol)+1:]
		}
		partialPkgName = strings.ReplaceAll(partialPkgName, "\\", "/")
	}
	pkgname := imports.ImportPathToAssumedName(partialPkgName)

	start, end, err := pgf.RangePos(rng)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", errorPrefix, err)
	}

	// Expand the selection, and compute the portion to extract.
	start, end, firstSymbol, ok := selectedToplevelDecls(pgf, start, end)
	if !ok {
		return nil, fmt.Errorf("invalid selection")
	}
	pgf.CheckPos(start) // #70553
	// Inv: start is valid wrt pgf.Tok.

	// select trailing empty lines
	offset, err := safetoken.Offset(pgf.Tok, end)
	if err != nil {
		return nil, err
	}
	rest := pgf.Src[offset:]
	spaces := len(rest) - len(bytes.TrimLeft(rest, " \t\n"))
	end += token.Pos(spaces)
	pgf.CheckPos(end) // #70553
	if !(start <= end) {
		bug.Reportf("start: not before end")
	}
	// Inv: end is valid wrt pgf.Tok; env >= start.
	fileStart := pgf.File.FileStart
	pgf.CheckPos(fileStart) // #70553
	if !(0 <= start-fileStart) {
		bug.Reportf("start: out of bounds")
	}
	if !(int(end-fileStart) <= len(pgf.Src)) {
		bug.Reportf("end: out of bounds")
	}
	// Inv: 0 <= start-fileStart <= end-fileStart <= len(Src).
	src := pgf.Src[start-fileStart : end-fileStart]

	replaceRange, err := pgf.PosRange(start, end)
	if err != nil {
		return nil, bug.Errorf("invalid range: %v", err)
	}

	adds, deletes, err := findImportEdits(pgf.File, pkg.TypesInfo(), start, end)
	if err != nil {
		return nil, err
	}

	var importDeletes []protocol.TextEdit
	// For unparenthesised declarations like `import "fmt"` we remove
	// the whole declaration because simply removing importSpec leaves
	// `import \n`, which does not compile.
	// For parenthesised declarations like `import ("fmt"\n "log")`
	// we only remove the ImportSpec, because removing the whole declaration
	// might remove other ImportsSpecs we don't want to touch.
	unparenthesizedImports := unparenthesizedImports(pgf)
	for _, importSpec := range deletes {
		if decl := unparenthesizedImports[importSpec]; decl != nil {
			importDeletes = append(importDeletes, removeNode(pgf, decl))
		} else {
			importDeletes = append(importDeletes, removeNode(pgf, importSpec))
		}
	}

	referenceUpdatesByFile := make(map[*parsego.File][]protocol.TextEdit)
	prefix := pkgname + "."
	for _, decl := range pgf.File.Decls {
		if posRangeIntersects(start, end, decl.Pos(), decl.End()) {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				err := editRefsForMovedDeclarationName(ctx, pkg, d.Name, snapshot, fh, start, end, referenceUpdatesByFile, prefix)
				if err != nil {
					return nil, err
				}
			case *ast.GenDecl:
				switch d.Tok {
				case token.VAR, token.CONST:
					for _, spec := range d.Specs {
						for _, name := range spec.(*ast.ValueSpec).Names {
							err := editRefsForMovedDeclarationName(ctx, pkg, name, snapshot, fh, start, end, referenceUpdatesByFile, prefix)
							if err != nil {
								return nil, err
							}
						}
					}
				case token.TYPE:
					for _, spec := range d.Specs {
						name := spec.(*ast.TypeSpec).Name
						err := editRefsForMovedDeclarationName(ctx, pkg, name, snapshot, fh, start, end, referenceUpdatesByFile, prefix)
						if err != nil {
							return nil, err
						}
					}
				case token.IMPORT:
					return nil, fmt.Errorf("cannot extract imports to new file")
				}
			}
		}
	}

	var buf bytes.Buffer
	if c := CopyrightComment(pgf.File); c != nil {
		start, end, err := pgf.NodeOffsets(c)
		if err != nil {
			return nil, err
		}
		buf.Write(pgf.Src[start:end])
		// One empty line between copyright header and following.
		buf.WriteString("\n\n")
	}

	if c := buildConstraintComment(pgf.File); c != nil {
		start, end, err := pgf.NodeOffsets(c)
		if err != nil {
			return nil, err
		}
		buf.Write(pgf.Src[start:end])
		// One empty line between build constraint and following.
		buf.WriteString("\n\n")
	}

	fmt.Fprintf(&buf, "package %s\n", pkgname)
	if len(adds) > 0 {
		buf.WriteString("import (")
		for _, importSpec := range adds {
			if importSpec.Name != nil {
				fmt.Fprintf(&buf, "%s %s\n", importSpec.Name.Name, importSpec.Path.Value)
			} else {
				fmt.Fprintf(&buf, "%s\n", importSpec.Path.Value)
			}
		}
		buf.WriteString(")\n")
	}
	// If this is a "downstream" extract, we can add a `import . "path/to/old/package"` to keep all the refs functioning, which can later be made explicit
	// We can assume this is a "downstream" extract if we didn't find any upstream renames to do
	rangeContainsDeclarationsWithUpdatedReferences := false
	for _, elem := range referenceUpdatesByFile {
		if len(elem) > 0 {
			rangeContainsDeclarationsWithUpdatedReferences = true
		}
	}
	if !rangeContainsDeclarationsWithUpdatedReferences {
		buf.WriteString("import . ")
		fmt.Fprintf(&buf, "\"%s\"\n", pkg.Metadata().PkgPath)
	}

	newFile, err := chooseNewFile(ctx, snapshot, dest.Path(), firstSymbol)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", errorPrefix, err)
	}

	buf.Write(src)

	newFileContent, err := format.Source(buf.Bytes())
	if err != nil {
		return nil, err
	}

	// Include changes caused by ref updates in the main file (not allowed to edit the same file twice in a single change request)
	for file, updates := range referenceUpdatesByFile {
		if file.URI != fh.URI() {
			continue
		}
		handle := snapshot.FindFile(file.URI)
		updates, err = addImportEditsToFileEdits(ctx, snapshot, file, handle, dest, destSpec, updates)
		if err != nil {
			return nil, err
		}
		importDeletes = append(importDeletes, updates...)
	}

	changes := []protocol.DocumentChange{
		// edit the original file
		// TODO: Update all references to declarations in range to use an import
		protocol.DocumentChangeEdit(fh, append(importDeletes, protocol.TextEdit{Range: replaceRange, NewText: ""})),
		// create a new file
		protocol.DocumentChangeCreate(newFile.URI()),
		// edit the created file
		protocol.DocumentChangeEdit(newFile, []protocol.TextEdit{
			{Range: protocol.Range{}, NewText: string(newFileContent)},
		})}

	// Add updates for all references
	for file, updates := range referenceUpdatesByFile {
		if file.URI == fh.URI() {
			continue // already added
		}
		handle := snapshot.FindFile(file.URI)
		updates, err = addImportEditsToFileEdits(ctx, snapshot, file, handle, dest, destSpec, updates)
		if err != nil {
			return nil, err
		}
		changes = append(changes, protocol.DocumentChangeEdit(
			handle,
			updates,
		))
	}

	return changes, nil
}

func addImportEditsToFileEdits(ctx context.Context, snapshot *cache.Snapshot, file *parsego.File, handle file.Handle, dest protocol.DocumentURI, destSpec string, updates []protocol.TextEdit) ([]protocol.TextEdit, error) {
	pkg, _, err := NarrowestPackageForFile(ctx, snapshot, handle.URI())
	if err != nil {
		return updates, err
	}
	if len(destSpec) == 0 {
		relative, err := filepath.Rel(handle.URI().DirPath(), dest.Path())
		if err != nil {
			return updates, err
		}
		relative = "./" + relative
		// The import has to be built ad-hoc, as the new package isn't going to exist on disk yet
		destSpec = strings.ReplaceAll(filepath.Join(string(pkg.Metadata().PkgPath), relative), "\\", "/")
	}
	err = snapshot.RunProcessEnvFunc(ctx, func(ctx context.Context, o *imports.Options) error {
		edits, err := ComputeImportFixEdits(snapshot.Options().Local, file.Src, &imports.ImportFix{
			StmtInfo: imports.ImportInfo{
				ImportPath: destSpec,
			},
		})
		if err != nil {
			return err
		}
		updates = append(edits, updates...)
		return nil
	})

	return updates, err
}

func editRefsForMovedDeclarationName(ctx context.Context, pkg *cache.Package, name *ast.Ident, snapshot *cache.Snapshot, fh file.Handle, start token.Pos, end token.Pos, referenceUpdatesByFile map[*parsego.File][]protocol.TextEdit, prefix string) error {
	p := safetoken.StartPosition(pkg.FileSet(), name.Pos())
	pos := protocol.Position{
		Line:      uint32(p.Line - 1),   // Line is zero-based
		Character: uint32(p.Column - 1), // Character is zero-based
	}
	refs, err := references(ctx, snapshot, fh, pos, false)
	if err != nil {
		return err
	}

	for _, ref := range refs {
		refPkg, refFile, err := NarrowestPackageForFile(ctx, snapshot, ref.location.URI)
		if err != nil {
			return err
		}
		refstart, refend, err := refFile.RangePos(ref.location.Range)
		if err != nil {
			return err
		}

		if ref.location.URI == fh.URI() {
			if posRangeIntersects(start, end, refstart, refend) {
				continue // ref is inside selection, no need to adjust
			}
		}

		if !name.IsExported() {
			return fmt.Errorf("Selected declaration %s is not public and cannot be moved becase it is referenced outside the selection - try renaming it", name.Name)
		}

		path, _ := astutil.PathEnclosingInterval(refFile.File, refstart, refend)
		_, ok := path[0].(*ast.Ident)
		if !ok {
			continue // unknown ref kind?
		}
		if parent, ok := path[1].(*ast.SelectorExpr); !ok {
			// insert `pkgname.` before Ident reference
			// This will replace a ref through a `import . "pkg"` with an explicit import ref. This seems fine, but could be somehow configurable.
			referenceUpdatesByFile[refFile] = append(referenceUpdatesByFile[refFile], protocol.TextEdit{
				Range: protocol.Range{
					Start: ref.location.Range.Start,
					End:   ref.location.Range.Start,
				},
				NewText: prefix,
			})
		} else {
			// replace existing `pkg.Name` with `newpkg.Name`
			parentStart := safetoken.StartPosition(refPkg.FileSet(), parent.Pos())
			parentStartPos := protocol.Position{
				Line:      uint32(parentStart.Line - 1),   // Line is zero-based
				Character: uint32(parentStart.Column - 1), // Character is zero-based
			}
			referenceUpdatesByFile[refFile] = append(referenceUpdatesByFile[refFile], protocol.TextEdit{
				Range: protocol.Range{
					Start: parentStartPos,
					End:   ref.location.Range.End,
				},
				NewText: prefix + name.Name,
			})
		}
	}
	return nil
}
