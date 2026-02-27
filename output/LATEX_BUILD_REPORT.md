# LATEX_BUILD_REPORT

- Date: 2026-02-27
- Workspace: `/Users/fwmbam4/CodeHub/Frankie/ClassificationOfIntegersOfQuadraticNumberFields`
- Target: `tex/report/report.tex`
- Template base: copied from `/Users/fwmbam4/CodeHub/Frankie/GroupAction/tex/report`

## Content profile (this build)

- Report expanded to Chapter-2 style exposition (Definition/Proposition style).
- Each Lean `def/lemma/theorem` in the main modules is restated in mathematical form.
- Includes line-linked Lean code excerpts for key theorem blocks.

## Build command

```bash
cd tex/report
latexmk -xelatex -shell-escape -interaction=nonstopmode -halt-on-error -output-directory=out report.tex
```

## Result

- Status: SUCCESS
- PDF: `tex/report/out/report.pdf`
- Page count: 13

## Non-fatal warnings

- `fancyhdr` headheight suggestion from template class.
- `hyperref` warnings for math tokens in section titles.
- `minted` font warning for Unicode angle brackets in code font.
