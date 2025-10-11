Paper Setup

- Build: `make` (uses `latexmk` + `pdflatex`).
- Watch: `make watch` (auto-rebuild on change).
- Clean: `make clean`.
- ArXiv zip: `make arxiv` (packages `.tex`, `.bbl`, and figures into `dist/paper-arxiv.zip`).

Prerequisites

- TeX distribution (TeX Live or MacTeX) with `latexmk` available in PATH.
- Optional: `bibtex` (used automatically by `latexmk`).

Notes

- Edit `paper.tex` and `refs.bib` to suit your project.
- Place figures under `figures/` and reference with `\includegraphics{figures/<name>}`.
- The ArXiv target generates a `.bbl` and zips sources for upload.
