# Formal Market Microstructure in U.S. Equities II

**Observable Conformance, Latent-State Identification, and Clock Uncertainty**  
Formal Market Microstructure, Paper II  
Miquel Noguer i Alonso · Artificial Intelligence Finance Institute · September 5, 2026

Paper DOI: [10.5281/zenodo.22392230](https://doi.org/10.5281/zenodo.22392230).

The paper studies which matching-rule deviations can be distinguished from
supplied observations. It treats total-only observations, exact order-aligned
fills, latent parity-wheel phases, and an explicit model of uncertain priority.
Clock comparisons preserve fixed order identities across candidate queues.

## Contents

- `fmm2.pdf`: the paper, including three PNG figures, keywords and linked contents.
- `fmm2.tex`, `refs.bib`: LaTeX and bibliography source.
- `lmr/`: complete Lean 4.22.0 development, including `TapeConformance.lean`.
- `figures/`: PNGs, exported Lean examples and synthetic simulation data.
- `scripts/export_figure_data.lean`: exports the actual executable examples.
- `scripts/generate_figures.py`: independently checks the examples and recreates figures and the probability table.
- `tables/masking_rows.tex`: generated simulation table rows.
- `build_release.sh`: PDF build entry point.
- `proof_audit.json`: declaration counts, axiom dependencies and validation facts.
- `CITATION.cff`, `LICENSE`, `MANIFEST.sha256`: citation, licensing and file hashes.

## Check the formal development

Install the toolchain pinned by `lmr/lean-toolchain`, then run:

```sh
cd lmr
lake build
python3 audit.py
lake build allocation_record
python3 verify_checker.py
lake env lean --run ../scripts/export_figure_data.lean > ../figures/figure_data.json
cd ..
python3 scripts/generate_figures.py --check-only
```

Lean checks 391 theorem declarations, including 29 in `TapeConformance.lean`.
Every declaration has a matching axiom report. None of the 29 new declarations
depends on `Classical.choice`; 48 inherited declarations do. Six of the seven
new worked-instance declarations use no axioms. Counts include supporting
lemmas and finite instances. They are not counts of independent contributions.
The core library is sufficient; Mathlib is not required.

The independent numerical check compares all plotted replay observations and
survivor counts with Lean exports. It also checks 2,048 separating two-order
clock cases, including equal quantities and reversed external identifier order.
The inherited command-line checker has 12 parser and conformance regressions.

## Rebuild figures and PDF

Python 3 and Matplotlib 3.10.8 recreate the three PNG figures:

```sh
python3 -m pip install -r requirements-figures.txt
python3 scripts/generate_figures.py
sh build_release.sh
```

The PDF needs `latexmk`, pdfLaTeX, BibTeX and the packages listed in `fmm2.tex`.
TeX Live 2023 and 2026 are supported. On Overleaf, select `fmm2.tex` as the main
document and pdfLaTeX as the compiler. The separate Overleaf ZIP uses `main.tex`.
The PDF build fixes its source epoch, timezone and variable PDF metadata.
The PNGs are already included, so rebuilding the PDF does not require Python.

The simulation uses 200,000 exponential draws, `random.Random(7)`, rate 1,
and one shared sample across thresholds. It is synthetic, not market data.
The candidate-filter figure uses claims `(700,500,900,600,800)`, lot 100 and
fuel 3501. A first quantity of 250 leaves one of 500 candidates; a first quantity
of 500 leaves all 500 candidates. The source records both cases.

## Interpretation and availability

Acceptance means compatibility with the supplied model and admissible initial
family. Rejection excludes that family for those inputs. Neither authenticates
market data nor certifies a production venue or legal compliance. The clock
uncertainty family must respect trustworthy sequence information. Participant
identifiers must be unique and fills correctly aligned. The wheel replay fixes
remaining claims and cyclic order during its observation window.

The package includes source code. The GitHub repository is
[MiquelNoguerAlonso/Formal-Verification](https://github.com/MiquelNoguerAlonso/Formal-Verification).
The companion Paper I has the separate DOI
[10.5281/zenodo.22343804](https://doi.org/10.5281/zenodo.22343804).
Use the Paper II DOI above to cite this paper.
