# Formal Verification

Lean 4 proofs, executable allocation rules, and reproducible research on
U.S. equity market microstructure by **Miquel Noguer i Alonso (AIFI)**.

## Paper 1

**Foundations of Formal Market Microstructure in U.S. Equities:**
*Machine-Checked Allocation, Composition, Necessary State, and Regulatory
Traceability.*

[Read the paper](fmm.pdf) ·
[Paper DOI: 10.5281/zenodo.22343804](https://doi.org/10.5281/zenodo.22343804) ·
[Proof guide](lmr/README.md)

Splitting an incoming quantity into smaller orders can change who receives
shares if a round-robin allocation wheel restarts each time. The formal
development proves that preserving the wheel's position and remaining lot
allowance restores consistency between split and combined quantities with no intervening order-book changes and under
the stated assumptions. On reachable states, the allowance can be recovered
from the current participant's cumulative allocation. Further results identify
the pointer information needed to predict future fills on specified families
of states.

The package also includes price-time allocation, conservation and balance
results, a command-line allocation checker, and a dated regulatory
traceability ledger. The full statements and their assumptions are in the
paper and the [Lean source guide](lmr/README.md).

## Repository contents

| Path | Contents |
| --- | --- |
| `fmm.pdf` | Paper 1, including its regulatory appendix |
| `fmm.tex`, `refs.bib` | Paper and bibliography sources |
| `lmr/` | Lean definitions, proofs, allocation checker, and audit scripts |
| `figures/` | Five 450-dpi PNG figures and Lean-exported numerical data |
| `scripts/` | Data exporter, independent numerical checks, and figure renderer |
| `numerical_review.json` | Finite numerical verification results |
| `.github/workflows/lean.yml` | Automated Lean build and checker verification |
| `build_release.sh` | Reproducible PDF build entry point |
| `proof_audit.json` | Declaration counts and classical-choice dependency list |
| `CITATION.cff` | Machine-readable citation metadata |
| `LICENSE` | MIT license |
| `MANIFEST.sha256` | SHA-256 hashes for the distributed files |

## Check the proofs

Install [Lean and Lake](https://lean-lang.org/install/) and Python 3. The
`lmr/lean-toolchain` file selects **Lean 4.22.0**. The development uses the
Lean core library and has no Mathlib or other Lake package dependencies.

From the repository root:

```sh
cd lmr
lake build
python3 audit.py
lake build allocation_record
python3 verify_checker.py
./.lake/build/bin/allocation_record < sample.allocation
```

`lake build` checks the proofs and prints the axiom dependencies recorded in
`Check.lean`. The release contains **362 theorem declarations**; 48 have
`Classical.choice` among their proof dependencies. The separate static audit
checks that every declaration has a corresponding axiom-report command and
rejects proof placeholders and explicitly forbidden source constructs.

The executable verification script checks 12 parsing and conformance cases.
The sample file deliberately contains both conforming and nonconforming
allocations, so its output includes both acceptance and rejection messages.

The **Lean artifact** workflow runs on pushes, pull requests, and manual
dispatch. It builds the Lake package in `lmr/`, runs the static audit, builds
the checker, exercises its sample and regression cases, and checks
Lean-exported figure data against an independent Python implementation. Results appear in
the repository's **Actions** tab. The workflow's action references are pinned
to commits, and its token has read-only repository-content permissions.

## Rebuild the paper

Install a TeX distribution with `latexmk`, `pdflatex`, `bibtex`, and the
packages listed in `fmm.tex`. From the repository root, run:

```sh
sh build_release.sh
```

The script fixes the source epoch, timezone, and locale. The LaTeX source
fixes PDF metadata used for reproducible builds. Rebuilding requires the
stated TeX environment; it is separate from the Lean workflow.

On systems with `sha256sum`, verify the distributed files before modifying
them with:

```sh
sha256sum -c MANIFEST.sha256
```

The manifest excludes itself and generated build files.

## Figures and numerical checks

The five PNG figures visualize allocation, the computed water-level bound,
stream composition, auction price selection, and future-state probes. They
are generated from the executable Lean definitions and independently checked
in Python. They illustrate the mathematical model and are not empirical data.

To regenerate all figure inputs and images from the repository root:

```sh
cd lmr
lake build
lake env lean --run ../scripts/export_figure_data.lean > ../figures/figure_data.json
cd ..
python3 scripts/numerical_review.py
python3 -m pip install -r scripts/requirements-figures.txt
python3 scripts/generate_figures.py
sh build_release.sh
```

The supplied PNGs are ready for LaTeX; Matplotlib is needed only to regenerate
them. The independent checks cover 15,306 reachable runs, 168,744 split-versus-
combined comparisons, 15,306 pass-wheel bounds, and 2,310 phase pairs.
These finite checks supplement the general Lean proofs.

The Nasdaq catalogue includes 17 named order types and 13 lettered attribute
families under Rules 4702(b)(1)-(17) and 4703(a)-(m). Extended Trading Close is
included as a type; Rule 4755 procedures remain outside the fixed ledger.

## Scope

Lean verifies deductions from the encoded definitions and assumptions. It
does not establish that a production exchange implements those definitions or
that externally supplied records are complete and authentic. The allocation
checker requires an order-level queue and aligned fills.

The regulatory appendix and its 58-row ledger describe a fixed September 2026
snapshot. Their numerical checks and audit lemmas do not establish legal
interpretation or the truth of procedural attestations. The paper distinguishes
its Lean proofs from analytic arguments that are not formalized in this
development.

## Citation and license

Please cite Paper 1 using
[10.5281/zenodo.22343804](https://doi.org/10.5281/zenodo.22343804).
That DOI identifies the paper. When reporting a software result, also record
the Git commit used to build it. See [CITATION.cff](CITATION.cff) for citation
metadata and [LICENSE](LICENSE) for the MIT license.
