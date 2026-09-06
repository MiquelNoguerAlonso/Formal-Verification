# Formal Market Microstructure, Paper II: Lean development

The complete source for *Formal Market Microstructure in U.S. Equities II*, by Miquel Noguer i Alonso,
Artificial Intelligence Finance Institute (2026).

Paper DOI: [10.5281/zenodo.22392230](https://doi.org/10.5281/zenodo.22392230).

## Build

Lean 4.22.0, release commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`,
core library only. No Mathlib dependency.

```sh
lake build
python3 audit.py
lake build allocation_record
python3 verify_checker.py
lake env lean --run ../scripts/export_figure_data.lean > ../figures/figure_data.json
```

There are 391 theorem declarations with 391 matching `#print axioms` commands.
`TapeConformance.lean` adds 29 declarations to the 362-declaration foundations
baseline. Its new declarations use at most `propext` and `Quot.sound`; six of
its seven worked-instance declarations use no axioms. There are 48 inherited
`Classical.choice` dependencies, listed in the root `proof_audit.json`.

## Paper II interfaces

| Interface | Input contract | Result |
|---|---|---|
| `tapeView` | An allocation vector | Total filled quantity |
| `conformsPT` | Authenticated queue, incoming quantity and aligned fills | Exact price-time comparison |
| `wheelConsistent` | Remaining claims, cyclic order, lot, fuel, quantity stream and participant-aligned observations | Existence of an explaining candidate rotation and allowance |
| `labelledPriceTime` | Unique order IDs, labelled timestamped queue and quantity | Fills restored to a fixed external ID order |
| `conformsPTδ` | The same fixed IDs and fills, plus a swap bound and uncertainty threshold | Existence of a labelled explaining queue |

`twoOrder_masking_iff` requires the two possible priority orders to produce
different labelled fills. It is an exact two-order threshold, not a converse
for arbitrary queues. `ex_equal_size_clock_jump` protects order identity even
when the two quantities are equal.

The wheel's `candidates_length` counts list entries, not distinct predictive
classes for all possible claims. Its zero allocated counters are measured from
the audit boundary; a partial allowance may reflect unknown earlier history.
With positive lot and allowance, fuel `1 + sum initial_remaining` suffices for
complete fixed-claim replay. The Boolean theorems themselves compare the fuel
supplied by the caller.

## Inherited modules

`Rule737`, `Markets`, `Balance`, `Rulebook`, `Orders`, `Strategic`, `SetterRace`,
`Closure`, `Conformance`, `Collisions`, `Algebra`, `MoreRules`,
`PathIndependence`, `WheelInformation` and `ClauseComplete` supply the Paper I
baseline. `Check` audits both papers. `AllocationRecord` is the standalone
price-time input checker; `verify_checker.py` covers 12 input and diagnostic
cases. It does not parse exchange feeds.

The inherited fixed regulatory ledger contains 58 rows with partition
43 + 5 + 3 + 7. Its catalogue includes 17 Nasdaq order types and 13 attribute
families. These are source audit lemmas, not a certification of law, supplied
attestations or a production system. Paper II adds no regulatory claims.

The workflow in `lmr/.github/` is usable when this directory is a repository
root. The outer package workflow also verifies the figure data and independent
numerical examples. Source publication is planned at
[MiquelNoguerAlonso/Formal-Verification](https://github.com/MiquelNoguerAlonso/Formal-Verification).
