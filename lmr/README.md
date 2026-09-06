# lean-market-rules — Lean 4 certificates for formal market microstructure

Formal source for *Foundations of Formal Market Microstructure in U.S. Equities* (AIFI, 2026).

**Toolchain.** Lean 4.22.0 release commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`, core library only — no Mathlib, no dependencies.
**Status.** 362 theorem declarations, 0 `sorry`, 0 warnings. `Check.lean` audits all 362 declarations; each depends on at most `propext`, `Quot.sound`, and `Classical.choice`.

## Build

```
lake build            # all modules + Check.lean (axiom audit printed as info lines)
lake build allocation_record       # queue-aligned conformance checker
./.lake/build/bin/allocation_record < sample.allocation
python3 audit.py       # exact theorem/Check coverage + forbidden-token guard
python3 verify_checker.py           # 12 parser/conformance regression cases
```

## If you are new to Lean

Lean is a proof checker. Each `.lean` file contains definitions and statements
plus proofs that Lean verifies mechanically. You do not need to understand Lean
syntax to use the results:

- `lake build` checks the entire formal development. A successful build means
  every stated theorem follows from its listed assumptions.
- `Check.lean` asks Lean to report the logical dependencies of every theorem.
- `AllocationRecord.lean` is an ordinary executable checker: it compares a
  proposed queue-aligned price-time allocation with a supplied order-level
  queue. This privileged record is not asserted to be a public trade tape.
- A theorem name in backticks is simply a stable cross-reference from the paper
  to the exact machine-checked statement.

Formal verification checks the deduction inside the model. `ClauseComplete.lean`
maps 58 expressly cited paragraphs, paragraph ranges, or identified
guidance/order items in the fixed, dated
corpus to compiler-linked destinations and checks the encoded logical records.
Each destination carries an actual Lean value, function, projection, or tuple;
the ledger also has checked row/family counts and unique citations. Only its
explicit finite catalogues have exhaustiveness theorems. It does not prove that
the mappings are legally faithful or sufficient, that supplied procedural
attestations or underlying evidence are true, that a production venue
implements the specification, or that
an order book reconstructed from messages is complete.
Without Lake: `LEAN_PATH=. lean -o X.olean X.lean` in the order
Rule737 → Markets → Balance → Rulebook → Orders → Strategic → SetterRace → Closure → Conformance → Collisions → Algebra → MoreRules → PathIndependence → WheelInformation → ClauseComplete → Check; `lean --run AllocationRecord.lean < sample.allocation`.

## Main results

| Result | Lean | File |
|---|---|---|
| Wheel is an exact round-robin; cap and conservation | `wheelRound_full`, `wheel_cap`, `wheel_sum` | Rule737 |
| Large-lot endpoint: one wheel pass equals price-time | `wheelRound_eq_priceTime_of_large_lot` | Rule737 |
| Fuel `R.sum + 1` always suffices | `wheel_exhausts`, `wheelS_exhausts` | MoreRules |
| **Balance with explicit level:** `wheelLevel` computes the run-dependent witness placing the wheel within one lot of water-filling | `wheelS_band_explicit`, `wheelS_within_L_explicit` | Balance |
| Stateful wheel ≡ fill-vector wheel; **balance stated on `wheel` itself** | `wheelS_eq_wheel`, `wheelS_state_eq`, `wheel_within_L` | Closure |
| **Same-operator result:** persistent `runWFull` is one-lot balanced and composes under canonical fuel; on reachable states allowance positivity is derived | `runW_band`, `runW_balanced`, `runWFull_comp`, `runWFull_comp_reachable` | PathIndependence |
| **Uniqueness:** price–time is the unique feasible serial allocation | `serial_unique`, `ladder_unique` | Rulebook, Algebra |
| Price-time conformance is complete and composes across consecutive executions | `conformsPT_iff`, `conformsPT_comp` | Rulebook, PathIndependence |
| **Parity observability limit:** queue and aligned fills cannot determine pointer conformance or the next allocation | `parity_pointer_not_identified_from_prints`, `no_parity_conformance_from_queue_and_prints` (legacy identifiers) | PathIndependence |
| **Necessary pointer information:** every universally future-sufficient four-party summary distinguishes the two future-inequivalent pointer witnesses | `future_sufficient_summary_requires_pointer_information` | PathIndependence |
| **General phase separation:** one-lot probes force equal pointer and allowance on arbitrary nondegenerate phase states | `validWheelPhase_probe_equiv_implies` | WheelInformation |
| **Exact fiberwise pointer state:** on any nondegenerate common-observation family, every future-sufficient summary is pointer-injective and the pointer is sufficient | `wheelFiberSufficient_pointer_injective`, `wheelPointerCode_fiber_sufficient` | WheelInformation |
| **Finite executable information bound:** reachable mL phase states, probes of at most L shares, and exact sufficient code | `phaseState_reachable`, `phaseState_probe_equiv_iff`, `wheelPhaseSufficient_injective`, `wheelPhaseCode_sufficient` | WheelInformation |
| **Reachable pointer-only bound:** the full-allowance family has one common aligned-allocation observation and exactly m pointer states | `phaseState_full_observation`, `phaseState_full_summary_injective`, `phaseState_full_pointer_sufficient` | WheelInformation |
| **Reachable allowance identity:** the invariant derives allowance from the live head's cumulative fill | `runW_allowance_phase`, `allowance_from_cumulative` | WheelInformation |
| Relabeling transports the pointer and leaves quantities unchanged | `runWFull_relabel` | WheelInformation |
| **Impossibility:** serial and band jointly unsatisfiable | `serial_band_incompatible` | Algebra |
| **Composition:** operator monoid and conservation closure | `seq_conserves`, `seq_assoc`, `ladderOp_conserves`, `rule737Op_eq` | Algebra |
| **Discrete benchmark boundary:** natural water levels do not encode a one-share estate for two equal claims | `waterFill_level_comp`, `waterFill_two_equal_no_single_share` | PathIndependence |
| **Estate completion and obstruction:** the unit rule is feasible for every estate, but reset rotation does not compose | `discreteCEA_feasible`, `discreteCEA_reset_not_composable` | MoreRules |
| Cross maximizes volume; ties → imbalance → reference distance | `crossPrice_maximizes`, `crossPrice2_lex`, `crossPrice3_lex` | Markets, Balance, Orders |
| **Candidate sufficiency:** cross over ask prices is a global maximum | `matched_dominated_by_ask_price`, `crossPrice_global` | Markets |
| Rule 611 ISO exception; lock/cross sliding; MPL/peg no-lock | `iso_compliance`, `slide_no_lock`, `mpl_no_trade_through`, `marketPeg_no_lock` | Rulebook, Orders |
| Legacy Rule 610/612 kernels agree with clause functions on dated dollar-price branches | `feeCap_eq_accessFeeCap610_legacy_dollar`, `rule612_iff_minimumTick612_legacy` | ClauseComplete |
| NYSE ladder with parity per level: conservation, price priority | `matchNYSE_conserve`, `nyse_price_priority` | MoreRules |
| Observability: hidden depth, parity fingerprint, allocation-vector invisibility | `hidden_depth_lower_bound`, `parity_count_fingerprint`, `priceTime_tail_invisible`, `priceTime_boundary_invisible` | Markets, Collisions |
| Tullock best response in exact integers | `tullock_best_response` | Strategic |
| Setter race: no pure NE for S ≥ 3 | `setter_race_no_pure_NE` | SetterRace |
| Uniform mix is an ε-equilibrium, ε = ½ cost unit, ε/S → 0 | `uniform_payoff`, `uniform_selfpayoff_zero`, `uniform_eps_relative` | Closure |

`uniform_payoff` proves the doubled payoff of bid b against the uniform opponent is N − 2b (a strict preference for low bids, not indifference); `uniform_selfpayoff_zero` proves the uniform profile's own value is 0; hence the best deviation gains N/(N+1) < 1 doubled unit = ½ cost unit, and < 1/N of the prize.

## Supporting arithmetic and evaluated examples

One-line arithmetic that pins down definitions: `dmm_advantage`, `dissipation_increasing`, `dmm_share_antitone`, `dmm_option_dilution`, `dmm_option_spread`, `relative_tick_antitone`, `race_spend`, `lower_le_ref`, `ref_le_upper`, `ref_in_bands`, `eff_at_nbo`, `pi_le_spread`, `midpoint_zero_eff`, `dmm_conserve`, `dmm_clears`, `wheelS_zero`, `dist_comm`, `dist_self`, `sq_nonneg_int`, `sip_ge_venue`, and the `ex_*` worked examples (kernel-evaluated worked instances in the paper).

## Modelling abstractions

- `Ev.sip = venue + lat`: the two-clock results are about additive latency, not a tape semantics.
- `midpoint` floors to the $0.0001 grid and is guaranteed only in `[NBB,NBO)`;
  `midpoint2_strict_inside` gives the exact strict result in doubled units.
- `effSpread2` performs signed subtraction in `Int`, preserving below-midpoint
  magnitude; it remains a buy-side kernel, not a full Rule 605 report statistic.
- `tradeThroughBuy px nbo := nbo < px`: Rule 611 without the one-second window or flickering-quote exception; the protected-quote structure lives in `protected_`, `nbo`, `iso_compliance`.
- `luldBands` uses `⌊ref·pct/100⌋`: no five-minute reference recomputation, no band doubling in the last 25 minutes, no rounding convention. `limitState_boundary` is the only limit-state theorem.
- `shortSaleOK` takes the Reg SHO circuit breaker as a Boolean input; the
  analytic kernel does not derive the 10 % trigger (the clause layer does).
- `hidden_depth_lower_bound` uses truncated subtraction; informative only when `Qs + ΣR < x`.
- The book-share inequality concerns water-filling only. `wheel_book_share_counterexample` proves failure of the uncorrected inequality for both integer wheels.
- `wheel L fuel` with fuel 0 returns no fills; `wheelOpFull` (fuel `R.sum + 1`) is the canonical operator.

## Executables

- `Conformance.lean`: `runTrials 200 → (200, 200)` (honest allocation records accepted) and the mutation harness `runMutation 200 → (200, 800, 800)`: 200 honest records with varying incoming size accepted, 800/800 mutants (lot moved forward, moved backward, over-fill, under-fill) rejected.
- `AllocationRecord.lean`: reads `<queue sizes>;<incoming x>;<aligned fills>` per line; prints `OK` or the violated property (`LENGTH` / `CAP` / `CONSERVATION` / `SERIAL`) with index. It checks price–time against a supplied order-level queue and privileged order-to-fill alignment; consolidated trade data alone supplies neither. A parity record also requires authenticated pointer-and-lot state. The legacy declaration `no_parity_conformance_from_queue_and_prints` proves that queue sizes and aligned fills alone cannot decide parity conformance or determine the next allocation.

## Not formalized

Real-valued limits (continuous water-filling, Tullock with real efforts, the seven venue games' mixed equilibria), a global minimal quotient of raw `WState` across claim-boundary and one-live-participant degeneracies, and axiomatic characterizations of all parity/hybrid families are not formalized. Exact fiberwise pointer minimality, exact predictive-summary minimality on the reachable finite phase families, general nondegenerate phase separation, reachable allowance recovery, the estate-indexed unit completion and its reset obstruction, the integer Tullock contest, and the setter race *are* formalized.

## File map

Rule737 (wheel, setter, price–time, water-level benchmark, worked example) · Markets (T3 tier, observability, cross, Reg NMS 610/611/612, two clocks, venue routing, candidate sufficiency) · Balance (stateful wheel, balance theorem, three-key cross, fee cap) · Rulebook (uniqueness, conformance, ladder, NBBO, ISO, sliding) · Orders (MPL, exact doubled midpoint, reserve, D-orders, pegs, self-help, auction, DMM facilitation) · Strategic (Tullock, DMM option, Bertrand routing) · SetterRace · Closure (wheelS ≡ wheel, balance on `wheel`, ε-equilibrium) · Conformance (harness) · Collisions (allocation/pointer collisions, invisibility) · Algebra (operator monoid, conservation closure, ladder uniqueness, impossibility) · MoreRules (fuel bounds, estate completion/reset obstruction, NYSE ladder, LULD, Reg SHO 201, execution-quality proxy, LOC/MOC, post-only) · PathIndependence (composition boundaries, future-summary lower bound, pointer wheel) · WheelInformation (general fiberwise pointer minimality, finite information bounds, reachability, label uniqueness, allowance recovery, equivariance) · ClauseComplete (dated specifications and ledger) · AllocationRecord (checker) · Check (axiom audit) · audit.py (static release guard).

## ClauseComplete.lean (current fixed-corpus layer)

- Dated corpus: necessary Rule 600 definitions; Rules 605, 610, 611, 612;
  Regulation SHO Rule 201; LULD; NYSE 7.31/7.35/7.37; and Nasdaq
  4702/4703/4752/4753/4754/4757.
- Typed checklist records for numerical rules, exceptions, procedures,
  disclosures, order types, attributes, auctions, priority, routing, and LULD.
- Dated Rule 610/612 profiles distinguish the September 2026 relief regime from
  delayed amended parameters; explicit theorems reject the amended profile for
  the dated decision.
- Whole-record relief requires attestations of grant, full scope, and satisfied
  conditions. Rule 605 selects the joint-plan publication route or the no-plan
  fallback, distinguishes the September 14-field and November 19-field
  immediate-report profiles, and records application of Release 34-105136.
- Exhaustive finite schemas: 10 Rule 605 order classes and 60 reporting fields;
  all nine Rule 611 exceptions; all Rule 201 short-exempt bases; 17 Nasdaq
  order types; and 13 attribute families.
- `clause_corpus_has_58_entries` verifies the range-ledger count;
  `clause_corpus_family_counts` proves the advertised breakdown;
  `clause_corpus_citations_unique` rejects duplicates; and
  `clause_corpus_traceability_complete` checks readable labels. Construction of
  each row also compiler-checks its actual destination object. These are
  traceability results, not proof that the mapping is faithful or sufficient, a
  legal conclusion, or production certification.

## PathIndependence.lean

- `priceTime_comp` proves estate-indexed composition. `waterFill_level_comp`
  proves only a water-level identity, while
  `waterFill_two_equal_no_single_share` proves that natural levels do not encode
  every estate. `wheel_not_path_independent` is the decided pass-reset
  counterexample. The pointer-and-lot transition system `stepW`/`runW` has
  technical state composition in `runW_comp`; descent and conservation lemmas
  discharge those premises in the canonical `runWFull_comp` theorem. The
  phase-level `AtWheelPhase` invariant yields `runWFull_comp_reachable`, which
  derives allowance positivity on every state reached from `initW`. The
  pointer-relative `AllAtP` invariant yields `runW_band` and `runW_balanced`, so
  the same persistent operator has both the one-lot band and canonical composition.
  `conformsPT_comp` carries price-time
  conformance across consecutive executions. The legacy pointer-observability
  theorem names retain “prints,” but their data are participant-aligned fills,
  not a public tape. `FutureSufficient4` quantifies over arbitrary summary
  codomains and predictors, and
  `future_sufficient_summary_requires_pointer_information` proves that every
  such correct summary distinguishes the two witness pointer states.
  The idealized saturatedOwner trace and its injectivity lemmas remain here.
  The main information theorem uses actual finite executions in
  WheelInformation.lean, independently of that trace. Its complete-summary
  decoder receives no separate queue or cumulative-fill input.

## Interfaces and audit

Rule 600(b)(89)(i)(F) is the minimum-pricing-increment indicator, represented
by `MinimumIncrementIndicatorProfile600`; odd-lot information is (69).
`checkedRoundLotSize600` rejects existing-stock averages off the cent grid.
Normalization and period assignment require external evidence.

The CLI rejects malformed numeric tokens. Run `python3 verify_checker.py`
after building `allocation_record` for 12 executable interface checks.
The axiom audit covers 362 declarations, including 48 with classical-choice proof
dependencies. `runW_allowance_phase` derives allowance from cumulative
allocation on every reachable live-head state, and
`validWheelPhase_probe_equiv_implies` separates pointer and allowance on the
general nondegenerate domain. `wheelFiberSufficient_pointer_injective` and
`wheelPointerCode_fiber_sufficient` give exact pointer minimality on every
one-state-per-pointer nondegenerate common-observation family; the reachable
full-allowance instantiation is checked separately. Binary-encoding
consequences are explicitly identified as mathematical corollaries.

The Nasdaq catalogues follow Rule 4702(b)(1)-(17) and Rule 4703(a)-(m).
They identify Market On Open explicitly and include Extended Trading Close,
Reserve Size, Attribution, and Trade Now. The three auction ranges are
4752(a)-(d), 4753(a)-(e), and 4754(a)-(b). Rule 4755 procedures are outside
the fixed ledger; an order-type constructor does not implement its lifecycle.
