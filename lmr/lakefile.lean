import Lake
open Lake DSL

package «lean-market-rules» where
  -- core Lean only: no dependencies, no Mathlib

/-- All certificate modules, in dependency order. -/
@[default_target]
lean_lib MarketRules where
  srcDir := "."
  roots := #[`Rule737, `Markets, `Balance, `Rulebook, `Orders, `Strategic,
             `SetterRace, `Closure, `Conformance, `Collisions, `Algebra, `MoreRules,
             `PathIndependence, `WheelInformation, `ClauseComplete, `Check]

/-- Queue-aligned allocation-record checker:
    `lake exe allocation_record < sample.allocation`. -/
lean_exe allocation_record where
  srcDir := "."
  root := `AllocationRecord
