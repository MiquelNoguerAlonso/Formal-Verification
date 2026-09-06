import Lean
import Rule737
import Balance
import Markets
import PathIndependence
import WheelInformation

open Lean Rule737

def fillsFor (m L : Nat) (st : WState) (x : Nat) : List Nat :=
  (List.range m).map (fun i => nextWFill L st x i)

def main : IO Unit := do
  let q := [200, 300, 500]
  let st := initW 100 [(0, 300), (1, 300)]
  let first := (runWFull 100 st 100).1
  let state150 := (runWFull 100 st 150).1
  let final := (runWFull 100 state150 150).1
  let pool := [300, 500, 0, 1000]
  let w := wheelLevel 100 20 (initS pool) 1100 0
  let prices := [99800, 99900, 100000, 100100, 100200, 100300]
  let bids := [(100200, 500), (100100, 300), (100000, 400), (99900, 200)]
  let asks := [(99800, 300), (100000, 300), (100100, 400), (100300, 500)]
  let demand := prices.map (demandAt bids)
  let supply := prices.map (supplyAt asks)
  let json := Json.mkObj [
    ("comparison_claims", toJson q),
    ("comparison_serial", toJson (priceTime q 600)),
    ("comparison_parity", toJson (wheel 100 20 q 600).1),
    ("reset_combined", toJson (wheel 100 20 [300, 300] 200).1),
    ("reset_split", toJson (List.zipWith (· + ·)
      (wheel 100 20 [300, 300] 100).1 (wheel 100 20 [200, 300] 100).1)),
    ("persistent_combined", toJson (fillsFor 2 100 st 200)),
    ("persistent_split", toJson (List.zipWith (· + ·)
      (fillsFor 2 100 st 100) (fillsFor 2 100 first 100))),
    ("partial_fills", toJson ((List.range 2).map (fun i => allocatedW i state150))),
    ("partial_pointer", toJson state150.S.head!.1),
    ("partial_allowance", toJson state150.lot),
    ("partial_final_fills", toJson ((List.range 2).map (fun i => allocatedW i final))),
    ("partial_final_pointer", toJson final.S.head!.1),
    ("partial_final_allowance", toJson final.lot),
    ("partial_composition", toJson (decide (runWFull 100 st 300 = runWFull 100 state150 150))),
    ("band_claims", toJson pool),
    ("band_fills", toJson (wheel 100 20 pool 1100).1),
    ("band_level", toJson w),
    ("band_benchmark", toJson (waterFill w pool)),
    ("pointer_probe_1", toJson (fillsFor 3 100 (phaseState 3 100 1 100) 1)),
    ("pointer_probe_2", toJson (fillsFor 3 100 (phaseState 3 100 2 100) 1)),
    ("allowance_probe_40", toJson (fillsFor 3 100 (phaseState 3 100 1 40) 41)),
    ("allowance_probe_80", toJson (fillsFor 3 100 (phaseState 3 100 1 80) 41)),
    ("allowance_curve_40", toJson ((List.range 101).map
      (fun x => nextWFill 100 (phaseState 3 100 1 40) x 1))),
    ("allowance_curve_80", toJson ((List.range 101).map
      (fun x => nextWFill 100 (phaseState 3 100 1 80) x 1))),
    ("auction_prices", toJson prices),
    ("auction_demand", toJson demand),
    ("auction_supply", toJson supply),
    ("auction_matched", toJson (prices.map (matchedAt bids asks)))]
  IO.println json.compress
