import TapeConformance
import Lean
open Rule737 Lean

def claims5 : List (Nat × Nat) :=
  [(1, 700), (2, 500), (3, 900), (4, 600), (5, 800)]
def quantities5 : List Nat := [250, 130, 420, 90, 310, 260]
def ids5 : List Nat := claims5.map (·.1)
def fuel5 : Nat := (claims5.map (·.2)).sum + 1
def observations5 := replay 100 fuel5 ids5 (initW 100 claims5) quantities5

def surviving (xs : List Nat) : Nat :=
  let obs := replay 100 fuel5 ids5 (initW 100 claims5) xs
  ((candidates 100 claims5).filter (fun st => replay 100 fuel5 ids5 st xs == obs)).length

def main : IO Unit := do
  let data := Json.mkObj [
    ("lot", toJson (100 : Nat)),
    ("ids", toJson ids5),
    ("claims", toJson (claims5.map (·.2))),
    ("quantities", toJson quantities5),
    ("fuel", toJson fuel5),
    ("observations", toJson observations5),
    ("survivors", toJson ((List.range 7).map (fun k => surviving (quantities5.take k)))),
    ("full_cycle_quantity", toJson (500 : Nat)),
    ("full_cycle_survivors", toJson (surviving [500])),
    ("depth_honest", toJson (priceTime [200, 300] 400)),
    ("depth_jump", toJson (jumped [] [] [] 200 200 100)),
    ("clock_equal_size_accept", toJson
      (conformsPTδ 2 1 [1, 2] [(10, 1, 200), (12, 2, 200)] [0, 200] 200)),
    ("clock_equal_size_reject", toJson
      (conformsPTδ 1 1 [1, 2] [(10, 1, 200), (12, 2, 200)] [0, 200] 200))]
  IO.println data.compress
