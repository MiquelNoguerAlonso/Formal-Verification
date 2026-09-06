import Rule737
import Rulebook
import Conformance
namespace Rule737

def seeds : List Nat := List.range 200 |>.map (· + 1)
def queues : List (List Nat) := seeds.map (synthQueue 8)
def prints : List (List Nat) := queues.map (priceTime · 2500)

def countDup (l : List (List Nat)) : Nat :=
  l.length - (l.foldl (fun acc q => if acc.contains q then acc else q :: acc) []).length

-- 1. seed collisions: distinct seeds, identical queue
#eval countDup queues
-- 2. allocation-record collisions: distinct queues, identical fill vectors at x = 2500
#eval countDup prints
-- 3. the collided groups (first few): queues that print identically
def groups : List (List Nat × List (List Nat)) :=
  prints.foldl (fun acc p =>
    if acc.any (·.1 == p) then acc else
      (p, (queues.zip prints).filterMap (fun (q, p') => if p' == p then some q else none)) :: acc) []
#eval (groups.filter (·.2.length > 1)).take 3
-- 4. wheel pointer collisions: rotations of the same level giving identical multisets of fills
def rot (l : List Nat) (k : Nat) : List Nat := l.drop k ++ l.take k
def wheelFills (k : Nat) : List Nat :=
  let R := [300, 500, 200, 1000]
  let f := (wheel 100 20 (rot R k) 1100).1
  rot f (4 - k)   -- un-rotate to participant order
#eval (List.range 4).map wheelFills

end Rule737

namespace Rule737
theorem priceTime_zero (Q : List Nat) : priceTime Q 0 = Q.map (fun _ => 0) := by
  induction Q with
  | nil => rfl
  | cons q Q ih => simp [priceTime, ih]

/-- **Tail invisibility.**  Once the incoming quantity is absorbed by the head,
    the queue-aligned allocation record is identical for any queue tail of the same length. -/
theorem priceTime_tail_invisible (q x : Nat) (Q Q' : List Nat)
    (hx : x ≤ q) (hl : Q.length = Q'.length) :
    priceTime (q :: Q) x = priceTime (q :: Q') x := by
  simp only [priceTime, Nat.min_eq_right hx, Nat.sub_self, priceTime_zero]
  congr 1
  induction Q generalizing Q' with
  | nil => cases Q' with | nil => rfl | cons => simp at hl
  | cons a A ih => cases Q' with | nil => simp at hl | cons b B => simp [ih B (by simpa using hl)]

/-- **Boundary invisibility.**  If the incoming quantity is absorbed by the
    head, neither the head's capacity above that quantity nor an equally long
    tail is identified by the fill vector. -/
theorem priceTime_boundary_invisible (q q' x : Nat) (Q Q' : List Nat)
    (hq : x ≤ q) (hq' : x ≤ q') (hl : Q.length = Q'.length) :
    priceTime (q :: Q) x = priceTime (q' :: Q') x := by
  simp only [priceTime, Nat.min_eq_right hq, Nat.min_eq_right hq', Nat.sub_self,
    priceTime_zero]
  congr 1
  induction Q generalizing Q' with
  | nil => cases Q' with | nil => rfl | cons => simp at hl
  | cons a A ih => cases Q' with | nil => simp at hl | cons b B => simp [ih B (by simpa using hl)]
end Rule737
