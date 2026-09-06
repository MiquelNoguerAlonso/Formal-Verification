/- AllocationRecord.lean — order-book-state conformance checker. Input lines:
     <queue sizes space-separated>;<incoming x>;<queue-aligned fills space-separated>
   Output per line: OK, or the violated property and first offending index.

   The third field is a privileged engine-audit allocation record aligned to
   the supplied queue. It is not a public consolidated trade tape. -/
import Rule737
import Rulebook
open Rule737

/-- Reject a malformed token instead of silently deleting it from the queue
    or allocation record.  Repeated spaces and an empty vector are allowed. -/
def parseNats (s : String) : Option (List Nat) :=
  ((s.splitOn " ").filter (fun t => !t.trim.isEmpty)).mapM (fun t => t.trim.toNat?)

def firstDiff (a b : List Nat) : Option Nat :=
  (List.range (min a.length b.length)).find? (fun i => a[i]! ≠ b[i]!)

def diagnose (Q A : List Nat) (x : Nat) : String :=
  if A.length ≠ Q.length then s!"LENGTH allocation={A.length} book={Q.length}"
  else match (List.range Q.length).find? (fun i => Q[i]! < A[i]!) with
  | some i => s!"CAP at {i}: fill {A[i]!} > size {Q[i]!}"
  | none =>
    if A.sum ≠ min x Q.sum then s!"CONSERVATION sum={A.sum} expected={min x Q.sum}"
    else match (List.range Q.length).find? (fun i =>
        A[i]! < Q[i]! ∧ 0 < (A.drop (i+1)).sum) with
    | some i => s!"SERIAL at {i}: partial fill {A[i]!}/{Q[i]!} with {(A.drop (i+1)).sum} behind"
    | none => "OK"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut n := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    n := n + 1
    match line.trim.splitOn ";" with
    | [q, x, a] =>
      match parseNats q, x.trim.toNat?, parseNats a with
      | some Q, some xv, some A =>
        let verdict := if conformsPT Q A xv then "OK" else diagnose Q A xv
        IO.println s!"{n}: {verdict}"
      | _, _, _ => IO.println s!"{n}: PARSE"
    | _ => IO.println s!"{n}: PARSE"
