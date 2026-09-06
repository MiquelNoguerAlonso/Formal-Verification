/- TapeConformance.lean — what each observation channel can certify.
   Lean 4.22.0, core only.  No `sorry`.

   Three observation channels of the same execution:
     tapeView   — consolidated tape: total printed quantity only;
     depthView  — order-level feed: the queue-aligned fill vector;
     δ-clock    — order-level feed whose priority order is known only up to a
                  clock resolution δ.
   The results: queue jumps are invisible on the tape and always detected on
   the depth feed; wheel conformance with a latent pointer is decidable by a
   finite search of exactly m·L candidates, sound, complete, prefix-monotone,
   and accepts every honest run; clock coarsening enlarges the accepted set
   monotonically; a two-order separation hypothesis gives exact masking. -/
import Rule737
import Rulebook
import PathIndependence
namespace Rule737

/-! ## Observation channels -/

/-- Consolidated-tape view of one execution: the printed total. -/
def tapeView (prints : List Nat) : Nat := prints.sum

/-- Order-level (depth) view of one execution: the fill vector itself. -/
def depthView (prints : List Nat) : List Nat := prints

theorem sum_app (A B : List Nat) : (A ++ B).sum = A.sum + B.sum := by
  induction A with
  | nil => simp
  | cons a T ih => simp [List.sum_cons, ih, Nat.add_assoc]

/-! ## Queue jumps: a lot moved from one resting order to another -/

/-- Honest record and a jumped record: `t` shares move from position of `a`
    to position of `b`. -/
def jumped (A B C : List Nat) (a b t : Nat) : List Nat := A ++ (a - t) :: B ++ (b + t) :: C
def honest (A B C : List Nat) (a b : Nat) : List Nat := A ++ a :: B ++ b :: C

/-- **Tape invisibility of a queue jump.**  The consolidated tape prints the
    same total for the honest and the jumped record. -/
theorem jump_tape_invisible (A B C : List Nat) (a b t : Nat) (ht : t ≤ a) :
    tapeView (jumped A B C a b t) = tapeView (honest A B C a b) := by
  simp only [tapeView, jumped, honest, sum_app, List.sum_cons]
  omega

/-- **Depth detection of a queue jump.**  A positive jump never conforms to
    price–time when the honest record does. -/
theorem jump_depth_detected (Q A B C : List Nat) (a b t x : Nat)
    (ht : 0 < t) (_hta : t ≤ a) (hpt : priceTime Q x = honest A B C a b) :
    conformsPT Q (jumped A B C a b t) x = false := by
  simp only [conformsPT, hpt]
  apply beq_eq_false_iff_ne.2
  intro h
  simp only [jumped, honest] at h
  have h1 := List.append_inj_right h (by simp)
  have h2 := List.cons_eq_cons.1 h1
  omega

/-- The honest record itself conforms (soundness of the channel). -/
theorem honest_conforms (Q : List Nat) (x : Nat) : conformsPT Q (priceTime Q x) x = true := by
  simp [conformsPT]

/-! ## Wheel conformance with a latent pointer

The depth feed shows, per execution, how much each participant received.  It
does not show the wheel pointer or the unfinished lot.  Conformance to the
pointer-and-lot wheel is therefore an existential statement over the latent
initial state, decided by exhaustive search over the finite candidate set. -/

/-- All rotations of a list (length-many). -/
def rotate1 {α} : List α → List α
  | [] => []
  | a :: T => T ++ [a]

def rotations {α} (S : List α) : List (List α) :=
  (List.range S.length).map (fun k => (fun s => Nat.repeat rotate1 k s) S)

theorem rotations_length {α} (S : List α) : (rotations S).length = S.length := by
  simp [rotations]

theorem rotations_self {α} (S : List α) (h : 0 < S.length) : S ∈ rotations S := by
  simp only [rotations, List.mem_map]
  exact ⟨0, List.mem_range.2 h, rfl⟩

/-- Candidate initial states: every rotation of the initialized book, every
    lot allowance in `1..L`. -/
def candidates (L : Nat) (R : List (Nat × Nat)) : List WState :=
  (rotations (initW L R).S).flatMap (fun S =>
    (List.range L).map (fun k => (⟨S, k + 1⟩ : WState)))

theorem length_flatMap_const {α β} (l : List α) (f : α → List β) (c : Nat)
    (h : ∀ a, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a T ih => simp [List.flatMap_cons, h, ih, Nat.succ_mul, Nat.add_comm]

/-- **Exactly m·L candidates.**  The search space has the size of the
    pointer–allowance family of the information theorems. -/
theorem candidates_length (L : Nat) (R : List (Nat × Nat)) :
    (candidates L R).length = R.length * L := by
  unfold candidates
  rw [length_flatMap_const _ _ L (by intro a; simp), rotations_length]
  simp [initW]

theorem initW_mem_candidates (L : Nat) (R : List (Nat × Nat)) (hL : 0 < L) (hR : 0 < R.length) :
    initW L R ∈ candidates L R := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  refine ⟨(initW L R).S, rotations_self _ (by simp [initW]; exact hR), L - 1, List.mem_range.2 (by omega), ?_⟩
  show (⟨(initW L R).S, L - 1 + 1⟩ : WState) = initW L R
  have : L - 1 + 1 = L := by omega
  rw [this]
  rfl

/-- Allocation of participant `id` in a state (0 if absent). -/
def allocOf (S : List (Nat × Nat × Nat)) (id : Nat) : Nat :=
  match S.find? (fun p => p.1 == id) with
  | some p => p.2.1
  | none => 0

/-- Participant-aligned fill vector of one execution of size `x`. -/
def execFills (L n : Nat) (ids : List Nat) (st : WState) (x : Nat) : List Nat × WState :=
  let st' := (runW L n st x).1
  (ids.map (fun id => allocOf st'.S id - allocOf st.S id), st')

/-- Replay a sequence of executions, emitting one aligned fill vector each. -/
def replay (L n : Nat) (ids : List Nat) : WState → List Nat → List (List Nat)
  | _, [] => []
  | st, x :: xs =>
      let r := execFills L n ids st x
      r.1 :: replay L n ids r.2 xs

theorem replay_length (L n : Nat) (ids : List Nat) (st : WState) (xs : List Nat) :
    (replay L n ids st xs).length = xs.length := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp [replay, ih]

def replayState (L n : Nat) (ids : List Nat) : WState → List Nat → WState
  | st, [] => st
  | st, x :: xs => replayState L n ids (execFills L n ids st x).2 xs

theorem replay_append (L n : Nat) (ids : List Nat) (st : WState) (xs ys : List Nat) :
    replay L n ids st (xs ++ ys) =
      replay L n ids st xs ++ replay L n ids (replayState L n ids st xs) ys := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp [replay, replayState, ih]

/-- **Decidable wheel conformance with latent pointer and lot.** -/
def wheelConsistent (L n : Nat) (R : List (Nat × Nat)) (xs : List Nat)
    (obs : List (List Nat)) : Bool :=
  (candidates L R).any (fun st => replay L n (R.map (·.1)) st xs == obs)

/-- Soundness: acceptance exhibits a candidate initial state. -/
theorem wheelConsistent_sound (L n : Nat) (R : List (Nat × Nat)) (xs : List Nat)
    (obs : List (List Nat)) (h : wheelConsistent L n R xs obs = true) :
    ∃ st, st ∈ candidates L R ∧ replay L n (R.map (·.1)) st xs = obs := by
  simp only [wheelConsistent, List.any_eq_true, beq_iff_eq] at h
  exact h

/-- Completeness relative to the candidate family. -/
theorem wheelConsistent_complete (L n : Nat) (R : List (Nat × Nat)) (xs : List Nat)
    (obs : List (List Nat)) (st : WState) (hst : st ∈ candidates L R)
    (h : replay L n (R.map (·.1)) st xs = obs) :
    wheelConsistent L n R xs obs = true := by
  simp only [wheelConsistent, List.any_eq_true, beq_iff_eq]
  exact ⟨st, hst, h⟩

/-- **Every honest run is accepted.** -/
theorem wheelConsistent_honest (L n : Nat) (R : List (Nat × Nat)) (xs : List Nat)
    (hL : 0 < L) (hR : 0 < R.length) :
    wheelConsistent L n R xs (replay L n (R.map (·.1)) (initW L R) xs) = true :=
  wheelConsistent_complete L n R xs _ _ (initW_mem_candidates L R hL hR) rfl

/-- **Prefix monotonicity (filtering).**  Consistency of a longer record
    implies consistency of every prefix. -/
theorem wheelConsistent_prefix (L n : Nat) (R : List (Nat × Nat)) (xs ys : List Nat)
    (o₁ o₂ : List (List Nat)) (hlen : o₁.length = xs.length)
    (h : wheelConsistent L n R (xs ++ ys) (o₁ ++ o₂) = true) :
    wheelConsistent L n R xs o₁ = true := by
  obtain ⟨st, hst, hr⟩ := wheelConsistent_sound _ _ _ _ _ h
  rw [replay_append] at hr
  have hl : (replay L n (R.map (·.1)) st xs).length = o₁.length := by
    rw [replay_length, hlen]
  have hp := (List.append_inj hr hl).1
  exact wheelConsistent_complete L n R xs o₁ st hst hp

/-! ## Clock coarsening

Queue entries carry a timestamp, an order identifier, and a size. The declared
uncertainty model permits swaps of neighbours whose timestamps differ by at
most `δ`. Fills are restored to a fixed external identifier order before
comparison. Protocol sequence information may rule out these swaps in a real
feed; this is an explicit uncertainty model, not a claim about every feed. -/

/-- Timestamp, order identifier, and remaining quantity. -/
abbrev TimedOrder := Nat × Nat × Nat

/-- Price-time fills restored to the supplied external order-label list. -/
def labelledPriceTime (ids : List Nat) (Q : List TimedOrder) (x : Nat) : List Nat :=
  let pairs := Q.zip (priceTime (Q.map (fun p => p.2.2)) x)
  ids.map (fun id => ((pairs.find? (fun p => p.1.2.1 == id)).map (fun p => p.2)).getD 0)

def labelledConformsPT (ids : List Nat) (Q : List TimedOrder) (prints : List Nat)
    (x : Nat) : Bool := prints == labelledPriceTime ids Q x

/-- One-step δ-swaps: every list obtained by swapping one adjacent pair whose
    timestamps are within δ. -/
def swaps1 (δ : Nat) : List TimedOrder → List (List TimedOrder)
  | a :: b :: T =>
      (if b.1 - a.1 ≤ δ ∧ a.1 - b.1 ≤ δ then [b :: a :: T] else []) ++
        (swaps1 δ (b :: T)).map (a :: ·)
  | _ => []

def nbhd (δ : Nat) : Nat → List TimedOrder → List (List TimedOrder)
  | 0, Q => [Q]
  | k + 1, Q => Q :: (swaps1 δ Q).flatMap (nbhd δ k)

/-- Conformance modulo clock resolution: some δ-neighbour of the observed
    queue explains the fills under price–time. -/
def conformsPTδ (δ k : Nat) (ids : List Nat) (Q : List TimedOrder) (prints : List Nat) (x : Nat) : Bool :=
  (nbhd δ k Q).any (fun Q' => labelledConformsPT ids Q' prints x)

theorem swaps1_mono (δ δ' : Nat) (h : δ ≤ δ') (Q : List TimedOrder) :
    ∀ Q', Q' ∈ swaps1 δ Q → Q' ∈ swaps1 δ' Q := by
  induction Q with
  | nil => intro Q' hQ; simp [swaps1] at hQ
  | cons a T ih =>
      cases T with
      | nil => intro Q' hQ; simp [swaps1] at hQ
      | cons b T =>
          intro Q' hQ
          simp only [swaps1, List.mem_append, List.mem_map] at hQ ⊢
          rcases hQ with hQ | ⟨y, hy, rfl⟩
          · left
            split at hQ
            · rename_i hc; rw [if_pos ⟨Nat.le_trans hc.1 h, Nat.le_trans hc.2 h⟩]; exact hQ
            · simp at hQ
          · right; exact ⟨y, ih y hy, rfl⟩

theorem nbhd_mono (δ δ' : Nat) (h : δ ≤ δ') (k : Nat) (Q : List TimedOrder) :
    ∀ Q', Q' ∈ nbhd δ k Q → Q' ∈ nbhd δ' k Q := by
  induction k generalizing Q with
  | zero => intro Q' hQ; simpa [nbhd] using hQ
  | succ k ih =>
      intro Q' hQ
      simp only [nbhd, List.mem_cons, List.mem_flatMap] at hQ ⊢
      rcases hQ with rfl | ⟨y, hy, hQ'⟩
      · left; rfl
      · right; exact ⟨y, swaps1_mono δ δ' h Q y hy, ih y Q' hQ'⟩

/-- **Coarser clocks accept more.**  Acceptance under resolution δ implies
    acceptance under any δ' ≥ δ. -/
theorem conformsPTδ_mono (δ δ' k : Nat) (h : δ ≤ δ') (ids : List Nat) (Q : List TimedOrder)
    (prints : List Nat) (x : Nat) (hc : conformsPTδ δ k ids Q prints x = true) :
    conformsPTδ δ' k ids Q prints x = true := by
  simp only [conformsPTδ, List.any_eq_true] at hc ⊢
  obtain ⟨Q', hQ', hp⟩ := hc
  exact ⟨Q', nbhd_mono δ δ' h k Q Q' hQ', hp⟩

/-- Exact labelled conformance is accepted under every declared uncertainty budget. -/
theorem conformsPTδ_of_conformsPT (δ k : Nat) (ids : List Nat) (Q : List TimedOrder) (prints : List Nat) (x : Nat)
    (h : labelledConformsPT ids Q prints x = true) : conformsPTδ δ k ids Q prints x = true := by
  simp only [conformsPTδ, List.any_eq_true]
  refine ⟨Q, ?_, h⟩
  cases k <;> simp [nbhd]

/-- A swap of δ-close adjacent neighbours is a one-step δ-swap. -/
theorem swap_mem_swaps1 (δ : Nat) (A C : List TimedOrder) (a b : TimedOrder)
    (hab : b.1 - a.1 ≤ δ ∧ a.1 - b.1 ≤ δ) :
    A ++ b :: a :: C ∈ swaps1 δ (A ++ a :: b :: C) := by
  induction A with
  | nil => simp [swaps1, hab]
  | cons p A ih =>
      cases A with
      | nil =>
          simp only [List.nil_append, List.cons_append, swaps1, List.mem_append, List.mem_map]
          right; exact ⟨b :: a :: C, by simp [hab], rfl⟩
      | cons q A =>
          simp only [List.cons_append, swaps1, List.mem_append, List.mem_map]
          right
          refine ⟨(q :: A) ++ b :: a :: C, ?_, rfl⟩
          simpa using ih

/-- **δ-masking of a queue jump.**  If the honest fills are those of the
    swapped queue and the two swapped neighbours are within δ, the record is
    accepted at resolution δ with a single swap: the jump is not detectable. -/
theorem jump_masked (δ : Nat) (ids : List Nat) (A C : List TimedOrder) (a b : TimedOrder) (x : Nat)
    (hab : b.1 - a.1 ≤ δ ∧ a.1 - b.1 ≤ δ) :
    conformsPTδ δ 1 ids (A ++ a :: b :: C)
      (labelledPriceTime ids (A ++ b :: a :: C) x) x = true := by
  simp only [conformsPTδ, List.any_eq_true]
  refine ⟨A ++ b :: a :: C, ?_, by simp [labelledConformsPT]⟩
  simp only [nbhd, List.mem_cons, List.mem_flatMap]
  right
  exact ⟨A ++ b :: a :: C, swap_mem_swaps1 δ A C a b hab, by simp⟩

/-- For two orders whose labelled fills differ when swapped, the clock
    checker masks the swapped record exactly at the declared gap threshold. -/
theorem twoOrder_masking_iff (δ : Nat) (ids : List Nat) (a b : TimedOrder) (x : Nat)
    (hd : labelledPriceTime ids [b, a] x ≠ labelledPriceTime ids [a, b] x) :
    conformsPTδ δ 1 ids [a, b] (labelledPriceTime ids [b, a] x) x = true ↔
      b.1 - a.1 ≤ δ ∧ a.1 - b.1 ≤ δ := by
  by_cases h : b.1 - a.1 ≤ δ ∧ a.1 - b.1 ≤ δ
  · simp only [conformsPTδ, nbhd, swaps1, h]
    simp [labelledConformsPT]
  · simp only [conformsPTδ, nbhd, swaps1, h, if_false]
    simp [labelledConformsPT, beq_iff_eq, hd]

/-! ## Worked instances -/

def exR : List (Nat × Nat) := [(1, 300), (2, 300), (3, 200)]
def exObs := replay 100 20 [1, 2, 3] (initW 100 exR) [250, 150]

theorem ex_candidates : (candidates 100 exR).length = 300 := by
  rw [candidates_length]; rfl
set_option maxRecDepth 100000 in
theorem ex_honest : wheelConsistent 100 20 exR [250, 150] exObs = true := by rfl
set_option maxRecDepth 100000 in
theorem ex_reset_rejected :
    wheelConsistent 100 20 exR [250, 150]
      [[100, 100, 50], [100, 50, 0]] = false := by rfl
theorem ex_tape_jump :
    tapeView (jumped [] [] [] 200 300 100) = tapeView (honest [] [] [] 200 300) := by decide
theorem ex_masked :
    conformsPTδ 5 1 [1, 2, 3] [(10, 1, 200), (12, 2, 300), (40, 3, 100)] [100, 300, 0] 400 = true := by decide
theorem ex_not_masked :
    conformsPTδ 1 1 [1, 2, 3] [(10, 1, 200), (12, 2, 300), (40, 3, 100)] [100, 300, 0] 400 = false := by decide

/-- Equal sizes must not erase different order identities. -/
theorem ex_equal_size_clock_jump :
    conformsPTδ 2 1 [1, 2] [(10, 1, 200), (12, 2, 200)] [0, 200] 200 = true ∧
    conformsPTδ 1 1 [1, 2] [(10, 1, 200), (12, 2, 200)] [0, 200] 200 = false := by decide

end Rule737
