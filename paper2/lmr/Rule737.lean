/-
  Rule737.lean — Lean 4 (core, no Mathlib) formalization of the
  allocation operators in "The Mathematics of NASDAQ and NYSE" (Sec. 2):
  NASDAQ price–time (Rule 4757), NYSE Rule 7.37 three-tier operator
  (setter → round-lot parity wheel → non-displayed), continuous parity
  (water-filling) and the book-participant fill-share proposition.
  Checked with Lean 4.22.0.  No `sorry`; only propext/Quot.sound/Classical.choice.
-/

namespace Rule737

/-! ## Primitives -/

/-- Pointwise relation between two lists of equal length. -/
inductive Pw (P : Nat → Nat → Prop) : List Nat → List Nat → Prop
  | nil : Pw P [] []
  | cons {a b : Nat} {A B : List Nat} : P a b → Pw P A B → Pw P (a :: A) (b :: B)

theorem map_zero_sum (R : List Nat) : (R.map (fun _ => (0:Nat))).sum = 0 := by
  induction R with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Pw_map_zero (R : List Nat) : Pw (fun a r => a ≤ r) (R.map (fun _ => 0)) R := by
  induction R with
  | nil => exact Pw.nil
  | cons r R ih => exact Pw.cons (Nat.zero_le _) ih

/-- Quantity one participant receives in one wheel visit:
    one round lot `L`, capped by its remaining size `r` and by the
    incoming quantity `x`. -/
def give (L r x : Nat) : Nat := min L (min r x)

theorem give_le_L (L r x : Nat) : give L r x ≤ L := Nat.min_le_left _ _
theorem give_le_r (L r x : Nat) : give L r x ≤ r :=
  Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
theorem give_le_x (L r x : Nat) : give L r x ≤ x :=
  Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

/-- If the incoming quantity is not exhausted by this visit, the visit
    gave the full `min L r` (the round lot or the participant's remainder). -/
theorem give_of_pos (L r x : Nat) (h : 0 < x - give L r x) :
    give L r x = min L r := by
  unfold give at *
  have hx : min L (min r x) ≤ x := Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
  by_cases hrx : r ≤ x
  · rw [Nat.min_eq_left hrx]
  · have : x < r := Nat.lt_of_not_le hrx
    rw [Nat.min_eq_right (Nat.le_of_lt this)] at *
    by_cases hLx : L ≤ x
    · rw [Nat.min_eq_left hLx]; rw [Nat.min_eq_left (Nat.le_trans hLx (Nat.le_of_lt this))]
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hLx))] at h; omega

/-! ## Tier 2: one pass of the round-lot parity wheel -/

/-- One pass of the wheel over remaining displayed sizes `R` (listed in
    wheel order starting at the pointer) with incoming `x`.
    Returns the fills of this pass and the quantity left. -/
def wheelRound (L : Nat) : List Nat → Nat → List Nat × Nat
  | [], x => ([], x)
  | r :: R, x =>
      let g := give L r x
      let p := wheelRound L R (x - g)
      (g :: p.1, p.2)

/-- Each fill in a pass is at most one round lot. -/
theorem wheelRound_le_L (L : Nat) (R : List Nat) (x : Nat) :
    ∀ g ∈ (wheelRound L R x).1, g ≤ L := by
  induction R generalizing x with
  | nil => intro g h; simp [wheelRound] at h
  | cons r R ih =>
      intro g h
      simp only [wheelRound, List.mem_cons] at h
      rcases h with h | h
      · rw [h]; exact give_le_L _ _ _
      · exact ih _ _ h

/-- Fills respect remaining sizes (pointwise cap). -/
theorem wheelRound_cap (L : Nat) (R : List Nat) (x : Nat) :
    Pw (fun g r => g ≤ r) (wheelRound L R x).1 R := by
  induction R generalizing x with
  | nil => exact Pw.nil
  | cons r R ih => exact Pw.cons (give_le_r _ _ _) (ih _)

/-- Conservation: a pass allocates exactly `x - x'` where `x'` is what is left. -/
theorem wheelRound_sum (L : Nat) (R : List Nat) (x : Nat) :
    (wheelRound L R x).1.sum + (wheelRound L R x).2 = x := by
  induction R generalizing x with
  | nil => simp [wheelRound]
  | cons r R ih =>
      simp only [wheelRound, List.sum_cons]
      have h1 := give_le_x L r x
      have h2 := ih (x - give L r x)
      omega

theorem wheelRound_sum_le (L : Nat) (R : List Nat) (x : Nat) :
    (wheelRound L R x).1.sum ≤ x := by
  have := wheelRound_sum L R x; omega

/-- Un-truncated pass: if quantity is left after the pass, every
    participant received `min L r` — the wheel is a fair round-robin. -/
theorem wheelRound_full (L : Nat) (R : List Nat) (x : Nat)
    (h : 0 < (wheelRound L R x).2) :
    (wheelRound L R x).1 = R.map (fun r => min L r) := by
  induction R generalizing x with
  | nil => rfl
  | cons r R ih =>
      simp only [wheelRound, List.map_cons] at *
      have hs := wheelRound_sum L R (x - give L r x)
      have hpos : 0 < x - give L r x := by omega
      rw [give_of_pos L r x hpos] at h ⊢
      rw [ih _ h]

/-! ## Tier 2: the full wheel (iterated passes, fuel-bounded) -/

/-- Iterate passes until `x = 0`, the book is exhausted, or fuel runs out. -/
def wheel (L : Nat) : Nat → List Nat → Nat → List Nat × Nat
  | 0, R, x => (R.map (fun _ => 0), x)
  | n + 1, R, x =>
      if x = 0 then (R.map (fun _ => 0), x)
      else
        let p := wheelRound L R x
        let R' := List.zipWith (fun r g => r - g) R p.1
        let q := wheel L n R' p.2
        (List.zipWith (fun a b => a + b) p.1 q.1, q.2)

theorem wheelRound_length (L : Nat) (R : List Nat) (x : Nat) :
    (wheelRound L R x).1.length = R.length := by
  induction R generalizing x with
  | nil => rfl
  | cons r R ih => simp [wheelRound, ih]

theorem wheel_length (L n : Nat) (R : List Nat) (x : Nat) :
    (wheel L n R x).1.length = R.length := by
  induction n generalizing R x with
  | zero => simp [wheel]
  | succ n ih =>
      simp only [wheel]
      split
      · simp
      · simp [List.length_zipWith, ih, wheelRound_length]

/-- Wheel conservation: total allocated plus leftover equals `x`. -/
theorem wheel_sum (L n : Nat) (R : List Nat) (x : Nat) :
    (wheel L n R x).1.sum + (wheel L n R x).2 = x := by
  induction n generalizing R x with
  | zero => simp [wheel, map_zero_sum]
  | succ n ih =>
      simp only [wheel]
      split
      · simp [map_zero_sum]
      · have hsum : ∀ (A B : List Nat), A.length = B.length →
            (List.zipWith (fun a b => a + b) A B).sum = A.sum + B.sum := by
          intro A
          induction A with
          | nil => intro B h; cases B <;> simp at h ⊢
          | cons a A ihA =>
              intro B h
              cases B with
              | nil => simp at h
              | cons b B =>
                  simp only [List.zipWith_cons_cons, List.sum_cons]
                  rw [ihA B (by simpa using h)]; omega
        have h1 := wheelRound_sum L R x
        have h2 := ih (List.zipWith (fun r g => r - g) R (wheelRound L R x).1)
                      (wheelRound L R x).2
        rw [hsum _ _ (by rw [wheelRound_length, wheel_length, List.length_zipWith,
                             wheelRound_length, Nat.min_self])]
        omega

theorem Pw_zip_add {G R A : List Nat}
    (h1 : Pw (fun g r => g ≤ r) G R)
    (h2 : Pw (fun a r => a ≤ r) A (List.zipWith (fun r g => r - g) R G)) :
    Pw (fun a r => a ≤ r) (List.zipWith (fun a b => a + b) G A) R := by
  induction h1 generalizing A with
  | nil => cases h2; exact Pw.nil
  | @cons g r G R hgr hGR ih =>
      simp only [List.zipWith_cons_cons] at h2
      cases h2 with
      | cons ha hA => exact Pw.cons (show g + _ ≤ r by omega) (ih hA)

/-- Wheel cap: no participant is allocated more than its displayed size. -/
theorem wheel_cap (L n : Nat) (R : List Nat) (x : Nat) :
    Pw (fun a r => a ≤ r) (wheel L n R x).1 R := by
  induction n generalizing R x with
  | zero => exact Pw_map_zero R
  | succ n ih =>
      simp only [wheel]
      split
      · exact Pw_map_zero R
      · exact Pw_zip_add (wheelRound_cap L R x) (ih _ _)

/-! ## Tier 1 (setter) and the composed Rule 7.37 operator -/

/-- Tier 1: the setter takes `min Qs x`; the rest goes to the wheel.
    `R` is displayed interest in wheel order *excluding* the setter's
    priority tranche (the setter's residual, if any, sits in `R`). -/
def rule737 (L fuel : Nat) (Qs : Nat) (R : List Nat) (x : Nat) : Nat × List Nat × Nat :=
  let t1 := min Qs x
  let w := wheel L fuel R (x - t1)
  (t1, w.1, w.2)

theorem rule737_setter_cap (L fuel Qs : Nat) (R : List Nat) (x : Nat) :
    (rule737 L fuel Qs R x).1 ≤ Qs := Nat.min_le_left _ _

/-- Conservation across both tiers. -/
theorem rule737_sum (L fuel Qs : Nat) (R : List Nat) (x : Nat) :
    (rule737 L fuel Qs R x).1 + (rule737 L fuel Qs R x).2.1.sum
      + (rule737 L fuel Qs R x).2.2 = x := by
  simp only [rule737]
  have := wheel_sum L fuel R (x - min Qs x)
  have := Nat.min_le_right Qs x
  omega

/-! ## NASDAQ price–time (Rule 4757) -/

/-- Strict price–time: fill the queue in arrival order. -/
def priceTime : List Nat → Nat → List Nat
  | [], _ => []
  | q :: Q, x => min q x :: priceTime Q (x - min q x)

/-- If one wheel visit is at least as large as every resting claim, a pass of
    the wheel is exactly price--time.  Thus the serial rule is the large-lot
    endpoint of the same parameterized pass operator. -/
theorem wheelRound_eq_priceTime_of_large_lot (L : Nat) (Q : List Nat) (x : Nat)
    (hlarge : ∀ q ∈ Q, q ≤ L) :
    (wheelRound L Q x).1 = priceTime Q x := by
  induction Q generalizing x with
  | nil => rfl
  | cons q Q ih =>
      have hq : q ≤ L := hlarge q (List.mem_cons_self ..)
      have hQ : ∀ r ∈ Q, r ≤ L :=
        fun r hr => hlarge r (List.mem_cons_of_mem q hr)
      have hgive : give L q x = min q x := by
        unfold give
        rw [Nat.min_eq_right (Nat.le_trans (Nat.min_le_left q x) hq)]
      simp only [wheelRound, priceTime, hgive, List.cons.injEq, true_and]
      exact ih (x - min q x) hQ

theorem priceTime_cap (Q : List Nat) (x : Nat) :
    Pw (fun a q => a ≤ q) (priceTime Q x) Q := by
  induction Q generalizing x with
  | nil => exact Pw.nil
  | cons q Q ih => exact Pw.cons (Nat.min_le_left _ _) (ih _)

theorem priceTime_sum_le (Q : List Nat) (x : Nat) : (priceTime Q x).sum ≤ x := by
  induction Q generalizing x with
  | nil => simp [priceTime]
  | cons q Q ih =>
      simp only [priceTime, List.sum_cons]
      have := ih (x - min q x); have := Nat.min_le_right q x; omega

/-- Price–time is *strictly serial*: if a later order is filled at all,
    every earlier order is filled completely. -/
theorem priceTime_serial (q : Nat) (Q : List Nat) (x : Nat)
    (h : 0 < (priceTime Q (x - min q x)).sum) : min q x = q := by
  by_cases hq : q ≤ x
  · exact Nat.min_eq_left hq
  · exfalso
    have hm : min q x = x := Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hq))
    rw [hm, Nat.sub_self] at h
    have := priceTime_sum_le Q 0
    omega

/-! ## Continuous parity (water-filling) and the book-share proposition -/

/-- Continuous parity at water level `s`. -/
def waterFill (s : Nat) (Q : List Nat) : List Nat := Q.map (fun q => min q s)

/-- Book-participant fill-share theorem (continuous parity):
    if the book is the largest participant and is not capped
    (`s ≤ Qb`), then its fill share is at most its depth share:
    `Wb / X ≤ Qb / D`, written multiplicatively as `Wb * D ≤ Qb * X`
    where `X = (waterFill s Q).sum`, `D = Q.sum`, `Wb = min Qb s = s`. -/
theorem book_share_le_depth_share (s Qb : Nat) (Q : List Nat)
    (hcap : s ≤ Qb) (hmax : ∀ q ∈ Q, q ≤ Qb) :
    (min Qb s) * Q.sum ≤ Qb * (waterFill s Q).sum := by
  rw [Nat.min_eq_right hcap]
  induction Q with
  | nil => simp [waterFill]
  | cons q Q ih =>
      simp only [waterFill, List.map_cons, List.sum_cons] at *
      have hq := hmax q (List.mem_cons_self ..)
      have ihQ := ih (fun q' hq' => hmax q' (List.mem_cons_of_mem q hq'))
      have key : s * q ≤ Qb * min q s := by
        by_cases hqs : q ≤ s
        · rw [Nat.min_eq_left hqs]; exact Nat.mul_le_mul_right q hcap
        · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hqs))]
          rw [Nat.mul_comm s q]; exact Nat.mul_le_mul_right s hq
      calc s * (q + Q.sum) = s * q + s * Q.sum := Nat.mul_add _ _ _
        _ ≤ Qb * min q s + Qb * (Q.map (fun q => min q s)).sum := Nat.add_le_add key ihQ
        _ = Qb * (min q s + (Q.map (fun q => min q s)).sum) := (Nat.mul_add _ _ _).symm

/-- Same statement with the book's displayed size required to be one of the
    participants, so that "the book is the largest participant" is literal. -/
theorem book_share_le_depth_share_mem (s Qb : Nat) (Q : List Nat)
    (hmem : Qb ∈ Q) (hcap : s ≤ Qb) (hmax : ∀ q ∈ Q, q ≤ Qb) :
    (min Qb s) * Q.sum ≤ Qb * (waterFill s Q).sum :=
  have _ := hmem
  book_share_le_depth_share s Qb Q hcap hmax


/-! ## The paper's worked example (Sec. 2.9), checked by evaluation -/

/-- L = 100, m = 4 (DMM, broker 1, broker 2, book), Q = (300,500,200,1000),
    setter = broker 2 with Qs = 200, pointer at the DMM, x = 1300. -/
def exQ : List Nat := [300, 500, 0, 1000]   -- broker 2 residual after T1 is 0
def ex := rule737 100 20 200 exQ 1300

/-- Rule 7.37 result: setter 200; wheel (DMM 300, broker 1 400, broker 2 0, book 400); nothing left. -/
theorem ex_rule737 : ex = (200, [300, 400, 0, 400], 0) := by decide

/-- Continuous parity on the post-T1 problem at water level s = 400 gives the
    same allocation and clears exactly x - 200 = 1100. -/
theorem ex_waterfill : waterFill 400 exQ = [300, 400, 0, 400] ∧ (waterFill 400 exQ).sum = 1100 := by
  decide

/-- Wheel = water-filling here to within L (in fact exactly). -/
theorem ex_within_L :
    (List.zipWith (fun a w => decide (a ≤ w + 100 ∧ w ≤ a + 100)) ex.2.1 (waterFill 400 exQ)).all id
      = true := by decide

/-- Within the post-setter parity pool, the book holds 1000/1800 of residual
    depth but receives only 400/1100 of the parity allocation. -/
theorem ex_book_share : 400 * 1800 < 1000 * 1100 := by decide

/-- NASDAQ price–time with arrival order (broker 2, DMM, broker 1, book). -/
theorem ex_priceTime : priceTime [200, 300, 500, 1000] 1300 = [200, 300, 500, 300] := by decide

end Rule737
