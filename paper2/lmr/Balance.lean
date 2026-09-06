/-
  Balance.lean — the general O(L) theorem: the round-lot parity wheel is
  L-balanced, hence pointwise within one round lot of continuous water-filling
  at some water level.  Also: cross tie-breaking (max volume, then min
  imbalance) and the Rule 610(c) access-fee cap.  Lean 4.22.0, core only.
-/
import Rule737
import Markets
namespace Rule737

/-! ## Stateful wheel: participants carry (allocated, remaining) -/

def visit (L : Nat) (p : Nat × Nat) (x : Nat) : (Nat × Nat) × Nat :=
  let g := give L p.2 x
  ((p.1 + g, p.2 - g), x - g)

def passS (L : Nat) : List (Nat × Nat) → Nat → List (Nat × Nat) × Nat
  | [], x => ([], x)
  | p :: S, x =>
      let v := visit L p x
      let q := passS L S v.2
      (v.1 :: q.1, q.2)

def wheelS (L : Nat) : Nat → List (Nat × Nat) → Nat → List (Nat × Nat) × Nat
  | 0, S, x => (S, x)
  | n + 1, S, x => if x = 0 then (S, x) else
      let p := passS L S x
      wheelS L n p.1 p.2

/-- Initial state from displayed sizes. -/
def initS (R : List Nat) : List (Nat × Nat) := R.map (fun r => (0, r))

/-- Agreement with the fill-vector wheel on the paper's worked example. -/
theorem ex_wheelS_agrees :
    ((wheelS 100 20 (initS exQ) 1100).1.map (·.1), (wheelS 100 20 (initS exQ) 1100).2)
      = wheel 100 20 exQ 1100 := by decide

/-! ## Invariants -/

/-- Before a pass: every participant has allocation ≤ v, and every
    unexhausted participant has allocation exactly v. -/
def AllAt (v : Nat) (S : List (Nat × Nat)) : Prop :=
  ∀ p ∈ S, p.1 ≤ v ∧ (0 < p.2 → p.1 = v)

/-- After the last pass: all allocations ≤ w + L, unexhausted ≥ w. -/
def Band (L w : Nat) (S : List (Nat × Nat)) : Prop :=
  (∀ p ∈ S, p.1 ≤ w + L) ∧ (∀ q ∈ S, 0 < q.2 → w ≤ q.1)

/-- L-balanced: any participant is within L above any unexhausted one. -/
def Balanced (L : Nat) (S : List (Nat × Nat)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, 0 < q.2 → p.1 ≤ q.1 + L

theorem Band_Balanced {L w : Nat} {S : List (Nat × Nat)} (h : Band L w S) : Balanced L S := by
  intro p hp q hq hq2
  have := h.1 p hp; have := h.2 q hq hq2; omega

theorem passS_sum (L : Nat) (S : List (Nat × Nat)) (x : Nat) :
    x - (passS L S x).2 ≤ x := Nat.sub_le _ _

theorem passS_leftover_le (L : Nat) (S : List (Nat × Nat)) (x : Nat) :
    (passS L S x).2 ≤ x := by
  induction S generalizing x with
  | nil => exact Nat.le_refl _
  | cons p S ih =>
      simp only [passS, visit]
      exact Nat.le_trans (ih _) (Nat.sub_le _ _)

/-- Any pass (truncated or not) maps `AllAt v` (every participant at level `v`) to `Band L v`. -/
theorem passS_band (L v : Nat) (S : List (Nat × Nat)) (x : Nat) (h : AllAt v S) :
    Band L v (passS L S x).1 := by
  induction S generalizing x with
  | nil => exact ⟨fun p hp => by simp [passS] at hp, fun q hq => by simp [passS] at hq⟩
  | cons p S ih =>
      have hp := h p (List.mem_cons_self ..)
      have hS : AllAt v S := fun q hq => h q (List.mem_cons_of_mem p hq)
      have ihS := ih (x - give L p.2 x) hS
      simp only [passS, visit]
      constructor
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · have := give_le_L L p.2 x; simp only; omega
        · exact ihS.1 q hq'
      · intro q hq hq2
        rcases List.mem_cons.mp hq with rfl | hq'
        · simp only at hq2 ⊢
          have hg := give_le_r L p.2 x
          have : 0 < p.2 := by omega
          have := hp.2 this; omega
        · exact ihS.2 q hq' hq2

/-- An un-truncated pass preserves the equal-allocation invariant, raising it by L. -/
theorem passS_eq (L v : Nat) (S : List (Nat × Nat)) (x : Nat) (h : AllAt v S)
    (hfull : 0 < (passS L S x).2) : AllAt (v + L) (passS L S x).1 := by
  induction S generalizing x with
  | nil => intro p hp; simp [passS] at hp
  | cons p S ih =>
      have hp := h p (List.mem_cons_self ..)
      have hS : AllAt v S := fun q hq => h q (List.mem_cons_of_mem p hq)
      simp only [passS, visit] at hfull ⊢
      have hlo := passS_leftover_le L S (x - give L p.2 x)
      have hpos : 0 < x - give L p.2 x := by omega
      have hg := give_of_pos L p.2 x hpos
      have ihS := ih (x - give L p.2 x) hS hfull
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · simp only
        rw [hg]
        constructor
        · have := Nat.min_le_left L p.2; omega
        · intro hr
          -- remaining after: p.2 - min L p.2 > 0 ⇒ min L p.2 = L and p.2 > 0
          have h1 : min L p.2 = L := by
            by_cases hl : L ≤ p.2
            · exact Nat.min_eq_left hl
            · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hl))] at hr; omega
          have h2 : 0 < p.2 := by omega
          rw [h1, hp.2 h2]
      · exact ihS q hq'

theorem wheelS_zero (L n : Nat) (S : List (Nat × Nat)) : wheelS L n S 0 = (S, 0) := by
  cases n <;> simp [wheelS]

/-- **Main theorem (band form).**  From any `AllAt v` state, the wheel ends in a
    band `[w, w + L]` for some water level `w ≥ v`. -/
theorem wheelS_band (L n : Nat) (S : List (Nat × Nat)) (x v : Nat) (h : AllAt v S) :
    ∃ w, v ≤ w ∧ Band L w (wheelS L n S x).1 := by
  induction n generalizing S x v with
  | zero =>
      refine ⟨v, Nat.le_refl _, ?_, ?_⟩
      · intro p hp; have := (h p hp).1; omega
      · intro q hq hq2; simp only [wheelS] at hq; rw [(h q hq).2 hq2]; exact Nat.le_refl _
  | succ n ih =>
      simp only [wheelS]
      split
      · refine ⟨v, Nat.le_refl _, ?_, ?_⟩
        · intro p hp; have := (h p hp).1; omega
        · intro q hq hq2; rw [(h q hq).2 hq2]; exact Nat.le_refl _
      · by_cases hl : (passS L S x).2 = 0
        · rw [hl, wheelS_zero]
          exact ⟨v, Nat.le_refl _, passS_band L v S x h⟩
        · have hE := passS_eq L v S x h (Nat.pos_of_ne_zero hl)
          obtain ⟨w, hw, hb⟩ := ih _ _ _ hE
          exact ⟨w, by omega, hb⟩

/-- A computable water-level witness.  It starts at `v` and adds one lot for
    every completed pass that leaves quantity for another pass. -/
def wheelLevel (L : Nat) : Nat → List (Nat × Nat) → Nat → Nat → Nat
  | 0, _, _, v => v
  | n + 1, S, x, v =>
      if x = 0 then v
      else
        let p := passS L S x
        if p.2 = 0 then v else wheelLevel L n p.1 p.2 (v + L)

/-- Explicit form of `wheelS_band`: the existential water level is the
    executable value returned by `wheelLevel`. -/
theorem wheelS_band_explicit (L n : Nat) (S : List (Nat × Nat)) (x v : Nat)
    (h : AllAt v S) :
    Band L (wheelLevel L n S x v) (wheelS L n S x).1 := by
  induction n generalizing S x v with
  | zero =>
      simp only [wheelLevel, wheelS]
      constructor
      · intro p hp
        have := (h p hp).1
        omega
      · intro q hq hq2
        rw [(h q hq).2 hq2]
        exact Nat.le_refl _
  | succ n ih =>
      simp only [wheelLevel, wheelS]
      by_cases hx : x = 0
      · rw [if_pos hx, if_pos hx]
        constructor
        · intro p hp
          have := (h p hp).1
          omega
        · intro q hq hq2
          rw [(h q hq).2 hq2]
          exact Nat.le_refl _
      · rw [if_neg hx, if_neg hx]
        by_cases hl : (passS L S x).2 = 0
        · rw [if_pos hl, hl, wheelS_zero]
          exact passS_band L v S x h
        · rw [if_neg hl]
          apply ih
          exact passS_eq L v S x h (Nat.pos_of_ne_zero hl)

/-- **Corollary: the wheel is L-balanced** (Proposition *wheel*, general form). -/
theorem wheelS_balanced (L n : Nat) (R : List Nat) (x : Nat) :
    Balanced L (wheelS L n (initS R) x).1 := by
  have h0 : AllAt 0 (initS R) := by
    intro p hp
    simp only [initS, List.mem_map] at hp
    obtain ⟨r, _, rfl⟩ := hp
    exact ⟨Nat.le_refl _, fun _ => rfl⟩
  obtain ⟨w, _, hb⟩ := wheelS_band L n (initS R) x 0 h0
  exact Band_Balanced hb

/-- At unit lot size, the band theorem is exactly the usual integer
    balancedness condition: no allocation exceeds an unexhausted peer by more
    than one share. -/
theorem wheelS_unit_balanced (n : Nat) (R : List Nat) (x : Nat) :
    Balanced 1 (wheelS 1 n (initS R) x).1 :=
  wheelS_balanced 1 n R x

/-- **Corollary: within one round lot of water-filling.**  There is a water
    level `w` such that every participant's wheel allocation `a` is within `L`
    of `min (a + r₀) w`, where `a + r₀` is its original displayed size
    (allocation plus remainder is invariant). -/
theorem wheelS_within_L (L n : Nat) (R : List Nat) (x : Nat) :
    ∃ w, ∀ p ∈ (wheelS L n (initS R) x).1,
      p.1 ≤ min (p.1 + p.2) w + L ∧ min (p.1 + p.2) w ≤ p.1 + L := by
  have h0 : AllAt 0 (initS R) := by
    intro p hp
    simp only [initS, List.mem_map] at hp
    obtain ⟨r, _, rfl⟩ := hp
    exact ⟨Nat.le_refl _, fun _ => rfl⟩
  obtain ⟨w, _, hb⟩ := wheelS_band L n (initS R) x 0 h0
  refine ⟨w, fun p hp => ?_⟩
  have h1 := hb.1 p hp
  by_cases hr : 0 < p.2
  · have h2 := hb.2 p hp hr
    have : min (p.1 + p.2) w = w := Nat.min_eq_right (by omega)
    omega
  · have hz : p.2 = 0 := by omega
    rw [hz, Nat.add_zero]
    by_cases hpw : p.1 ≤ w
    · rw [Nat.min_eq_left hpw]; omega
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hpw))]; omega

/-- Auditor-facing approximation theorem with an explicit, executable water
    level rather than an existential witness. -/
theorem wheelS_within_L_explicit (L n : Nat) (R : List Nat) (x : Nat) :
    ∀ p ∈ (wheelS L n (initS R) x).1,
      p.1 ≤ min (p.1 + p.2) (wheelLevel L n (initS R) x 0) + L ∧
      min (p.1 + p.2) (wheelLevel L n (initS R) x 0) ≤ p.1 + L := by
  have h0 : AllAt 0 (initS R) := by
    intro p hp
    simp only [initS, List.mem_map] at hp
    obtain ⟨r, _, rfl⟩ := hp
    exact ⟨Nat.le_refl _, fun _ => rfl⟩
  have hb := wheelS_band_explicit L n (initS R) x 0 h0
  intro p hp
  have h1 := hb.1 p hp
  by_cases hr : 0 < p.2
  · have h2 := hb.2 p hp hr
    have hmin : min (p.1 + p.2) (wheelLevel L n (initS R) x 0) =
        wheelLevel L n (initS R) x 0 := Nat.min_eq_right (by omega)
    rw [hmin]
    omega
  · have hz : p.2 = 0 := by omega
    rw [hz, Nat.add_zero]
    by_cases hpw : p.1 ≤ wheelLevel L n (initS R) x 0
    · rw [Nat.min_eq_left hpw]
      omega
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hpw))]
      omega

/-! ## Cross tie-breaking: maximum volume, then minimum imbalance -/

def imbAt (bids asks : List (Nat × Nat)) (p : Nat) : Nat :=
  (imbalanceAt bids asks p).1 + (imbalanceAt bids asks p).2

/-- Lexicographic key: volume first, then (B − imbalance), valid when imbalance ≤ B. -/
def crossKey (bids asks : List (Nat × Nat)) (B p : Nat) : Nat :=
  matchedAt bids asks p * (B + 1) + (B - imbAt bids asks p)

def crossPrice2 (bids asks : List (Nat × Nat)) (B : Nat) (cands : List Nat) : Nat :=
  cands.foldl (fun best p =>
    if crossKey bids asks B best < crossKey bids asks B p then p else best) (cands.headD 0)

theorem crossKey_lex (m₁ i₁ m₂ i₂ B : Nat) (h₁ : i₁ ≤ B) (h₂ : i₂ ≤ B)
    (h : m₁ * (B + 1) + (B - i₁) ≤ m₂ * (B + 1) + (B - i₂)) :
    m₁ ≤ m₂ ∧ (m₁ = m₂ → i₂ ≤ i₁) := by
  constructor
  · by_cases hc : m₁ ≤ m₂
    · exact hc
    · have hlt : m₂ + 1 ≤ m₁ := Nat.lt_of_not_le hc
      have hm := Nat.mul_le_mul_right (B + 1) hlt
      rw [Nat.add_mul, Nat.one_mul] at hm
      generalize m₁ * (B + 1) = A at h hm
      generalize m₂ * (B + 1) = C at h hm
      omega
  · intro hm; subst hm
    generalize m₁ * (B + 1) = A at h
    omega

/-- The two-criterion cross price maximizes volume and, among volume
    maximizers, minimizes imbalance (Nasdaq Rules 4752(b)/4754(b), criteria 1–2). -/
theorem foldl_sel_mem (f : Nat → Nat) (M : List Nat) :
    ∀ (l : List Nat) (b : Nat), b ∈ M → (∀ c ∈ l, c ∈ M) →
      l.foldl (fun best p => if f best < f p then p else best) b ∈ M := by
  intro l
  induction l with
  | nil => intro b hb _; simpa
  | cons c cs ih =>
      intro b hb hl
      simp only [List.foldl_cons]
      apply ih
      · split
        · exact hl c (List.mem_cons_self ..)
        · exact hb
      · intro d hd; exact hl d (List.mem_cons_of_mem c hd)

theorem crossPrice2_lex (bids asks : List (Nat × Nat)) (B : Nat) (cands : List Nat)
    (hB : ∀ p ∈ cands, imbAt bids asks p ≤ B) (hne : cands ≠ []) :
    ∀ p ∈ cands,
      matchedAt bids asks p ≤ matchedAt bids asks (crossPrice2 bids asks B cands) ∧
      (matchedAt bids asks p = matchedAt bids asks (crossPrice2 bids asks B cands) →
        imbAt bids asks (crossPrice2 bids asks B cands) ≤ imbAt bids asks p) := by
  intro p hp
  have hkey := foldl_argmax_ge (crossKey bids asks B) cands (cands.headD 0) p hp
  have hmem : crossPrice2 bids asks B cands ∈ cands := by
    unfold crossPrice2
    have hh : cands.headD 0 ∈ cands := by
      cases cands with
      | nil => exact absurd rfl hne
      | cons c cs => simp
    exact foldl_sel_mem _ cands cands _ hh (fun c hc => hc)
  exact crossKey_lex _ _ _ _ B (hB p hp) (hB _ hmem) hkey

/-- Tie-break example: candidates 1000 and 1001 both considered; 1001 wins on volume;
    with B = 4000 the key is valid (all imbalances ≤ total size 2900). -/
theorem ex_cross2 :
    crossPrice2 exBids exAsks 4000 [998, 999, 1000, 1001, 1002, 1003] = 1001 ∧
    (∀ p ∈ [998, 999, 1000, 1001, 1002, 1003], imbAt exBids exAsks p ≤ 4000) := by decide

/-! ## Rule 610(c): access-fee cap of $0.003 per share -/

def feeCap : Nat := 30   -- $0.0030 in units of $0.0001

/-- A protected quote's all-in taker cost is bounded by price plus the cap. -/
theorem netCost_le_cap (px fee : Nat) (h : fee ≤ feeCap) : netCost px fee ≤ px + feeCap := by
  unfold netCost; omega

/-- Effective spread including fees is at most the quoted spread plus two caps. -/
theorem fee_adjusted_spread (nbb nbo fb fo : Nat) (hb : fb ≤ feeCap) (ho : fo ≤ feeCap) :
    (nbo + fo) - (nbb - fb) ≤ (nbo - nbb) + 2 * feeCap := by
  unfold feeCap at *; omega

end Rule737
