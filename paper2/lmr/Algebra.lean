/-
  Algebra.lean — the algebra of allocation operators: sequential composition
  of tiers and levels, conservation closure, equivariance and
  monotonicity axioms, the serial/band impossibility theorem, and uniqueness
  of the price–time ladder.  Lean 4.22.0, core only.
-/
import Rule737
import Rulebook
import Balance
namespace Rule737

/-! ## Operators and sequential composition -/

/-- An allocation operator: incoming quantity ↦ (fills, leftover). -/
def Op := Nat → List Nat × Nat

/-- Conservative: fills sum plus leftover equals input. -/
def Conserves (f : Op) : Prop := ∀ x, (f x).1.sum + (f x).2 = x

/-- Sequential composition: run f, feed its leftover to g, concatenate fills. -/
def seq (f g : Op) : Op := fun x =>
  let a := f x
  let b := g a.2
  (a.1 ++ b.1, b.2)

theorem sum_append (a b : List Nat) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, List.sum_cons, ih]; omega

/-- Conservation is preserved by composition. Quantity absorbed obeys a
    residual-input cocycle, not a homomorphism from operators to a fixed
    additive codomain. -/
theorem seq_conserves {f g : Op} (hf : Conserves f) (hg : Conserves g) : Conserves (seq f g) := by
  intro x
  simp only [seq, sum_append]
  have := hf x; have := hg (f x).2
  omega

/-- Composition is associative. -/
theorem seq_assoc (f g h : Op) (x : Nat) : seq (seq f g) h x = seq f (seq g h) x := by
  simp [seq, List.append_assoc]

/-- The identity operator (no fills). -/
def idOp : Op := fun x => ([], x)
theorem seq_id_left (f : Op) (x : Nat) : seq idOp f x = f x := by simp [seq, idOp]
theorem seq_id_right (f : Op) (x : Nat) : seq f idOp x = f x := by simp [seq, idOp]

/-- The tiers of Rule 7.37 are a composition: setter, then wheel, then hidden wheel. -/
def setterOp (Qs : Nat) : Op := fun x => ([min Qs x], x - min Qs x)
def wheelOp (L fuel : Nat) (R : List Nat) : Op := fun x => wheel L fuel R x
/-- Canonical wheel operator: fuel `R.sum + 1` always suffices (`wheel_exhausts`),
    so this is the non-degenerate member of the family `wheelOp L · R`. -/
def wheelOpFull (L : Nat) (R : List Nat) : Op := wheelOp L (R.sum + 1) R
def ptOp (Q : List Nat) : Op := fun x => (priceTime Q x, x - (priceTime Q x).sum)

theorem setterOp_conserves (Qs : Nat) : Conserves (setterOp Qs) := by
  intro x; simp [setterOp]; have := Nat.min_le_right Qs x; omega
theorem wheelOp_conserves (L fuel : Nat) (R : List Nat) : Conserves (wheelOp L fuel R) :=
  fun x => wheel_sum L fuel R x
theorem wheelOpFull_conserves (L : Nat) (R : List Nat) : Conserves (wheelOpFull L R) :=
  wheelOp_conserves L _ R
theorem ptOp_conserves (Q : List Nat) : Conserves (ptOp Q) := by
  intro x; simp only [ptOp]; have := priceTime_sum_le Q x; omega

/-- Rule 7.37 as a composite, and its conservation obtained algebraically. -/
def rule737Op (L fuel Qs : Nat) (R H : List Nat) : Op :=
  seq (setterOp Qs) (seq (wheelOp L fuel R) (wheelOp L fuel H))
theorem rule737Op_conserves (L fuel Qs : Nat) (R H : List Nat) : Conserves (rule737Op L fuel Qs R H) :=
  seq_conserves (setterOp_conserves Qs) (seq_conserves (wheelOp_conserves _ _ _) (wheelOp_conserves _ _ _))

/-- Agreement with the direct definition. -/
theorem rule737Op_eq (L fuel Qs : Nat) (R H : List Nat) (x : Nat) :
    (rule737Op L fuel Qs R H x).1 = [(rule737full L fuel Qs R H x).1] ++ (rule737full L fuel Qs R H x).2.1
      ++ (rule737full L fuel Qs R H x).2.2.1 ∧
    (rule737Op L fuel Qs R H x).2 = (rule737full L fuel Qs R H x).2.2.2 := by
  simp [rule737Op, seq, setterOp, wheelOp, rule737full]

/-- A ladder is a fold of level operators under `seq`. -/
def ladderOp : List Op → Op
  | [] => idOp
  | f :: fs => seq f (ladderOp fs)
theorem ladderOp_conserves (fs : List Op) (h : ∀ f ∈ fs, Conserves f) : Conserves (ladderOp fs) := by
  induction fs with
  | nil => intro x; simp [ladderOp, idOp]
  | cons f fs ih =>
      exact seq_conserves (h f (List.mem_cons_self ..)) (ih (fun g hg => h g (List.mem_cons_of_mem f hg)))

/-! ## Equivariance and monotonicity -/

/-- Water-filling is equivariant under transformations that commute with every
    pointwise map (including permutations), so the benchmark is anonymous. -/
theorem waterFill_map (s : Nat) (Q : List Nat) (σ : List Nat → List Nat)
    (hσ : ∀ f : Nat → Nat, ∀ l, σ (l.map f) = (σ l).map f) :
    waterFill s (σ Q) = σ (waterFill s Q) := by
  unfold waterFill; rw [hσ]

/-- Price–time is *not* anonymous: reversing the queue changes the allocation. -/
theorem priceTime_not_anonymous :
    priceTime [200, 300] 200 ≠ (priceTime [300, 200] 200).reverse := by decide

/-- Price–time is monotone in incoming quantity, pointwise. -/
theorem priceTime_mono (Q : List Nat) (x y : Nat) (h : x ≤ y) :
    Pw (fun a b => a ≤ b) (priceTime Q x) (priceTime Q y) := by
  induction Q generalizing x y with
  | nil => exact Pw.nil
  | cons q Q ih =>
      simp only [priceTime]
      refine Pw.cons (by omega) (ih _ _ ?_)
      by_cases hq : q ≤ x
      · rw [Nat.min_eq_left hq, Nat.min_eq_left (Nat.le_trans hq h)]; omega
      · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hq))]; omega

/-- Water-filling is monotone in the water level, pointwise. -/
theorem waterFill_mono (Q : List Nat) (s t : Nat) (h : s ≤ t) :
    Pw (fun a b => a ≤ b) (waterFill s Q) (waterFill t Q) := by
  induction Q with
  | nil => exact Pw.nil
  | cons q Q ih => exact Pw.cons (by simp; omega) ih

/-! ## Impossibility: no allocation is both serial and banded -/

/-- **Impossibility theorem.**  With two participants each holding more than one
    round lot and incoming quantity x with L < x ≤ q₁, any feasible serial
    allocation gives (x, 0), which violates the band axiom (participant 2 is
    unexhausted, yet participant 1 is more than L ahead).  Hence no venue can
    be simultaneously price–time and parity. -/
theorem serial_band_incompatible (L q₁ q₂ x a₁ a₂ : Nat)
    (hx : L < x) (hq₁ : x ≤ q₁) (hq₂ : 0 < q₂)
    (hf : Feasible [q₁, q₂] [a₁, a₂] x) (hs : Serial [a₁, a₂] [q₁, q₂]) :
    (∀ w, ¬ ((a₁ ≤ w + L ∧ a₂ ≤ w + L) ∧ (0 < q₂ - a₂ → w ≤ a₂))) ∧ a₂ + L < a₁ := by
  have hu := serial_unique [q₁, q₂] [a₁, a₂] x hf hs
  simp only [priceTime, Nat.min_eq_right hq₁, Nat.sub_self, List.cons.injEq] at hu
  obtain ⟨h1, h2, _⟩ := hu
  have h2' : a₂ = 0 := by
    have : min q₂ 0 = 0 := Nat.min_eq_right (Nat.zero_le _)
    omega
  subst h1; subst h2'
  constructor
  · intro w ⟨⟨hb1, _⟩, hun⟩
    have := hun (by omega)
    omega
  · omega

/-- The same instance, decided: (200,200), L = 100, x = 200. -/
theorem ex_incompatible :
    priceTime [200, 200] 200 = [200, 0] ∧ ¬ (200 ≤ 0 + 100) := by decide

/-! ## Uniqueness of the price–time ladder -/

/-- Level-wise feasibility and cross-level seriality for a ladder allocation
    (all levels assumed marketable). -/
def LadderSerial : List (List Nat) → List (List Nat) → Prop
  | [], [] => True
  | a :: A, q :: Q => (0 < (A.map List.sum).sum → a = q) ∧ Serial a q ∧ LadderSerial A Q
  | _, _ => False

/-- Marketable ladder matching (no limit) as a list of per-level fills. -/
def ptLadder : List (List Nat) → Nat → List (List Nat)
  | [], _ => []
  | q :: Q, x => priceTime q x :: ptLadder Q (x - (priceTime q x).sum)

theorem ptLadder_sum_le (Q : List (List Nat)) (x : Nat) : ((ptLadder Q x).map List.sum).sum ≤ x := by
  induction Q generalizing x with
  | nil => simp [ptLadder]
  | cons q Q ih =>
      simp only [ptLadder, List.map_cons, List.sum_cons]
      have := priceTime_sum_le q x; have := ih (x - (priceTime q x).sum); omega

/-- **Ladder uniqueness.**  Any allocation that is level-wise feasible-and-serial and
    serial across levels equals the price–time ladder. -/
theorem ladder_unique (Q A : List (List Nat)) (x : Nat)
    (hlen : A.length = Q.length)
    (hcap : ∀ i, i < A.length → Pw (fun a q => a ≤ q) (A[i]!) (Q[i]!))
    (hsum : (A.map List.sum).sum = min x (Q.map List.sum).sum)
    (hs : LadderSerial A Q) : A = ptLadder Q x := by
  induction Q generalizing A x with
  | nil => cases A with | nil => rfl | cons => simp at hlen
  | cons q Q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          simp only [LadderSerial] at hs
          obtain ⟨hcross, hser, hrest⟩ := hs
          have hcap0 := hcap 0 (by simp)
          simp only [List.getElem!_cons_zero] at hcap0
          simp only [List.map_cons, List.sum_cons] at hsum
          have hAle : (A.map List.sum).sum ≤ (Q.map List.sum).sum := by
            -- from per-level caps
            have : ∀ (A Q : List (List Nat)), A.length = Q.length →
                (∀ i, i < A.length → Pw (fun a q => a ≤ q) (A[i]!) (Q[i]!)) →
                (A.map List.sum).sum ≤ (Q.map List.sum).sum := by
              intro A
              induction A with
              | nil => intros; simp
              | cons a A ihA =>
                  intro Q hl hc
                  cases Q with
                  | nil => simp at hl
                  | cons q Q =>
                      simp only [List.map_cons, List.sum_cons]
                      have h0 := hc 0 (by simp)
                      simp only [List.getElem!_cons_zero] at h0
                      have := Pw_le_sum h0
                      have := ihA Q (by simpa using hl) (fun i hi => by
                        have := hc (i+1) (by simp; omega)
                        simpa using this)
                      omega
            exact this A Q (by simpa using hlen) (fun i hi => by
              have := hcap (i+1) (by simp; omega); simpa using this)
          have hale := Pw_le_sum hcap0
          -- head level equals priceTime q x
          have hhead : a = priceTime q x := by
            apply serial_unique q a x ⟨hcap0, ?_⟩ hser
            by_cases hpos : 0 < (A.map List.sum).sum
            · rw [hcross hpos] at hsum ⊢
              have : q.sum ≤ x := by omega
              rw [Nat.min_eq_right this]
            · have hz : (A.map List.sum).sum = 0 := by omega
              rw [hz] at hsum
              by_cases hqx : q.sum ≤ x
              · rw [Nat.min_eq_right hqx]; omega
              · rw [Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hqx))]; omega
          subst hhead
          simp only [ptLadder]
          congr 1
          apply ih A (x - (priceTime q x).sum) (by simpa using hlen)
            (fun i hi => by have := hcap (i+1) (by simp; omega); simpa using this)
          · omega
          · exact hrest

end Rule737
