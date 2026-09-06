/-
  Strategic.lean — the real-valued layer done in exact integer arithmetic.
  Payoff comparisons are stated with denominators cleared over ℤ, so the
  equilibrium propositions of the companion analysis (parity contest, setter
  race, DMM parity option, venue fee competition) are certified without
  real analysis.  Lean 4.22.0, core only.
-/
import Rule737
import Markets
namespace Rule737

/-! ## Tullock contest: symmetric equilibrium is a best response

  m contestants, prize V (setter tranche or parity slot), linear cost.
  Payoff of effort e' against others' total O:  π(e') = V e'/(e'+O) − e'.
  At the symmetric equilibrium level, V·O = D² where D = e + O is total effort.
  Key identity (denominators cleared):  D·[π(e) − π(e')]·t = D·(D − t)²,  t = e'+O.
-/

theorem sq_nonneg_int (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

/-- Cleared-denominator best-response inequality.  Hypotheses: `D = e + O`
    (total effort at equilibrium), `V * O = D * D` (first-order condition),
    `t = e' + O > 0`, `D > 0`.  Conclusion: π(e') ≤ π(e), i.e.
    `(V e' − e' t) D ≤ (V e − e D) t`. -/
theorem tullock_best_response (V e e' O D t : Int)
    (hD : D = e + O) (hFOC : V * O = D * D) (ht : t = e' + O)
    (htpos : 0 < t) (hDpos : 0 < D) :
    (V * e' - e' * t) * D ≤ (V * e - e * D) * t := by
  subst hD; subst ht
  -- RHS − LHS = (e+O)·((e+O) − (e'+O))² = (e+O)(e − e')²  using V·O = (e+O)²
  have key : (V * e - e * (e + O)) * (e' + O) - (V * e' - e' * (e' + O)) * (e + O)
      = (e + O) * ((e - e') * (e - e')) := by
    have h1 : V * O * e' = (e + O) * (e + O) * e' := by rw [hFOC]
    have h2 : V * O * e = (e + O) * (e + O) * e := by rw [hFOC]
    have h3 : V * O * O = (e + O) * (e + O) * O := by rw [hFOC]
    -- expand everything and let omega match atoms
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul] at h1 h2 h3 ⊢
    simp only [Int.mul_comm, Int.mul_left_comm] at h1 h2 h3 ⊢
    omega
  have hnn : 0 ≤ (e + O) * ((e - e') * (e - e')) :=
    Int.mul_nonneg (Int.le_of_lt hDpos) (sq_nonneg_int _)
  omega

/-- Symmetric equilibrium effort in cleared form: with m contestants and
    e = (m−1)V/m², the FOC V·O = D² holds where O = (m−1)e, D = m e.
    Stated as: if m² e = (m−1) V then V·(m−1)·e = (m e)². -/
theorem tullock_symmetric_foc (m V e : Int) (h : m * m * e = (m - 1) * V) :
    V * ((m - 1) * e) = (m * e) * (m * e) := by
  have : (m * e) * (m * e) = (m * m * e) * e := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  rw [this, h]
  simp only [Int.mul_comm, Int.mul_left_comm]

/-- Rent dissipation: total equilibrium effort D = m e satisfies m·D = (m−1)·V,
    i.e. a fraction (m−1)/m of the prize is dissipated; increasing in m. -/
theorem tullock_dissipation (m V e : Int) (h : m * m * e = (m - 1) * V) :
    m * (m * e) = (m - 1) * V := by
  rw [← h]; simp only [Int.mul_assoc]

/-- Dissipated fraction (m−1)/m is strictly increasing in m:
    (m−1)/m < m/(m+1), after clearing the positive denominators. -/
theorem dissipation_increasing (m : Int) :
    (m - 1) * (m + 1) < m * m := by
  have : (m - 1) * (m + 1) = m * m - 1 := by
    simp only [Int.mul_add, Int.sub_mul, Int.one_mul, Int.mul_one]; omega
  omega

/-! ## DMM parity option: value of a free queue slot -/

/-- The DMM holds a parity slot at no queue cost.  If a parity slot is worth
    the expected fill `u/m` round lots times the half-spread `h`, the slot's
    value `(u/m)·h` is non-increasing in m (dilution) and non-decreasing in h. -/
theorem dmm_option_dilution (u m h : Nat) (hm : 0 < m) :
    (u / (m + 1)) * h ≤ (u / m) * h :=
  Nat.mul_le_mul_right h (Nat.div_le_div_left (Nat.le_succ m) hm)

theorem dmm_option_spread (u m h h' : Nat) (hh : h ≤ h') :
    (u / m) * h ≤ (u / m) * h' :=
  Nat.mul_le_mul_left _ hh

/-- Compared with a floor broker who must pay c per slot to be on the wheel,
    the DMM's net slot value exceeds the broker's by exactly c. -/
theorem dmm_advantage (slot c : Int) : slot - (slot - c) = c := by omega

/-! ## Venue fee competition: Bertrand-type routing outcome -/

/-- With two venues and the router of `bestVenue`, a venue whose net cost is
    strictly higher than the other's receives no marketable flow. -/
def flowShare (px₁ f₁ px₂ f₂ : Nat) : Nat × Nat :=
  if netCost px₁ f₁ < netCost px₂ f₂ then (1, 0)
  else if netCost px₂ f₂ < netCost px₁ f₁ then (0, 1) else (1, 1)

theorem undercut_wins (px₁ f₁ px₂ f₂ : Nat) (h : netCost px₁ f₁ < netCost px₂ f₂) :
    flowShare px₁ f₁ px₂ f₂ = (1, 0) := by simp [flowShare, h]

/-- Symmetric response: if the higher-cost venue cuts its fee below the rival's
    net cost, it captures the flow. -/
theorem fee_cut_captures (px₁ f₁ px₂ f₂ : Nat) (h : netCost px₂ f₂ < netCost px₁ f₁) :
    flowShare px₁ f₁ px₂ f₂ = (0, 1) := by
  have h1 : ¬ (netCost px₁ f₁ < netCost px₂ f₂) := by unfold netCost at *; omega
  simp [flowShare, h1, h]

/-- Under the Rule 610(c) cap, fee competition is bounded: no venue can offer
    a taker fee below zero, so the net-cost gap between venues is at most the cap
    when quoted prices are equal. -/
theorem fee_gap_bounded (px f₁ f₂ : Nat) (h₁ : f₁ ≤ feeCap) :
    netCost px f₁ - netCost px f₂ ≤ feeCap := by
  unfold netCost; omega

/-! ## Worked numbers (decided) -/

/-- m = 4, V = 1200: e = 3·1200/16 = 225, D = 900, O = 675; FOC 1200·675 = 810000 = 900². -/
theorem ex_tullock : (4:Int) * 4 * 225 = (4 - 1) * 1200 ∧ (1200:Int) * 675 = 900 * 900 := by decide

/-- Deviation to e' = 300 is not profitable: cleared inequality holds. -/
theorem ex_tullock_dev :
    ((1200:Int) * 300 - 300 * 975) * 900 ≤ ((1200:Int) * 225 - 225 * 900) * 975 := by decide

end Rule737
