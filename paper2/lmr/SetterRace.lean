/-
  SetterRace.lean — the setter race as a two-player all-pay contest for the
  setter tranche S (speed investment b ≥ 0, sunk).  Doubled payoffs (ties split)
  to stay in ℤ.  Result: for S ≥ 3 there is no pure-strategy equilibrium — the
  race is resolved only in mixed strategies, i.e. the speed rent is dissipated.
-/
namespace Rule737

/-- Twice player 1's payoff at bids (b₁, b₂), prize S, ties split. -/
def u2 (S b₁ b₂ : Int) : Int :=
  if b₂ < b₁ then 2 * S - 2 * b₁ else if b₁ = b₂ then S - 2 * b₁ else -2 * b₁

/-- A profile is a pure equilibrium if no player has a profitable unilateral deviation. -/
def PureNE (S b₁ b₂ : Int) : Prop :=
  (∀ d, 0 ≤ d → u2 S d b₂ ≤ u2 S b₁ b₂) ∧ (∀ d, 0 ≤ d → u2 S d b₁ ≤ u2 S b₂ b₁)

/-- **No pure equilibrium in the setter race** when the tranche is worth at
    least three cost units. -/
theorem setter_race_no_pure_NE (S b₁ b₂ : Int) (hS : 3 ≤ S) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂) :
    ¬ PureNE S b₁ b₂ := by
  intro ⟨hA, hB⟩
  -- Case analysis on the ordering of the bids.
  rcases Int.lt_trichotomy b₁ b₂ with hlt | heq | hgt
  · -- b₁ < b₂: player 1 loses.  Either b₂ ≥ b₁ + 2 and player 2 undercuts to b₁+1,
    -- or b₂ = b₁ + 1: if b₁ > 0 player 1 drops to 0; if b₁ = 0 player 1 jumps to 2.
    by_cases hgap : b₁ + 2 ≤ b₂
    · have := hB (b₁ + 1) (by omega)
      simp only [u2] at this
      have c1 : b₁ < b₁ + 1 := by omega
      have c2 : b₁ < b₂ := hlt
      simp [c1, c2] at this
      omega
    · have hb : b₂ = b₁ + 1 := by omega
      by_cases hz : b₁ = 0
      · have := hA 2 (by omega)
        simp only [u2] at this
        subst hz; subst hb
        simp at this; omega
      · have := hA 0 (by omega)
        simp only [u2] at this
        have c1 : ¬ b₂ < 0 := by omega
        have c2 : ¬ (0:Int) = b₂ := by omega
        have c3 : ¬ b₂ < b₁ := by omega
        have c4 : ¬ b₁ = b₂ := by omega
        simp [c1, c2, c3, c4] at this
        omega
  · -- tie: raising by one wins outright, gain 2S − 2 − 2 − (S − 2b)... profitable for S ≥ 3
    subst heq
    have := hA (b₁ + 1) (by omega)
    simp only [u2] at this
    have c1 : b₁ < b₁ + 1 := by omega
    simp [c1, Int.lt_irrefl] at this
    omega
  · -- symmetric to the first case with roles swapped
    by_cases hgap : b₂ + 2 ≤ b₁
    · have := hA (b₂ + 1) (by omega)
      simp only [u2] at this
      have c1 : b₂ < b₂ + 1 := by omega
      have c2 : b₂ < b₁ := hgt
      simp [c1, c2] at this
      omega
    · have hb : b₁ = b₂ + 1 := by omega
      by_cases hz : b₂ = 0
      · have := hB 2 (by omega)
        simp only [u2] at this
        subst hz; subst hb
        simp at this; omega
      · have := hB 0 (by omega)
        simp only [u2] at this
        have c1 : ¬ b₁ < 0 := by omega
        have c2 : ¬ (0:Int) = b₁ := by omega
        have c3 : ¬ b₁ < b₂ := by omega
        have c4 : ¬ b₂ = b₁ := by omega
        simp [c1, c2, c3, c4] at this
        omega

/-- Full dissipation bound: in any profile, the sum of doubled payoffs is at most 2S,
    and total speed spend is at least the payoff shortfall. -/
theorem race_spend (S b₁ b₂ : Int) (h₂ : 0 ≤ b₂) :
    u2 S b₁ b₂ + u2 S b₂ b₁ = 2 * S - 2 * (b₁ + b₂) := by
  unfold u2
  rcases Int.lt_trichotomy b₁ b₂ with h | h | h
  · have : ¬ b₂ < b₁ := by omega
    have : ¬ b₁ = b₂ := by omega
    have : ¬ b₂ = b₁ := by omega
    simp [*]; omega
  · subst h; simp; omega
  · have : ¬ b₁ < b₂ := by omega
    have : ¬ b₁ = b₂ := by omega
    have : ¬ b₂ = b₁ := by omega
    simp [*]; omega

end Rule737
