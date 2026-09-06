/-
  Closure.lean — closes the two remaining semantic items:
  (A) the stateful wheel agrees with the fill-vector wheel in general;
  (B) the setter race's mixed equilibrium in exact arithmetic: the uniform
      strategy on an integer grid is an ε-equilibrium with ε = ½ cost unit,
      uniformly in the grid size (so relative to the prize it vanishes).
-/
import Rule737
import Balance
import SetterRace
namespace Rule737

/-! ## (A) wheelS ≡ wheel -/

theorem passS_spec (L : Nat) (S : List (Nat × Nat)) (x : Nat) :
    (passS L S x).1.map (·.1) = List.zipWith (fun a b => a + b) (S.map (·.1)) (wheelRound L (S.map (·.2)) x).1 ∧
    (passS L S x).1.map (·.2) = List.zipWith (fun r g => r - g) (S.map (·.2)) (wheelRound L (S.map (·.2)) x).1 ∧
    (passS L S x).2 = (wheelRound L (S.map (·.2)) x).2 := by
  induction S generalizing x with
  | nil => simp [passS, wheelRound]
  | cons p S ih =>
      obtain ⟨h1, h2, h3⟩ := ih (x - give L p.2 x)
      simp only [passS, visit, wheelRound, List.map_cons, List.zipWith_cons_cons]
      exact ⟨by rw [h1], by rw [h2], h3⟩

theorem zip_add_zero (S : List (Nat × Nat)) :
    List.zipWith (fun a b => a + b) (S.map (·.1)) ((S.map (·.2)).map (fun _ => 0)) = S.map (·.1) := by
  induction S with
  | nil => rfl
  | cons p S ih => simp only [List.map_cons, List.zipWith_cons_cons, Nat.add_zero]; rw [ih]

theorem zip_add_assoc (A G F : List Nat) :
    List.zipWith (fun a b => a + b) (List.zipWith (fun a b => a + b) A G) F
      = List.zipWith (fun a b => a + b) A (List.zipWith (fun a b => a + b) G F) := by
  induction A generalizing G F with
  | nil => simp
  | cons a A ihA =>
      cases G with
      | nil => simp
      | cons g G =>
          cases F with
          | nil => simp
          | cons f F => simp only [List.zipWith_cons_cons, Nat.add_assoc]; rw [ihA]

theorem wheelS_spec (L n : Nat) (S : List (Nat × Nat)) (x : Nat) :
    (wheelS L n S x).1.map (·.1) = List.zipWith (fun a b => a + b) (S.map (·.1)) (wheel L n (S.map (·.2)) x).1 ∧
    (wheelS L n S x).2 = (wheel L n (S.map (·.2)) x).2 := by
  induction n generalizing S x with
  | zero =>
      dsimp only [wheelS, wheel]
      exact ⟨(zip_add_zero S).symm, rfl⟩
  | succ n ih =>
      dsimp only [wheelS, wheel]
      split
      · exact ⟨(zip_add_zero S).symm, rfl⟩
      · obtain ⟨p1, p2, p3⟩ := passS_spec L S x
        obtain ⟨q1, q2⟩ := ih (passS L S x).1 (passS L S x).2
        refine ⟨?_, ?_⟩
        · rw [q1, p1, p2, p3, zip_add_assoc]
        · rw [q2, p2, p3]

/-- **Agreement.**  From displayed sizes R, the stateful wheel's allocations
    are exactly the fill-vector wheel's fills; hence the balance theorem
    transfers to `wheel`. -/
theorem wheelS_eq_wheel (L n : Nat) (R : List Nat) (x : Nat) :
    (wheelS L n (initS R) x).1.map (·.1) = (wheel L n R x).1 := by
  have h := (wheelS_spec L n (initS R) x).1
  have hR : ∀ R : List Nat, (initS R).map (·.2) = R := by
    intro R; induction R with
    | nil => rfl
    | cons r R ih => simp only [initS, List.map_cons] at ih ⊢; rw [ih]
  have h0 : ∀ R : List Nat, (initS R).map (·.1) = R.map (fun _ => 0) := by
    intro R; induction R with
    | nil => rfl
    | cons r R ih => simp only [initS, List.map_cons] at ih ⊢; rw [ih]
  rw [h, hR, h0]
  have hl := wheel_length L n R x
  generalize (wheel L n R x).1 = F at hl
  clear h
  induction R generalizing F with
  | nil => cases F with | nil => rfl | cons => simp at hl
  | cons r R ih =>
      cases F with
      | nil => simp at hl
      | cons f F =>
          simp only [List.map_cons, List.zipWith_cons_cons, Nat.zero_add]
          rw [ih F (by simpa using hl)]

/-- Balance on the stateful representation (see `wheel_within_L` for the statement on `wheel`). -/
theorem wheel_balanced (L n : Nat) (R : List Nat) (x : Nat) :
    ∃ w, ∀ p ∈ (wheelS L n (initS R) x).1,
      p.1 ≤ min (p.1 + p.2) w + L ∧ min (p.1 + p.2) w ≤ p.1 + L :=
  wheelS_within_L L n R x


/-- Pointwise invariant: a pass preserves `allocated + remaining` for every participant. -/
theorem passS_pair (L : Nat) (S : List (Nat × Nat)) (x : Nat) :
    (passS L S x).1.map (fun p => p.1 + p.2) = S.map (fun p => p.1 + p.2) := by
  induction S generalizing x with
  | nil => rfl
  | cons p S ih =>
      simp only [passS, visit, List.map_cons]
      rw [ih]
      have := give_le_r L p.2 x
      congr 1; omega

theorem wheelS_pair (L n : Nat) (S : List (Nat × Nat)) (x : Nat) :
    (wheelS L n S x).1.map (fun p => p.1 + p.2) = S.map (fun p => p.1 + p.2) := by
  induction n generalizing S x with
  | zero => rfl
  | succ n ih =>
      dsimp only [wheelS]
      split
      · rfl
      · rw [ih, passS_pair]

theorem initS_pair (R : List Nat) : (initS R).map (fun p => p.1 + p.2) = R := by
  induction R with
  | nil => rfl
  | cons r R ih => simp only [initS, List.map_cons] at ih ⊢; rw [ih, Nat.zero_add]

theorem pairs_recover (W : List (Nat × Nat)) :
    List.zipWith (fun a s => (a, s - a)) (W.map (·.1)) (W.map (fun p => p.1 + p.2)) = W := by
  induction W with
  | nil => rfl
  | cons p W ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [ih, Nat.add_sub_cancel_left]

/-- The stateful wheel's final state is literally `(fill, size − fill)` zipped over `wheel`. -/
theorem wheelS_state_eq (L n : Nat) (R : List Nat) (x : Nat) :
    (wheelS L n (initS R) x).1 = List.zipWith (fun a r => (a, r - a)) (wheel L n R x).1 R := by
  have h := pairs_recover (wheelS L n (initS R) x).1
  rw [wheelS_eq_wheel, wheelS_pair, initS_pair] at h
  exact h.symm

theorem zipWith_pair_mem {β : Type} (f : Nat → Nat → β) :
    ∀ (F R : List Nat) (a r : Nat), (a, r) ∈ List.zipWith Prod.mk F R → f a r ∈ List.zipWith f F R := by
  intro F
  induction F with
  | nil => intro R a r h; cases R <;> simp at h
  | cons a' F ih =>
      intro R a r h
      cases R with
      | nil => simp at h
      | cons r' R =>
          simp only [List.zipWith_cons_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · left; cases h; rfl
          · right; exact ih R a r h

/-- **Balance for `wheel` itself.**  Pair each fill with its displayed size:
    there is a water level `w` such that every fill is within `L` of
    `min(size, w)`.  This is `wheelS_within_L` transported along
    `wheelS_state_eq`; no reference to the stateful wheel remains. -/
theorem wheel_within_L (L n : Nat) (R : List Nat) (x : Nat) :
    ∃ w, ∀ q ∈ List.zipWith Prod.mk (wheel L n R x).1 R,
      q.1 ≤ min q.2 w + L ∧ min q.2 w ≤ q.1 + L := by
  obtain ⟨w, hw⟩ := wheelS_within_L L n R x
  refine ⟨w, ?_⟩
  intro q hq
  have hcap : q.1 ≤ q.2 := by
    have := wheel_cap L n R x
    -- extract the pointwise cap from Pw via membership in the zip
    clear hw
    have hl := wheel_length L n R x
    generalize (wheel L n R x).1 = F at this hl hq
    induction this with
    | nil => simp at hq
    | cons h _ ih =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at hq
        rcases hq with hq | hq
        · subst hq; exact h
        · exact ih (by simpa using hl) hq
  have hm := zipWith_pair_mem (fun a r => (a, r - a)) _ _ q.1 q.2 hq
  rw [← wheelS_state_eq] at hm
  have := hw _ hm
  simp only at this
  rw [Nat.add_sub_cancel' hcap] at this
  exact this

/-! ## (B) Uniform mixed strategy is an ε-equilibrium of the setter race -/

/-- Σ_{j=0}^{n} 2·u₁(b, j) with prize N and bids on {0,…,N}. -/
def sumU (N b : Int) : Nat → Int
  | 0 => u2 N b 0
  | n + 1 => sumU N b n + u2 N b (n + 1)

macro "lin" : tactic => `(tactic| (simp only [Int.mul_add, Int.add_mul, Int.sub_mul, Int.mul_sub,
    Int.mul_one, Int.one_mul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] at *; omega))

theorem sumU_closed (N b : Int) (hb : 0 ≤ b) (n : Nat) :
    (((n:Int) < b) → sumU N b n = 2 * N * (n:Int) + 2 * N - 2 * b * (n:Int) - 2 * b) ∧
    ((b ≤ (n:Int)) → sumU N b n = 2 * N * b + N - 2 * b - 2 * b * (n:Int)) := by
  induction n with
  | zero =>
      simp only [sumU, u2, Int.ofNat_zero]
      constructor
      · intro h
        simp [show (0:Int) < b from h]
      · intro h
        have hb0 : b = 0 := by omega
        subst hb0; simp
  | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · intro h
        have hn : (n:Int) < b := by push_cast at h; omega
        simp only [sumU]
        rw [ih1 hn]
        have c1 : ((n:Int) + 1) < b := by push_cast at h; omega
        simp only [u2, c1, show ¬ b = (n:Int) + 1 by omega, if_true, if_false]
        push_cast; lin
      · intro h
        simp only [sumU]
        by_cases hlt : (n:Int) < b
        · have hb' : b = (n:Int) + 1 := by push_cast at h; omega
          rw [ih1 hlt]
          simp only [u2, hb', if_true]
          push_cast; lin
        · have hle : b ≤ (n:Int) := by omega
          rw [ih2 hle]
          simp only [u2, show ¬ ((n:Int) + 1 < b) by omega, show ¬ b = (n:Int) + 1 by omega, if_false]
          push_cast; lin

/-- **ε-equilibrium.**  Against a uniform opponent on {0,…,N}, the (N+1)-scaled
    doubled expected payoff of any bid b ∈ {0,…,N} is N − 2b, so
    |E[u](b)| ≤ N / (2(N+1)) < ½: every pure bid is within half a cost unit of
    indifference, uniformly in N.  In prize units (prize N) the gap is < 1/(2N). -/
theorem uniform_payoff (N : Nat) (b : Int) (hb : 0 ≤ b) (hbN : b ≤ N) :
    sumU N b N = N - 2 * b := by
  have := (sumU_closed N b hb N).2 hbN
  rw [this]; lin

theorem uniform_eps (N : Nat) (b : Int) (hb : 0 ≤ b) (hbN : b ≤ N) :
    -(N:Int) ≤ sumU N b N ∧ sumU N b N ≤ N := by
  rw [uniform_payoff N b hb hbN]; omega

/-- Σ_{b=0}^{n} (N − 2b), the uniform player's own doubled payoff summed over its support. -/
def sumSelf (N : Int) : Nat → Int
  | 0 => N
  | n + 1 => sumSelf N n + (N - 2 * ((n:Int) + 1))

theorem sumSelf_closed (N : Int) (n : Nat) : sumSelf N n = ((n:Int) + 1) * N - (n:Int) * ((n:Int) + 1) := by
  induction n with
  | zero => simp [sumSelf]
  | succ n ih => simp only [sumSelf, ih]; push_cast; lin

/-- **Value of the uniform profile is zero:** summing `uniform_payoff` over the
    support gives Σ_b (N − 2b) = 0, so a uniform player earns exactly 0 in
    expectation against a uniform opponent. -/
theorem uniform_selfpayoff_zero (N : Nat) : sumSelf N N = 0 := by
  rw [sumSelf_closed]; lin

/-- **ε-equilibrium, relative form.**  The best deviation from the uniform
    profile is the bid 0, worth doubled payoff N over N+1 states, i.e. an
    expected gain of N/(N+1) < 1 doubled unit = ½ cost unit.  Relative to the
    prize N the gain is < 1/N, so the uniform profile is an ε-equilibrium
    with ε/S → 0.  Stated with cleared denominators: the doubled gain of any
    bid is at most N, and strictly less than N + 1. -/
theorem uniform_eps_relative (N : Nat) (b : Int) (hb : 0 ≤ b) (hbN : b ≤ N) :
    sumU N b N ≤ N ∧ sumU N b N < (N:Int) + 1 := by
  rw [uniform_payoff N b hb hbN]; omega

end Rule737
