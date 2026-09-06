/-
  MoreRules.lean — further rules: NYSE full book (price priority across levels,
  Rule 7.37 within level), LULD price bands (Plan under Rule 608), Reg SHO
  Rule 201 short-sale price test, Rule 605 execution-quality statistics,
  MOC/LOC eligibility in the cross, Nasdaq post-only orders.  Lean 4.22.0, core only.
-/
import Rule737
import Markets
import Rulebook
import Balance
import Closure
namespace Rule737

/-! ## Wheel completeness: with enough fuel, leftover > 0 means the level is exhausted -/

def tot (S : List (Nat × Nat)) : Nat := (S.map (·.2)).sum

theorem passS_tot_le (L : Nat) (S : List (Nat × Nat)) (x : Nat) : tot (passS L S x).1 ≤ tot S := by
  induction S generalizing x with
  | nil => simp [passS, tot]
  | cons p S ih =>
      simp only [passS, visit, tot, List.map_cons, List.sum_cons] at ih ⊢
      have := ih (x - give L p.2 x)
      have := Nat.sub_le p.2 (give L p.2 x)
      omega

/-- An un-truncated pass over a non-exhausted level with L ≥ 1 strictly reduces total remaining. -/
theorem passS_tot_lt (L : Nat) (hL : 0 < L) (S : List (Nat × Nat)) (x : Nat)
    (hfull : 0 < (passS L S x).2) (hpos : 0 < tot S) : tot (passS L S x).1 < tot S := by
  induction S generalizing x with
  | nil => simp [tot] at hpos
  | cons p S ih =>
      have hle := passS_tot_le L S (x - give L p.2 x)
      have hlo := passS_leftover_le L S (x - give L p.2 x)
      have hfull' : 0 < (passS L S (x - give L p.2 x)).2 := by
        simp only [passS, visit] at hfull; exact hfull
      have hxpos : 0 < x - give L p.2 x := by omega
      have hg := give_of_pos L p.2 x hxpos
      have hgoal : tot (passS L (p :: S) x).1 = (p.2 - give L p.2 x) + tot (passS L S (x - give L p.2 x)).1 := by
        simp [passS, visit, tot]
      have hS : tot (p :: S) = p.2 + tot S := by simp [tot]
      rw [hgoal, hS]
      rw [hS] at hpos
      rw [hg] at hle hlo hfull' ⊢
      by_cases hp : 0 < p.2
      · have hm : 0 < min L p.2 := by
          rcases Nat.le_total L p.2 with h | h
          · rw [Nat.min_eq_left h]; exact hL
          · rw [Nat.min_eq_right h]; exact hp
        have hm2 : min L p.2 ≤ p.2 := Nat.min_le_right _ _
        omega
      · have hp0 : p.2 = 0 := by omega
        have := ih (x - min L p.2) hfull' (by omega)
        omega

theorem wheelS_zero_tot (L n : Nat) (S : List (Nat × Nat)) (x : Nat) (h : tot S = 0) :
    tot (wheelS L n S x).1 = 0 := by
  induction n generalizing S x with
  | zero => simpa [wheelS]
  | succ n ih =>
      simp only [wheelS]
      split
      · exact h
      · exact ih _ _ (by have := passS_tot_le L S x; omega)

/-- **Completeness.**  With L ≥ 1: if quantity is left over, then either the
    level is exhausted or fewer than `tot S` passes were available. -/
theorem wheelS_complete (L : Nat) (hL : 0 < L) (n : Nat) (S : List (Nat × Nat)) (x : Nat)
    (h : 0 < (wheelS L n S x).2) : tot (wheelS L n S x).1 = 0 ∨ n ≤ tot S := by
  induction n generalizing S x with
  | zero => right; exact Nat.zero_le _
  | succ n ih =>
      simp only [wheelS] at h ⊢
      split at h
      · omega
      · split
        · omega
        · by_cases ht : tot S = 0
          · left; exact wheelS_zero_tot L n _ _ (by have := passS_tot_le L S x; omega)
          · have hl : 0 < (passS L S x).2 := by
              by_cases hz : (passS L S x).2 = 0
              · rw [hz, wheelS_zero] at h; simp at h
              · omega
            have hlt := passS_tot_lt L hL S x hl (by omega)
            rcases ih _ _ h with h0 | hn
            · left; exact h0
            · right; omega

/-- With fuel `tot S + 1`, leftover > 0 forces exhaustion. -/
theorem wheelS_exhausts (L : Nat) (hL : 0 < L) (S : List (Nat × Nat)) (x : Nat)
    (h : 0 < (wheelS L (tot S + 1) S x).2) : tot (wheelS L (tot S + 1) S x).1 = 0 := by
  rcases wheelS_complete L hL _ S x h with h0 | hn
  · exact h0
  · omega

theorem initS_snd (R : List Nat) : (initS R).map (·.2) = R := by
  induction R with
  | nil => rfl
  | cons r R ih => simp only [initS, List.map_cons] at ih ⊢; rw [ih]
theorem initS_tot (R : List Nat) : tot (initS R) = R.sum := by
  simp only [tot]; rw [initS_snd]
theorem initS_fst_sum (R : List Nat) : ((initS R).map (·.1)).sum = 0 := by
  induction R with
  | nil => rfl
  | cons r R ih => simp only [initS, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]

theorem passS_inv (L : Nat) (S : List (Nat × Nat)) (x : Nat) :
    ((passS L S x).1.map (fun p => p.1 + p.2)).sum = (S.map (fun p => p.1 + p.2)).sum := by
  induction S generalizing x with
  | nil => rfl
  | cons p S ihS =>
      simp only [passS, visit, List.map_cons, List.sum_cons]
      rw [ihS]
      have := give_le_r L p.2 x
      omega

theorem wheelS_inv (L n : Nat) (S : List (Nat × Nat)) (x : Nat) :
    ((wheelS L n S x).1.map (fun p => p.1 + p.2)).sum = (S.map (fun p => p.1 + p.2)).sum := by
  induction n generalizing S x with
  | zero => rfl
  | succ n ih =>
      simp only [wheelS]
      split
      · rfl
      · rw [ih, passS_inv]

/-- Transfer to the fill-vector wheel: with fuel R.sum + 1 and L ≥ 1, leftover > 0
    implies the fills equal the displayed sizes. -/
theorem wheel_exhausts (L : Nat) (hL : 0 < L) (R : List Nat) (x : Nat)
    (h : 0 < (wheel L (R.sum + 1) R x).2) : (wheel L (R.sum + 1) R x).1.sum = R.sum := by
  have htot := initS_tot R
  have hsp := wheelS_spec L (R.sum + 1) (initS R) x
  have hR := initS_snd R
  rw [hR] at hsp
  have h' : 0 < (wheelS L (R.sum + 1) (initS R) x).2 := by rw [hsp.2]; exact h
  rw [← htot] at h'
  have hex := wheelS_exhausts L hL (initS R) x h'
  rw [htot] at hex
  -- allocated + remaining = original size for each participant; remaining sum 0 ⇒ allocated sum = R.sum
  have h1 := wheelS_inv L (R.sum + 1) (initS R) x
  have hsplit : ∀ (S : List (Nat × Nat)), (S.map (fun p => p.1 + p.2)).sum = (S.map (·.1)).sum + (S.map (·.2)).sum := by
    intro S; induction S with
    | nil => rfl
    | cons p S ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega
  rw [hsplit, hsplit] at h1
  simp only [tot] at hex
  have h0 := initS_fst_sum R
  rw [hex, h0, hR, wheelS_eq_wheel] at h1
  omega

/-! ## Estate-indexed indivisible equal awards -/

/-- The unit-increment wheel is an estate-indexed discrete equal-awards
    completion.  The large fuel bound is determined only by the claims. -/
def discreteCEA (Q : List Nat) (E : Nat) : List Nat :=
  (wheel 1 (Q.sum + 1) Q E).1

/-- The estate-indexed completion is feasible for every integer estate. -/
theorem discreteCEA_feasible (Q : List Nat) (E : Nat) :
    Feasible Q (discreteCEA Q E) E := by
  unfold discreteCEA Feasible
  refine ⟨wheel_cap 1 (Q.sum + 1) Q E, ?_⟩
  have hcap := Pw_le_sum (wheel_cap 1 (Q.sum + 1) Q E)
  have hsum := wheel_sum 1 (Q.sum + 1) Q E
  by_cases hzero : (wheel 1 (Q.sum + 1) Q E).2 = 0
  · rw [hzero, Nat.add_zero] at hsum
    rw [hsum, Nat.min_eq_left]
    omega
  · have hpos : 0 < (wheel 1 (Q.sum + 1) Q E).2 := Nat.pos_of_ne_zero hzero
    have hex := wheel_exhausts 1 (by omega) Q E hpos
    rw [hex]
    rw [Nat.min_eq_right]
    omega

/-- Resetting the deterministic rotation at each estate destroys composition:
    on two equal claims, one unit followed by one unit gives `(2,0)`, whereas
    the two-unit estate gives `(1,1)`.  Persisting the pointer is therefore not
    optional if this tie-break is to be stream consistent. -/
theorem discreteCEA_reset_not_composable :
    let Q : List Nat := [10, 10]
    let A := discreteCEA Q 1
    let R := List.zipWith (fun q a => q - a) Q A
    List.zipWith (fun a b => a + b) A (discreteCEA R 1) ≠
      discreteCEA Q 2 := by
  decide


/-! ## NYSE full book: price priority across levels, 7.37 within a level -/

/-- A level is (price, setter tranche, displayed parity sizes in wheel order). -/
structure Level where
  price : Nat
  setter : Nat
  parity : List Nat

/-- Walk ask levels ≤ limit; at each apply the two-tier 7.37 operator. -/
def matchNYSE (L fuel limit : Nat) : List Level → Nat → List (Nat × Nat × List Nat) × Nat
  | [], x => ([], x)
  | lv :: rest, x =>
      if lv.price ≤ limit then
        let r := rule737 L fuel lv.setter lv.parity x
        let used := r.1 + r.2.1.sum
        let q := matchNYSE L fuel limit rest (x - used)
        ((lv.price, r.1, r.2.1) :: q.1, q.2)
      else ((lv.price, 0, lv.parity.map (fun _ => 0)) ::
              rest.map (fun l => (l.price, 0, l.parity.map (fun _ => 0))), x)

theorem zeroedNYSE (rest : List Level) :
    ((rest.map (fun l => (l.price, 0, l.parity.map (fun _ => (0:Nat))))).map
        (fun t => t.2.1 + t.2.2.sum)).sum = 0 := by
  induction rest with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, map_zero_sum]; simpa using ih

theorem matchNYSE_conserve (L fuel limit : Nat) (lvs : List Level) (x : Nat) :
    ((matchNYSE L fuel limit lvs x).1.map (fun t => t.2.1 + t.2.2.sum)).sum
      + (matchNYSE L fuel limit lvs x).2 = x := by
  induction lvs generalizing x with
  | nil => simp [matchNYSE]
  | cons lv rest ih =>
      simp only [matchNYSE]
      split
      · simp only [List.map_cons, List.sum_cons]
        have hs := rule737_sum L fuel lv.setter lv.parity x
        have := ih (x - ((rule737 L fuel lv.setter lv.parity x).1 + (rule737 L fuel lv.setter lv.parity x).2.1.sum))
        omega
      · simp only [List.map_cons, List.sum_cons, map_zero_sum, zeroedNYSE]; omega

/-- **Price priority over parity.**  With L ≥ 1 and fuel ≥ Σparity + 1 at the
    top marketable level, if any deeper level receives quantity then the top
    level was exhausted: its setter tranche and every displayed parity share
    were filled in full. -/
theorem nyse_price_priority (L limit : Nat) (hL : 0 < L) (lv : Level) (rest : List Level) (x : Nat)
    (h : 0 < ((matchNYSE L (lv.parity.sum + 1) limit rest
        (x - ((rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).1
            + (rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).2.1.sum))).1.map
          (fun t => t.2.1 + t.2.2.sum)).sum) :
    (rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).1 = lv.setter ∧
    (rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).2.1.sum = lv.parity.sum := by
  have hc := matchNYSE_conserve L (lv.parity.sum + 1) limit rest
      (x - ((rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).1
            + (rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).2.1.sum))
  have hs := rule737_sum L (lv.parity.sum + 1) lv.setter lv.parity x
  have hleft : 0 < (rule737 L (lv.parity.sum + 1) lv.setter lv.parity x).2.2 := by omega
  simp only [rule737] at hleft ⊢
  have hw := wheel_exhausts L hL lv.parity (x - min lv.setter x) hleft
  refine ⟨?_, hw⟩
  -- setter: leftover > 0 after T1 and T2 means x > min Qs x ... hence min Qs x = Qs
  have := wheel_sum L (lv.parity.sum + 1) lv.parity (x - min lv.setter x)
  by_cases hq : lv.setter ≤ x
  · exact Nat.min_eq_left hq
  · exfalso
    rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hq)), Nat.sub_self] at hleft this
    omega

/-! ## LULD price bands -/

/-- Bands: reference ± pct% (pct in percent), floor rounding. -/
def luldBands (ref pct : Nat) : Nat × Nat := (ref - ref * pct / 100, ref + ref * pct / 100)

theorem lower_le_ref (ref pct : Nat) : (luldBands ref pct).1 ≤ ref := Nat.sub_le _ _
theorem ref_le_upper (ref pct : Nat) : ref ≤ (luldBands ref pct).2 := Nat.le_add_right _ _
theorem bands_widen (ref p q : Nat) (h : p ≤ q) :
    (luldBands ref q).1 ≤ (luldBands ref p).1 ∧ (luldBands ref p).2 ≤ (luldBands ref q).2 := by
  unfold luldBands
  have : ref * p / 100 ≤ ref * q / 100 := Nat.div_le_div_right (Nat.mul_le_mul_left ref h)
  constructor <;> omega

/-- An execution is LULD-compliant iff inside the bands; a limit state is declared
    when the NBO equals the lower band or the NBB equals the upper band. -/
def inBands (ref pct px : Nat) : Bool :=
  decide ((luldBands ref pct).1 ≤ px ∧ px ≤ (luldBands ref pct).2)
def limitState (ref pct nbb nbo : Nat) : Bool :=
  decide (nbo = (luldBands ref pct).1 ∨ nbb = (luldBands ref pct).2)

/-- A limit state is only ever declared with the NBO at the lower band or the
    NBB at the upper band, both of which lie inside the bands. -/
theorem limitState_boundary (ref pct nbb nbo : Nat) (h : limitState ref pct nbb nbo = true) :
    inBands ref pct nbo = true ∨ inBands ref pct nbb = true := by
  simp only [limitState, decide_eq_true_eq] at h
  rcases h with h | h
  · left; simp [inBands, h]
    have := lower_le_ref ref pct; have := ref_le_upper ref pct; omega
  · right; simp [inBands, h]
    have := lower_le_ref ref pct; have := ref_le_upper ref pct; omega

theorem ref_in_bands (ref pct : Nat) : inBands ref pct ref = true := by
  simp [inBands, lower_le_ref, ref_le_upper]

/-! ## Reg SHO Rule 201: short-sale price test -/

/-- When the circuit breaker is in effect, a short sale may execute only above the NBB. -/
def shortSaleOK (breaker : Bool) (px nbb : Nat) : Bool := !breaker || decide (nbb < px)

theorem no_short_at_or_below_nbb (px nbb : Nat) (h : shortSaleOK true px nbb = true) : nbb < px := by
  simpa [shortSaleOK] using h

theorem short_ok_when_no_breaker (px nbb : Nat) : shortSaleOK false px nbb = true := by
  simp [shortSaleOK]

/-! ## Rule 605 execution-quality statistics -/

/-- Signed doubled buy-side effective-spread kernel.  Prices enter as natural
    tick counts, but subtraction is performed in `Int`, so executions below the
    midpoint retain their negative magnitude.  A complete Rule 605 statistic
    still needs side, order classification, time, and aggregation inputs. -/
def effSpread2 (px nbb nbo : Nat) : Int :=
  2 * (px : Int) - ((nbb : Int) + (nbo : Int))
def priceImprovement (px nbo : Nat) : Nat := nbo - px

/-- At the NBO the effective spread equals the quoted spread (scaled by 1); inside it is less. -/
theorem eff_at_nbo (nbb nbo : Nat) :
    effSpread2 nbo nbb nbo = (nbo : Int) - (nbb : Int) := by
  unfold effSpread2; omega
theorem eff_le_quoted (px nbb nbo : Nat) (h : px ≤ nbo) :
    effSpread2 px nbb nbo ≤ (nbo : Int) - (nbb : Int) := by
  unfold effSpread2; omega
/-- The signed kernel is negative exactly for an execution below the midpoint. -/
theorem effSpread2_neg_iff (px nbb nbo : Nat) :
    effSpread2 px nbb nbo < 0 ↔ 2 * px < nbb + nbo := by
  unfold effSpread2
  omega
/-- The separate price-improvement proxy is bounded by the quoted spread; when
    the grid midpoint is exact (even bid-plus-offer), the spread proxy is zero. -/
theorem pi_le_spread (px nbb nbo : Nat) (h : nbb ≤ px) : priceImprovement px nbo ≤ nbo - nbb := by
  unfold priceImprovement; omega
theorem midpoint_zero_eff (nbb nbo : Nat) (h : (nbb + nbo) % 2 = 0) :
    effSpread2 ((nbb + nbo) / 2) nbb nbo = 0 := by
  unfold effSpread2; omega

/-! ## MOC / LOC eligibility in the cross -/

/-- A limit-on-close buy participates iff its limit is at or above the cross price;
    market-on-close always participates. -/
def locEligible (limit cross : Nat) : Bool := decide (cross ≤ limit)
def mocEligible : Bool := true

/-- Eligibility is monotone in the limit and antitone in the cross price. -/
theorem loc_mono (l l' c : Nat) (h : l ≤ l') (he : locEligible l c = true) : locEligible l' c = true := by
  simp [locEligible] at *; omega
theorem loc_anti (l c c' : Nat) (h : c' ≤ c) (he : locEligible l c = true) : locEligible l c' = true := by
  simp [locEligible] at *; omega

/-! ## Post-only orders (Nasdaq 4702(b)(4)) -/

/-- A post-only buy that would remove liquidity (limit ≥ best ask) is rejected
    unless it would execute with price improvement of at least one tick... in the
    simplest form: it rests only if it does not lock the book. -/
def postOnly (limit bestAsk : Nat) : Option Nat :=
  if limit < bestAsk then some limit else none

theorem postOnly_rests_iff (limit bestAsk p : Nat) (h : postOnly limit bestAsk = some p) :
    p = limit ∧ limit < bestAsk := by
  unfold postOnly at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

/-- A resting post-only order never removes liquidity: it is below the best ask. -/
theorem postOnly_never_takes (limit bestAsk p : Nat) (h : postOnly limit bestAsk = some p) :
    ¬ (bestAsk ≤ p) := by
  have := postOnly_rests_iff limit bestAsk p h; omega

/-! ## Worked -/
def exLevels : List Level := [⟨1000, 200, [300, 500, 0, 1000]⟩, ⟨1001, 0, [400]⟩]
theorem ex_nyse :
    matchNYSE 100 20 1001 exLevels 2200 =
      ([(1000, 200, [300, 500, 0, 1000]), (1001, 0, [200])], 0) ∧
    matchNYSE 100 20 1001 exLevels 1500 =
      ([(1000, 200, [300, 500, 0, 500]), (1001, 0, [0])], 0) := by decide
theorem ex_luld : luldBands 10000 5 = (9500, 10500) ∧ inBands 10000 5 10600 = false := by decide

end Rule737
