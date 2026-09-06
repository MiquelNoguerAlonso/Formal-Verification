/-
  Orders.lean — order-type catalogue (NYSE Rule 7.31 / Nasdaq 4703): MPL,
  reserve, discretionary (D-order), primary/market peg; self-help (Rule 611(b)(1));
  three-criterion cross / NYSE auction with DMM facilitation.  Lean 4.22.0, core only.
-/
import Rule737
import Markets
import Balance
import Rulebook
namespace Rule737

/-! ## Mid-Point Liquidity (MPL) -/

/-- Floor of the midpoint on the $0.0001 display grid. Odd sums lose a half-grid
    unit and therefore need the doubled-price representation below for an exact
    execution-price statement. -/
def midpoint (nbb nbo : Nat) : Nat := (nbb + nbo) / 2

/-- The floored midpoint lies in the half-open interval [NBB, NBO). It need not
    be strictly above NBB when the spread is one display-grid unit. -/
theorem midpoint_inside (nbb nbo : Nat) (h : nbb < nbo) :
    nbb ≤ midpoint nbb nbo ∧ midpoint nbb nbo < nbo := by
  unfold midpoint; omega

/-- Exact midpoint in doubled $0.0001 units: an odd value represents a half-grid
    execution price without rounding. -/
def midpoint2 (nbb nbo : Nat) : Nat := nbb + nbo

/-- In doubled units, the exact midpoint is strictly inside every non-locked
    spread, including a one-unit spread on the display grid. -/
theorem midpoint2_strict_inside (nbb nbo : Nat) (h : nbb < nbo) :
    2 * nbb < midpoint2 nbb nbo ∧ midpoint2 nbb nbo < 2 * nbo := by
  unfold midpoint2
  omega

/-- MPL never trades through: the midpoint is at or better than the NBO for a buyer. -/
theorem mpl_no_trade_through (nbb nbo : Nat) (h : nbb < nbo) :
    ¬ tradeThroughBuy (midpoint nbb nbo) nbo :=
  Nat.not_lt.mpr (Nat.le_of_lt (midpoint_inside nbb nbo h).2)

/-- An MPL order cannot execute in a locked or crossed market (Rule 7.31(d)(3)). -/
def mplEligible (nbb nbo : Nat) : Bool := decide (nbb < nbo)

/-! ## Reserve orders -/

/-- (displayed, reserve).  A fill of `x` consumes display first; when the
    display is exhausted it is replenished from reserve up to `disp0` and the
    order receives a new time stamp (modelled as the Bool flag). -/
structure Reserve where
  disp : Nat
  res  : Nat

def fillReserve (disp0 : Nat) (o : Reserve) (x : Nat) : Reserve × Nat × Bool :=
  let f := min o.disp x
  let d := o.disp - f
  if d = 0 ∧ 0 < o.res then
    let top := min disp0 o.res
    (⟨top, o.res - top⟩, f, true)
  else (⟨d, o.res⟩, f, false)

/-- Conservation: displayed + reserve decreases by exactly the fill. -/
theorem fillReserve_conserve (disp0 : Nat) (o : Reserve) (x : Nat) :
    (fillReserve disp0 o x).1.disp + (fillReserve disp0 o x).1.res + (fillReserve disp0 o x).2.1
      = o.disp + o.res := by
  have h1 := Nat.min_le_left o.disp x
  have h2 := Nat.min_le_left disp0 o.res
  by_cases hc : o.disp - min o.disp x = 0 ∧ 0 < o.res
  · simp only [fillReserve, hc, and_self, if_true]; omega
  · simp only [fillReserve, hc, if_false]; omega

/-- Replenishment happens only when the display is exhausted with reserve left,
    and then the new display is at most `disp0`. -/
theorem fillReserve_replenish (disp0 : Nat) (o : Reserve) (x : Nat)
    (h : (fillReserve disp0 o x).2.2 = true) :
    (fillReserve disp0 o x).1.disp ≤ disp0 ∧ o.disp ≤ x := by
  by_cases hc : o.disp - min o.disp x = 0 ∧ 0 < o.res
  · simp only [fillReserve, hc, and_self, if_true]
    refine ⟨Nat.min_le_left _ _, ?_⟩
    have := hc.1
    by_cases hx : o.disp ≤ x
    · exact hx
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hx))] at this; omega
  · simp only [fillReserve, hc, if_false] at h; cases h

/-- Hidden-depth certificate specialised to reserve: a fill exceeding the
    display implies reserve at least the excess (uses tier-3 semantics). -/
theorem reserve_certificate (disp res f : Nat) (h : f ≤ disp + res) (hf : disp < f) :
    f - disp ≤ res := by omega

/-! ## Discretionary (D-) orders -/

/-- Displayed at `disp`, may execute up to `limit ≥ disp` (buy side) against
    contra-side interest at price `p`.  Executes at `p` iff `disp ≤ p ≤ limit`. -/
def dOrderExec (disp limit p : Nat) : Option Nat :=
  if disp ≤ p ∧ p ≤ limit then some p else none

theorem dOrder_within (disp limit p q : Nat) (h : dOrderExec disp limit p = some q) :
    disp ≤ q ∧ q ≤ limit := by
  unfold dOrderExec at h
  split at h
  · cases h; assumption
  · cases h

/-- Discretion never exceeds the limit: a D-order is Rule 611 compliant whenever
    its limit is at or below the NBO. -/
theorem dOrder_compliant (disp limit p q nbo : Nat) (h : dOrderExec disp limit p = some q)
    (hl : limit ≤ nbo) : ¬ tradeThroughBuy q nbo :=
  compliant_of_le q nbo (Nat.le_trans (dOrder_within disp limit p q h).2 hl)

/-! ## Pegged orders -/

/-- Primary peg (buy): tracks the NBB plus an offset, capped by the limit.
    Market peg (buy): tracks the NBO minus an offset, capped by the limit. -/
def primaryPegBuy (nbb offset limit : Nat) : Nat := min (nbb + offset) limit
def marketPegBuy (nbo offset limit : Nat) : Nat := min (nbo - offset) limit

theorem primaryPeg_le_limit (nbb o l : Nat) : primaryPegBuy nbb o l ≤ l := Nat.min_le_right _ _
theorem marketPeg_le_limit (nbo o l : Nat) : marketPegBuy nbo o l ≤ l := Nat.min_le_right _ _

/-- A market-pegged buy with a positive offset never locks the NBO. -/
theorem marketPeg_no_lock (nbo o l : Nat) (ho : 0 < o) (hn : o ≤ nbo) :
    marketPegBuy nbo o l < nbo := by
  unfold marketPegBuy; have := Nat.min_le_left (nbo - o) l; omega

/-- A primary-pegged buy with zero offset re-prices monotonically with the NBB. -/
theorem primaryPeg_mono (nbb nbb' o l : Nat) (h : nbb ≤ nbb') :
    primaryPegBuy nbb o l ≤ primaryPegBuy nbb' o l := by
  unfold primaryPegBuy
  have := Nat.min_le_left (nbb + o) l
  have := Nat.min_le_right (nbb + o) l
  have h1 := Nat.add_le_add_right h o
  by_cases hc : nbb' + o ≤ l
  · rw [Nat.min_eq_left hc]; omega
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hc))]; omega

/-! ## Self-help (Rule 611(b)(1)) -/

/-- A venue that has declared self-help against venue `v` treats `v`'s quotes
    as unprotected. -/
def protectedSH (L : Nat) (selfHelp : List Nat) (q : Quote) : Bool :=
  protected_ L q && !(selfHelp.contains q.venue)

def nboSH (L : Nat) (selfHelp : List Nat) (asks : List Quote) : Option Nat :=
  (asks.filter (protectedSH L selfHelp)).foldl (fun acc q =>
    match acc with
    | none => some q.price
    | some b => some (min b q.price)) none

theorem foldl_min_opt_sub (l₁ l₂ : List Quote)
    (hsub : ∀ q ∈ l₁, q ∈ l₂) (v₁ v₂ : Nat)
    (h₁ : l₁.foldl (fun acc q => match acc with
        | none => some q.price | some b => some (min b q.price)) none = some v₁)
    (h₂ : l₂.foldl (fun acc q => match acc with
        | none => some q.price | some b => some (min b q.price)) none = some v₂) :
    v₂ ≤ v₁ := by
  -- v₁ is the price of some element of l₁ ⊆ l₂, and v₂ ≤ every price in l₂
  have hattain : ∀ (l : List Quote) (acc : Option Nat) (v : Nat),
      l.foldl (fun acc q => match acc with
        | none => some q.price | some b => some (min b q.price)) acc = some v →
      (acc = some v) ∨ (∃ q ∈ l, q.price = v) := by
    intro l
    induction l with
    | nil => intro acc v h; simp at h; exact Or.inl (by rw [h])
    | cons r rs ih =>
        intro acc v h
        simp only [List.foldl_cons] at h
        rcases ih _ v h with h' | ⟨q, hq, hqv⟩
        · cases acc with
          | none => simp at h'; exact Or.inr ⟨r, List.mem_cons_self .., h'⟩
          | some b =>
              simp at h'
              by_cases hb : b ≤ r.price
              · rw [Nat.min_eq_left hb] at h'; exact Or.inl (by rw [h'])
              · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hb))] at h'
                exact Or.inr ⟨r, List.mem_cons_self .., h'⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem r hq, hqv⟩
  rcases hattain l₁ none v₁ h₁ with h | ⟨q, hq, hqv⟩
  · simp at h
  · have := foldl_min_opt_le l₂ none q (hsub q hq) v₂ h₂
    omega

/-- **Self-help only relaxes protection**: declaring self-help can only raise the
    NBO (fewer protected offers), never lower it. -/
theorem selfhelp_raises_nbo (L : Nat) (sh : List Nat) (asks : List Quote) (v v' : Nat)
    (h : nbo L asks = some v) (h' : nboSH L sh asks = some v') : v ≤ v' := by
  unfold nbo at h; unfold nboSH at h'
  apply foldl_min_opt_sub (asks.filter (protectedSH L sh)) (asks.filter (protected_ L)) _ v' v h' h
  intro q hq
  have := List.mem_filter.mp hq
  refine List.mem_filter.mpr ⟨this.1, ?_⟩
  have h2 := this.2
  simp [protectedSH] at h2
  exact h2.1

/-! ## Three-criterion cross / NYSE auction: volume, imbalance, reference proximity -/

def dist (a b : Nat) : Nat := (a - b) + (b - a)

theorem dist_comm (a b : Nat) : dist a b = dist b a := by unfold dist; omega
theorem dist_self (a : Nat) : dist a a = 0 := by unfold dist; omega

/-- Lexicographic key with bounds `B` on imbalance and `D` on distance to the reference. -/
def crossKey3 (bids asks : List (Nat × Nat)) (B D ref p : Nat) : Nat :=
  (matchedAt bids asks p * (B + 1) + (B - imbAt bids asks p)) * (D + 1) + (D - dist p ref)

def crossPrice3 (bids asks : List (Nat × Nat)) (B D ref : Nat) (cands : List Nat) : Nat :=
  cands.foldl (fun best p =>
    if crossKey3 bids asks B D ref best < crossKey3 bids asks B D ref p then p else best)
    (cands.headD 0)

theorem lex2 (k₁ d₁ k₂ d₂ D : Nat) (h₁ : d₁ ≤ D) (h₂ : d₂ ≤ D)
    (h : k₁ * (D + 1) + (D - d₁) ≤ k₂ * (D + 1) + (D - d₂)) :
    k₁ ≤ k₂ ∧ (k₁ = k₂ → d₂ ≤ d₁) := by
  constructor
  · by_cases hc : k₁ ≤ k₂
    · exact hc
    · have hlt : k₂ + 1 ≤ k₁ := Nat.lt_of_not_le hc
      have hm := Nat.mul_le_mul_right (D + 1) hlt
      rw [Nat.add_mul, Nat.one_mul] at hm
      generalize k₁ * (D + 1) = A at h hm
      generalize k₂ * (D + 1) = C at h hm
      omega
  · intro hk; subst hk
    generalize k₁ * (D + 1) = A at h
    omega

/-- **Three criteria.**  The auction price maximizes volume; among volume
    maximizers minimizes imbalance; among those, is closest to the reference price
    (NYSE Rule 7.35(a)(10); Nasdaq 4752(b)/4754(b)). -/
theorem crossPrice3_lex (bids asks : List (Nat × Nat)) (B D ref : Nat) (cands : List Nat)
    (hB : ∀ p ∈ cands, imbAt bids asks p ≤ B) (hD : ∀ p ∈ cands, dist p ref ≤ D)
    (hne : cands ≠ []) :
    let p' := crossPrice3 bids asks B D ref cands
    ∀ p ∈ cands,
      matchedAt bids asks p ≤ matchedAt bids asks p' ∧
      (matchedAt bids asks p = matchedAt bids asks p' → imbAt bids asks p' ≤ imbAt bids asks p) ∧
      (matchedAt bids asks p = matchedAt bids asks p' → imbAt bids asks p = imbAt bids asks p' →
        dist p' ref ≤ dist p ref) := by
  intro p' p hp
  have hkey := foldl_argmax_ge (crossKey3 bids asks B D ref) cands (cands.headD 0) p hp
  have hmem : p' ∈ cands := by
    have hh : cands.headD 0 ∈ cands := by
      cases cands with
      | nil => exact absurd rfl hne
      | cons c cs => simp
    exact foldl_sel_mem _ cands cands _ hh (fun c hc => hc)
  have hl := lex2 _ _ _ _ D (hD p hp) (hD p' hmem) hkey
  have hl2 := crossKey_lex _ _ _ _ B (hB p hp) (hB p' hmem) hl.1
  refine ⟨hl2.1, hl2.2, ?_⟩
  intro hm hi
  apply hl.2
  show matchedAt bids asks p * (B + 1) + (B - imbAt bids asks p) =
       matchedAt bids asks p' * (B + 1) + (B - imbAt bids asks p')
  rw [hm, hi]

/-! ## NYSE auction with DMM facilitation -/

/-- After the auction price is set, the DMM absorbs residual imbalance up to
    its committed size `c`; the remaining imbalance is what the DMM does not cover. -/
def dmmFacilitate (imb c : Nat) : Nat × Nat := (min imb c, imb - min imb c)

theorem dmm_clears (imb c : Nat) (h : imb ≤ c) : (dmmFacilitate imb c).2 = 0 := by
  unfold dmmFacilitate; rw [Nat.min_eq_left h]; omega

theorem dmm_conserve (imb c : Nat) :
    (dmmFacilitate imb c).1 + (dmmFacilitate imb c).2 = imb := by
  unfold dmmFacilitate; have := Nat.min_le_left imb c; omega

/-- Worked auction: three-criterion price with reference 10.00 (=100000 units of 0.0001?
    here prices are in cents as in exBids/exAsks). -/
theorem ex_auction :
    crossPrice3 exBids exAsks 4000 100 1000 [998, 999, 1000, 1001, 1002, 1003] = 1001 ∧
    dmmFacilitate 200 500 = (200, 0) := by decide

end Rule737
