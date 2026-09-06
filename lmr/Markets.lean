/-
  Markets.lean — remaining market rules of "The Mathematics of NASDAQ and NYSE":
  T3 non-displayed tier, opening/closing crosses, Reg NMS (Rule 610 lock/cross,
  Rule 611 order protection, Rule 612 sub-penny / effective tick), DMM parity
  dilution, SIP-vs-direct two-clock event model, venue fee routing, and the
  observability section (parity-count fingerprint, hidden-depth bound).
  Lean 4.22.0, core only.  No `sorry`.
-/
import Rule737
namespace Rule737

/-! ## Tier 3: non-displayed interest, and the full three-tier operator -/

theorem Pw_le_sum {A R : List Nat} (h : Pw (fun a r => a ≤ r) A R) : A.sum ≤ R.sum := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hab _ ih => simp only [List.sum_cons]; omega

/-- Full Rule 7.37: setter (T1), displayed parity wheel (T2), non-displayed
    parity wheel (T3) over hidden/reserve/MPL sizes `H`.  Returns
    (setter fill, displayed fills, non-displayed fills, leftover). -/
def rule737full (L fuel Qs : Nat) (R H : List Nat) (x : Nat) :
    Nat × List Nat × List Nat × Nat :=
  let t1 := min Qs x
  let w := wheel L fuel R (x - t1)
  let h := wheel L fuel H w.2
  (t1, w.1, h.1, h.2)

theorem rule737full_sum (L fuel Qs : Nat) (R H : List Nat) (x : Nat) :
    let o := rule737full L fuel Qs R H x
    o.1 + o.2.1.sum + o.2.2.1.sum + o.2.2.2 = x := by
  simp only [rule737full]
  have := wheel_sum L fuel R (x - min Qs x)
  have := wheel_sum L fuel H (wheel L fuel R (x - min Qs x)).2
  have := Nat.min_le_right Qs x
  omega

/-- Displayed-before-hidden: T3 receives nothing unless all displayed
    interest reachable by the wheel has been offered the quantity first —
    formally, if T3 gets anything then T2 left `x - t1 - Σ displayed fills > 0`. -/
theorem t3_only_after_t2 (L fuel Qs : Nat) (R H : List Nat) (x : Nat)
    (h : 0 < (rule737full L fuel Qs R H x).2.2.1.sum) :
    0 < x - min Qs x - (wheel L fuel R (x - min Qs x)).1.sum := by
  simp only [rule737full] at h
  have hs := wheel_sum L fuel R (x - min Qs x)
  have hh := wheel_sum L fuel H (wheel L fuel R (x - min Qs x)).2
  omega

/-- **Observability: hidden-depth lower bound.**  If an execution of `x` shares
    clears the level (leftover 0), then non-displayed fills are at least
    `x − Qs − Σ R`: executed volume in excess of displayed depth is a
    certificate of hidden depth.  Truncated subtraction: the bound is
    informative only when `Qs + R.sum < x`; otherwise the left side is 0. -/
theorem hidden_depth_lower_bound (L fuel Qs : Nat) (R H : List Nat) (x : Nat)
    (hclear : (rule737full L fuel Qs R H x).2.2.2 = 0) :
    x - Qs - R.sum ≤ (rule737full L fuel Qs R H x).2.2.1.sum := by
  have hsum := rule737full_sum L fuel Qs R H x
  simp only at hsum
  have hcap := Pw_le_sum (wheel_cap L fuel R (x - min Qs x))
  simp only [rule737full] at hsum hclear ⊢
  have := Nat.min_le_left Qs x
  omega

/-- **Observability: parity-count fingerprint.**  In an un-truncated pass in
    which every participant has at least one round lot remaining, the fill
    vector is exactly `replicate m L`: counting the equal round-lot prints in
    one pass identifies the number of parity participants `m`. -/
theorem parity_count_fingerprint (L : Nat) (R : List Nat) (x : Nat)
    (hfull : 0 < (wheelRound L R x).2) (hlot : ∀ r ∈ R, L ≤ r) :
    (wheelRound L R x).1 = List.replicate R.length L := by
  rw [wheelRound_full L R x hfull]
  clear hfull
  induction R with
  | nil => rfl
  | cons r R ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      rw [Nat.min_eq_left (hlot r (List.mem_cons_self ..))]
      rw [ih (fun r' h' => hlot r' (List.mem_cons_of_mem r h'))]

/-! ## DMM parity share dilution -/

/-- With `u` parity units at a level split equally among `m` participants
    (m ≥ 1), the DMM's parity share `u / m` is non-increasing in `m`
    (Prop. dmmshare: floor-broker proliferation dilutes the DMM). -/
theorem dmm_share_antitone (u m : Nat) (hm : 0 < m) : u / (m + 1) ≤ u / m :=
  Nat.div_le_div_left (Nat.le_succ m) hm

/-! ## Opening / closing crosses (NASDAQ) and NYSE auctions -/

/-- Orders are (limit price, size). Demand at `p`: bids with limit ≥ p.
    Supply at `p`: asks with limit ≤ p. -/
def demandAt (bids : List (Nat × Nat)) (p : Nat) : Nat :=
  (bids.filter (fun o => p ≤ o.1)).map (·.2) |>.sum
def supplyAt (asks : List (Nat × Nat)) (p : Nat) : Nat :=
  (asks.filter (fun o => o.1 ≤ p)).map (·.2) |>.sum
/-- Executable volume at a uniform price `p`. -/
def matchedAt (bids asks : List (Nat × Nat)) (p : Nat) : Nat :=
  min (demandAt bids p) (supplyAt asks p)
/-- Imbalance at `p` (signed as a pair: buy-side excess, sell-side excess). -/
def imbalanceAt (bids asks : List (Nat × Nat)) (p : Nat) : Nat × Nat :=
  (demandAt bids p - supplyAt asks p, supplyAt asks p - demandAt bids p)

theorem filter_sum_mono {α} (l : List (α × Nat)) (P Q : α × Nat → Bool)
    (h : ∀ o, P o = true → Q o = true) :
    ((l.filter P).map (·.2)).sum ≤ ((l.filter Q).map (·.2)).sum := by
  induction l with
  | nil => simp
  | cons o l ih =>
      simp only [List.filter_cons]
      by_cases hp : P o = true
      · rw [if_pos hp, if_pos (h o hp)]; simp only [List.map_cons, List.sum_cons]; omega
      · rw [if_neg hp]
        by_cases hq : Q o = true
        · rw [if_pos hq]; simp only [List.map_cons, List.sum_cons]; omega
        · rw [if_neg hq]; exact ih

/-- Demand is non-increasing in price. -/
theorem demandAt_antitone (bids : List (Nat × Nat)) {p q : Nat} (h : p ≤ q) :
    demandAt bids q ≤ demandAt bids p :=
  filter_sum_mono bids _ _ (by intro o ho; simp at ho ⊢; omega)

/-- Supply is non-decreasing in price. -/
theorem supplyAt_mono (asks : List (Nat × Nat)) {p q : Nat} (h : p ≤ q) :
    supplyAt asks p ≤ supplyAt asks q :=
  filter_sum_mono asks _ _ (by intro o ho; simp at ho ⊢; omega)

/-- Cross price: the candidate price maximizing matched volume
    (ties → the first candidate, i.e. the lowest price in the list order). -/
def crossPrice (bids asks : List (Nat × Nat)) (cands : List Nat) : Nat :=
  cands.foldl (fun best p =>
    if matchedAt bids asks best < matchedAt bids asks p then p else best) (cands.headD 0)

theorem foldl_argmax_mono (f : Nat → Nat) (cs : List Nat) (v : Nat) :
    ∀ b, v ≤ f b → v ≤ f (cs.foldl (fun best p => if f best < f p then p else best) b) := by
  induction cs with
  | nil => intro b h; simpa
  | cons d ds ihd =>
      intro b h
      simp only [List.foldl_cons]
      apply ihd
      split <;> omega

theorem foldl_argmax_ge (f : Nat → Nat) (cands : List Nat) (b : Nat) :
    ∀ p ∈ cands, f p ≤ f (cands.foldl (fun best p => if f best < f p then p else best) b) := by
  induction cands generalizing b with
  | nil => intro p h; simp at h
  | cons c cs ih =>
      intro p hp
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hp with rfl | hp'
      · apply foldl_argmax_mono
        split <;> omega
      · exact ih _ p hp'

/-- The cross price maximizes matched volume over the candidate set
    (Rule 4752/4754 maximum-executable-volume principle). -/
theorem crossPrice_maximizes (bids asks : List (Nat × Nat)) (cands : List Nat) :
    ∀ p ∈ cands, matchedAt bids asks p ≤ matchedAt bids asks (crossPrice bids asks cands) :=
  foldl_argmax_ge (matchedAt bids asks) cands _

/-- Worked cross: bids (price, size) and asks in cents. -/
def exBids : List (Nat × Nat) := [(1002, 500), (1001, 300), (1000, 400), (999, 200)]
def exAsks : List (Nat × Nat) := [(998, 300), (1000, 300), (1001, 400), (1003, 500)]
theorem ex_cross :
    crossPrice exBids exAsks [998, 999, 1000, 1001, 1002, 1003] = 1001 ∧
    matchedAt exBids exAsks 1001 = 800 ∧ imbalanceAt exBids exAsks 1001 = (0, 200) ∧
    matchedAt exBids exAsks 1000 = 600 ∧ matchedAt exBids exAsks 1002 = 500 := by decide

/-! ## Reg NMS: Rules 610, 611, 612 -/

/-- Prices in units of $0.0001. -/
def dollar : Nat := 10000
def penny : Nat := 100
/-- Rule 612: quotations ≥ $1.00 must be priced in $0.01 increments;
    below $1.00 the minimum increment is $0.0001. -/
def rule612 (p : Nat) : Prop := dollar ≤ p → p % penny = 0
/-- Rule 610(d): a protected quote may not lock or cross the market. -/
def notLockedOrCrossed (nbb nbo : Nat) : Prop := nbb < nbo
/-- Rule 611: an execution at `px` on the buy side trades through if it is
    worse than (above) the protected NBO. -/
def tradeThroughBuy (px nbo : Nat) : Prop := nbo < px

/-- Effective tick: tick compliance plus no lock/cross forces the quoted
    spread to be at least one full cent for stocks at or above $1. -/
theorem effective_tick (nbb nbo : Nat) (h1 : rule612 nbb) (h2 : rule612 nbo)
    (hd : dollar ≤ nbb) (hlc : notLockedOrCrossed nbb nbo) : penny ≤ nbo - nbb := by
  unfold rule612 notLockedOrCrossed at *
  have hb := h1 hd
  have ho := h2 (Nat.le_trans hd (Nat.le_of_lt hlc))
  simp only [penny] at *
  omega

/-- Relative (effective) tick `penny / price` is non-increasing in price:
    high-priced stocks are effectively finer-grained (Rule 612 binds low prices). -/
theorem relative_tick_antitone (p : Nat) (hp : 0 < p) :
    (penny * dollar) / (p + 1) ≤ (penny * dollar) / p :=
  Nat.div_le_div_left (Nat.le_succ p) hp

/-- Routing to the protected NBO never trades through. -/
theorem route_to_nbo_no_trade_through (nbo : Nat) : ¬ tradeThroughBuy nbo nbo :=
  Nat.lt_irrefl _

/-- A marketable buy executed at `px ≤ nbo` is Rule 611 compliant. -/
theorem compliant_of_le (px nbo : Nat) (h : px ≤ nbo) : ¬ tradeThroughBuy px nbo :=
  Nat.not_lt.mpr h

/-! ## Two market-data clocks: SIP vs direct feeds -/

/-- An event has a venue (matching-engine) timestamp and a SIP timestamp
    `venue + latency`. -/
structure Ev where
  venue : Nat
  lat : Nat
def Ev.sip (e : Ev) : Nat := e.venue + e.lat

/-- The SIP clock never precedes the venue clock. -/
theorem sip_ge_venue (e : Ev) : e.venue ≤ e.sip := Nat.le_add_right _ _

/-- Order preservation: with equal latencies the SIP event order and the direct
    feed agree on event order. -/
theorem sip_order_preserved (e f : Ev) (h : e.lat = f.lat) (hv : e.venue < f.venue) :
    e.sip < f.sip := by unfold Ev.sip; omega

/-- Order inversion: unequal latencies can invert order in SIP timestamps
    (a later venue event printing first) — the two-clock ambiguity. -/
theorem sip_order_inversion_exists :
    ∃ e f : Ev, e.venue < f.venue ∧ f.sip < e.sip :=
  ⟨⟨100, 50⟩, ⟨120, 10⟩, by decide, by decide⟩

/-- Inversion needs latency difference exceeding the venue gap. -/
theorem sip_inversion_bound (e f : Ev) (hv : e.venue < f.venue) (hinv : f.sip < e.sip) :
    f.venue - e.venue < e.lat - f.lat := by unfold Ev.sip at hinv; omega

/-! ## Venue fee game: routing to the cheapest net price -/

/-- Net cost of taking at venue `v`: price plus take fee (rebate modeled
    as a lower fee).  Router picks the minimum over venues. -/
def netCost (px fee : Nat) : Nat := px + fee
def bestVenue (vs : List (Nat × Nat)) : Nat :=
  vs.foldl (fun best v => min best (netCost v.1 v.2)) (netCost (vs.headD (0,0)).1 (vs.headD (0,0)).2)

theorem foldl_min_le_init (g : Nat × Nat → Nat) (l : List (Nat × Nat)) :
    ∀ b, l.foldl (fun best v => min best (g v)) b ≤ b := by
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons w ws ih =>
      intro b
      simp only [List.foldl_cons]
      exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

theorem foldl_min_le_mem (g : Nat × Nat → Nat) (l : List (Nat × Nat)) :
    ∀ b, ∀ v ∈ l, l.foldl (fun best v => min best (g v)) b ≤ g v := by
  induction l with
  | nil => intro b v h; simp at h
  | cons w ws ih =>
      intro b v hv
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Nat.le_trans (foldl_min_le_init g ws _) (Nat.min_le_right _ _)
      · exact ih _ v hv'

/-- The router's chosen net cost is no worse than any venue's
    (fragmented-equilibrium routing condition). -/
theorem bestVenue_le (vs : List (Nat × Nat)) :
    ∀ v ∈ vs, bestVenue vs ≤ netCost v.1 v.2 :=
  foldl_min_le_mem (fun v => netCost v.1 v.2) vs _

/-! ### Candidate sufficiency for the cross

`crossPrice` maximizes over a supplied candidate list.  The next results show
that restricting the candidates to the ask limit prices loses nothing:
`matchedAt` is piecewise constant between ask prices and antitone in demand,
so every price is dominated by the largest ask price at or below it. -/

/-- Largest ask limit price at or below `p`, if any. -/
def maxAskLE (asks : List (Nat × Nat)) (p : Nat) : Option Nat :=
  asks.foldl (fun acc o => if o.1 ≤ p then
      (match acc with | none => some o.1 | some b => some (max b o.1)) else acc) none

private def fm (p : Nat) (asks : List (Nat × Nat)) (acc : Option Nat) : Option Nat :=
  asks.foldl (fun acc o => if o.1 ≤ p then
      (match acc with | none => some o.1 | some b => some (max b o.1)) else acc) acc

theorem fm_some (p : Nat) (asks : List (Nat × Nat)) :
    ∀ b, ∃ c, fm p asks (some b) = some c ∧ b ≤ c := by
  induction asks with
  | nil => intro b; exact ⟨b, rfl, Nat.le_refl _⟩
  | cons o os ih =>
      intro b
      simp only [fm, List.foldl_cons]
      by_cases h : o.1 ≤ p
      · simp only [h, if_true]
        obtain ⟨c, hc, hbc⟩ := ih (max b o.1)
        exact ⟨c, hc, Nat.le_trans (Nat.le_max_left _ _) hbc⟩
      · simp only [h, if_false]; exact ih b

theorem fm_none (p : Nat) (asks : List (Nat × Nat)) :
    ∀ acc, fm p asks acc = none → acc = none ∧ ∀ o ∈ asks, ¬ o.1 ≤ p := by
  induction asks with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons o os ih =>
      intro acc h
      simp only [fm, List.foldl_cons] at h
      by_cases ho : o.1 ≤ p
      · simp only [ho, if_true] at h
        exfalso
        cases acc with
        | none => obtain ⟨c, hc, _⟩ := fm_some p os o.1; simp [fm] at hc; simp_all
        | some b => obtain ⟨c, hc, _⟩ := fm_some p os (max b o.1); simp [fm] at hc; simp_all
      · simp only [ho, if_false] at h
        obtain ⟨h1, h2⟩ := ih acc h
        refine ⟨h1, ?_⟩
        intro o' ho'
        simp only [List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · exact ho
        · exact h2 o' ho'

theorem fm_mem (p : Nat) (asks : List (Nat × Nat)) :
    ∀ acc c, fm p asks acc = some c → acc = some c ∨ (c ≤ p ∧ ∃ o ∈ asks, o.1 = c) := by
  induction asks with
  | nil => intro acc c h; left; exact h
  | cons o os ih =>
      intro acc c h
      simp only [fm, List.foldl_cons] at h
      by_cases ho : o.1 ≤ p
      · simp only [ho, if_true] at h
        cases acc with
        | none =>
            rcases ih _ _ h with h' | ⟨hc, o', ho', rfl⟩
            · right; cases h'; exact ⟨ho, o, List.mem_cons_self .., rfl⟩
            · right; exact ⟨hc, o', List.mem_cons_of_mem _ ho', rfl⟩
        | some b =>
            rcases ih _ _ h with h' | ⟨hc, o', ho', rfl⟩
            · cases h'
              rcases Nat.le_total b o.1 with hb | hb
              · rw [Nat.max_eq_right hb]; right; exact ⟨ho, o, List.mem_cons_self .., rfl⟩
              · rw [Nat.max_eq_left hb]; left; rfl
            · right; exact ⟨hc, o', List.mem_cons_of_mem _ ho', rfl⟩
      · simp only [ho, if_false] at h
        rcases ih _ _ h with h' | ⟨hc, o', ho', rfl⟩
        · left; exact h'
        · right; exact ⟨hc, o', List.mem_cons_of_mem _ ho', rfl⟩

theorem fm_ub (p : Nat) (asks : List (Nat × Nat)) :
    ∀ acc c, fm p asks acc = some c → ∀ o ∈ asks, o.1 ≤ p → o.1 ≤ c := by
  induction asks with
  | nil => intro acc c _ o ho; simp at ho
  | cons o os ih =>
      intro acc c h o' ho' hp'
      simp only [fm, List.foldl_cons] at h
      simp only [List.mem_cons] at ho'
      by_cases ho : o.1 ≤ p
      · simp only [ho, if_true] at h
        rcases ho' with rfl | ho'
        · cases acc with
          | none =>
              obtain ⟨c', hc', hle⟩ := fm_some p os o'.1
              simp only [fm] at hc'; rw [hc'] at h; cases h; exact hle
          | some b =>
              obtain ⟨c', hc', hle⟩ := fm_some p os (max b o'.1)
              simp only [fm] at hc'; rw [hc'] at h; cases h
              exact Nat.le_trans (Nat.le_max_right _ _) hle
        · exact ih _ _ h o' ho' hp'
      · simp only [ho, if_false] at h
        rcases ho' with rfl | ho'
        · exact absurd hp' ho
        · exact ih _ _ h o' ho' hp'

theorem supplyAt_zero_of_none (asks : List (Nat × Nat)) (p : Nat)
    (h : ∀ o ∈ asks, ¬ o.1 ≤ p) : supplyAt asks p = 0 := by
  unfold supplyAt
  have : asks.filter (fun o => o.1 ≤ p) = [] := by
    rw [List.filter_eq_nil_iff]; intro o ho; simpa using h o ho
  rw [this]; rfl

theorem supplyAt_eq_of_ub (asks : List (Nat × Nat)) (p c : Nat) (hc : c ≤ p)
    (hub : ∀ o ∈ asks, o.1 ≤ p → o.1 ≤ c) : supplyAt asks c = supplyAt asks p := by
  unfold supplyAt
  congr 2
  apply List.filter_congr
  intro o ho
  have h1 : o.1 ≤ c → o.1 ≤ p := fun h => Nat.le_trans h hc
  have h2 := hub o ho
  by_cases h : o.1 ≤ p
  · simp [h, h2 h]
  · have : ¬ o.1 ≤ c := fun h' => h (h1 h')
    simp [h, this]

/-- **Candidate sufficiency.**  Every price is dominated in matched volume by
    some ask limit price at or below it, or matches nothing at all. -/
theorem matched_dominated_by_ask_price (bids asks : List (Nat × Nat)) (p : Nat) :
    matchedAt bids asks p = 0 ∨
    ∃ c, c ≤ p ∧ (∃ o ∈ asks, o.1 = c) ∧ matchedAt bids asks p ≤ matchedAt bids asks c := by
  cases hm : maxAskLE asks p with
  | none =>
      left
      have := (fm_none p asks none hm).2
      unfold matchedAt; rw [supplyAt_zero_of_none asks p this]; simp
  | some c =>
      right
      rcases fm_mem p asks none c hm with h | ⟨hc, hmem⟩
      · cases h
      refine ⟨c, hc, hmem, ?_⟩
      have hub := fm_ub p asks none c hm
      unfold matchedAt
      rw [supplyAt_eq_of_ub asks p c hc hub]
      have := demandAt_antitone bids hc
      omega

/-- **The cross over ask prices is a global maximum.**  With the candidate list
    equal to the ask limit prices, `crossPrice` maximizes matched volume over
    every price, not only over the candidates. -/
theorem crossPrice_global (bids asks : List (Nat × Nat)) (p : Nat) :
    matchedAt bids asks p ≤ matchedAt bids asks (crossPrice bids asks (asks.map (·.1))) := by
  rcases matched_dominated_by_ask_price bids asks p with h | ⟨c, _, ⟨o, ho, rfl⟩, hle⟩
  · rw [h]; exact Nat.zero_le _
  · exact Nat.le_trans hle (crossPrice_maximizes bids asks _ _ (List.mem_map_of_mem ho))

end Rule737
