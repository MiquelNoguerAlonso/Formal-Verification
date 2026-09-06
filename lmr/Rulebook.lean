/-
  Rulebook.lean — rulebook-scale layer: multi-level price–time book matching
  with price priority (Nasdaq 4757), limit-order marketability, NBBO
  formation from protected round-lot quotes across venues (Reg NMS 600),
  Rule 611 with the ISO exception (sweep-then-execute), Rule 610(d) price
  sliding, uniqueness characterization of price–time, and a decidable
  conformance checker for queue-aligned allocation records. Lean 4.22.0, core only.
-/
import Rule737
import Markets
namespace Rule737

/-! ## Characterization: price–time is the unique feasible serial allocation -/

/-- Feasible: capped by sizes and allocates min(x, total). -/
def Feasible (Q A : List Nat) (x : Nat) : Prop :=
  Pw (fun a q => a ≤ q) A Q ∧ A.sum = min x Q.sum

/-- Serial: if anything behind position i is filled, position i is filled in full. -/
def Serial : List Nat → List Nat → Prop
  | [], [] => True
  | a :: A, q :: Q => (0 < A.sum → a = q) ∧ Serial A Q
  | _, _ => False

theorem priceTime_feasible (Q : List Nat) (x : Nat) : Feasible Q (priceTime Q x) x := by
  refine ⟨priceTime_cap Q x, ?_⟩
  induction Q generalizing x with
  | nil => simp [priceTime]
  | cons q Q ih =>
      simp only [priceTime, List.sum_cons]
      rw [ih (x - min q x)]
      omega

theorem priceTime_serial' (Q : List Nat) (x : Nat) : Serial (priceTime Q x) Q := by
  induction Q generalizing x with
  | nil => trivial
  | cons q Q ih =>
      simp only [priceTime, Serial]
      exact ⟨priceTime_serial q Q x, ih _⟩

/-- **Uniqueness.**  Any feasible serial allocation equals price–time. -/
theorem serial_unique (Q A : List Nat) (x : Nat)
    (hf : Feasible Q A x) (hs : Serial A Q) : A = priceTime Q x := by
  induction Q generalizing A x with
  | nil =>
      cases A with
      | nil => rfl
      | cons a A => exact absurd hs (by simp [Serial])
  | cons q Q ih =>
      cases A with
      | nil => exact absurd hs (by simp [Serial])
      | cons a A =>
          simp only [Serial] at hs
          obtain ⟨hcap, hsum⟩ := hf
          cases hcap with
          | cons haq hAQ =>
              simp only [List.sum_cons] at hsum
              simp only [priceTime]
              have hAle : A.sum ≤ Q.sum := Pw_le_sum hAQ
              -- head
              have hhead : a = min q x := by
                by_cases hpos : 0 < A.sum
                · have := hs.1 hpos
                  have : q ≤ x := by omega
                  rw [Nat.min_eq_left this]; omega
                · have hz : A.sum = 0 := by omega
                  rw [hz] at hsum
                  by_cases hqx : q ≤ x
                  · rw [Nat.min_eq_left hqx]; omega
                  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hqx))]; omega
              rw [hhead]
              congr
              apply ih A (x - min q x) ⟨hAQ, ?_⟩ hs.2
              rw [hhead] at hsum
              omega

/-- **Decidable conformance.** A queue-aligned fill vector conforms to price–time iff it
    equals the engine output; by uniqueness this is iff it is feasible and serial. -/
def conformsPT (Q prints : List Nat) (x : Nat) : Bool := prints == priceTime Q x

theorem conformsPT_iff (Q prints : List Nat) (x : Nat) :
    conformsPT Q prints x = true ↔ (Feasible Q prints x ∧ Serial prints Q) := by
  unfold conformsPT
  constructor
  · intro h
    have : prints = priceTime Q x := by simpa using h
    rw [this]; exact ⟨priceTime_feasible Q x, priceTime_serial' Q x⟩
  · intro ⟨hf, hs⟩
    have := serial_unique Q prints x hf hs
    simpa using this

/-! ## Multi-level book: price priority, then time priority -/

/-- An ask ladder: levels (price, queue in arrival order), ascending price.
    A marketable buy of `x` walks levels while `price ≤ limit`. -/
def matchAsks (limit : Nat) : List (Nat × List Nat) → Nat → List (Nat × List Nat) × Nat
  | [], x => ([], x)
  | (p, q) :: rest, x =>
      if p ≤ limit then
        let f := priceTime q x
        let r := matchAsks limit rest (x - f.sum)
        ((p, f) :: r.1, r.2)
      else ((p, q.map (fun _ => 0)) :: (rest.map (fun l => (l.1, l.2.map (fun _ => 0)))), x)

theorem zeroed_levels_sum (rest : List (Nat × List Nat)) :
    ((rest.map (fun l => (l.1, l.2.map (fun _ => (0:Nat))))).map (fun l => l.2.sum)).sum = 0 := by
  induction rest with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, map_zero_sum]; simpa using ih

theorem matchAsks_conserve (limit : Nat) (asks : List (Nat × List Nat)) (x : Nat) :
    ((matchAsks limit asks x).1.map (fun l => l.2.sum)).sum + (matchAsks limit asks x).2 = x := by
  induction asks generalizing x with
  | nil => simp [matchAsks]
  | cons l rest ih =>
      obtain ⟨p, q⟩ := l
      simp only [matchAsks]
      split
      · simp only [List.map_cons, List.sum_cons]
        have h1 := priceTime_sum_le q x
        have h2 := ih (x - (priceTime q x).sum)
        omega
      · simp only [List.map_cons, List.sum_cons, map_zero_sum, zeroed_levels_sum]; omega

/-- **Price priority.**  If any deeper level receives a fill, the top level is
    exhausted: its fills equal its queue. -/
theorem price_priority (limit : Nat) (q : List Nat) (rest : List (Nat × List Nat)) (x : Nat)
    (h : 0 < ((matchAsks limit rest (x - (priceTime q x).sum)).1.map (fun l => l.2.sum)).sum) :
    priceTime q x = q := by
  have hc := matchAsks_conserve limit rest (x - (priceTime q x).sum)
  have hle := priceTime_sum_le q x
  have hpos : 0 < x - (priceTime q x).sum := by omega
  -- if x is not exhausted by the top level, every order there is filled in full
  clear h hc hle
  induction q generalizing x with
  | nil => rfl
  | cons a Q ih =>
      simp only [priceTime, List.sum_cons] at hpos ⊢
      have hqx : a ≤ x := by
        by_cases h : a ≤ x
        · exact h
        · exfalso
          rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))] at hpos
          have := priceTime_sum_le Q (x - x)
          omega
      rw [Nat.min_eq_left hqx] at hpos ⊢
      rw [ih (x - a) (by omega)]

/-- Non-marketable levels are never touched: a level above the limit gets zero. -/
theorem no_fill_above_limit (limit p : Nat) (q : List Nat) (rest : List (Nat × List Nat)) (x : Nat)
    (hp : limit < p) :
    (matchAsks limit ((p, q) :: rest) x).2 = x := by
  simp [matchAsks, Nat.not_le.mpr hp]

/-! ## NBBO formation from protected quotes (Reg NMS Rule 600(b)) -/

structure Quote where
  venue : Nat
  price : Nat
  size  : Nat
  auto  : Bool   -- automated (immediately and automatically accessible)

/-- A quote is protected iff it is automated and at least a round lot. -/
def protected_ (L : Nat) (q : Quote) : Bool := q.auto && decide (L ≤ q.size)

def nbo (L : Nat) (asks : List Quote) : Option Nat :=
  (asks.filter (protected_ L)).foldl (fun acc q =>
    match acc with
    | none => some q.price
    | some b => some (min b q.price)) none

theorem foldl_min_opt_mono (rs : List Quote) :
    ∀ (b : Nat) (v : Nat), rs.foldl (fun acc q => match acc with
        | none => some q.price | some b => some (min b q.price)) (some b) = some v → v ≤ b := by
  induction rs with
  | nil => intro b v hv; simp at hv; omega
  | cons s ss ihs =>
      intro b v hv
      simp only [List.foldl_cons] at hv
      exact Nat.le_trans (ihs _ v hv) (Nat.min_le_left _ _)

theorem foldl_min_opt_le (l : List Quote) :
    ∀ acc, ∀ q ∈ l, ∀ v, l.foldl (fun acc q => match acc with
        | none => some q.price | some b => some (min b q.price)) acc = some v → v ≤ q.price := by
  induction l with
  | nil => intro acc q hq; simp at hq
  | cons r rs ih =>
      intro acc q hq v hv
      simp only [List.foldl_cons] at hv
      rcases List.mem_cons.mp hq with rfl | hq'
      · cases acc with
        | none => exact foldl_min_opt_mono rs _ v hv
        | some b => exact Nat.le_trans (foldl_min_opt_mono rs _ v hv) (Nat.min_le_right _ _)
      · exact ih _ q hq' v hv

/-- **NBO is the best protected offer**: no protected ask is below it. -/
theorem nbo_le_protected (L : Nat) (asks : List Quote) (v : Nat) (h : nbo L asks = some v) :
    ∀ q ∈ asks, protected_ L q = true → v ≤ q.price := by
  intro q hq hp
  have hmem : q ∈ asks.filter (protected_ L) := List.mem_filter.mpr ⟨hq, hp⟩
  exact foldl_min_opt_le _ none q hmem v h

/-- Odd lots and manual quotes do not set the NBO (they are filtered out). -/
theorem oddlot_not_protected (L : Nat) (q : Quote) (h : q.size < L) : protected_ L q = false := by
  simp [protected_, Nat.not_le.mpr h]

/-! ## Rule 611 with the intermarket-sweep exception -/

/-- Sweep: send ISOs to every protected quote priced better than `px`
    (filling `min size x` at each in list order), then execute the remainder
    at `px` on the local book.  Returns (fills at away venues, executed at px). -/
def sweepThenExecute (L px : Nat) : List Quote → Nat → List Nat × Nat
  | [], x => ([], x)
  | q :: qs, x =>
      if protected_ L q && decide (q.price < px) then
        let f := min q.size x
        let r := sweepThenExecute L px qs (x - f)
        (f :: r.1, r.2)
      else
        let r := sweepThenExecute L px qs x
        (0 :: r.1, r.2)

theorem sweep_conserve (L px : Nat) (qs : List Quote) (x : Nat) :
    (sweepThenExecute L px qs x).1.sum + (sweepThenExecute L px qs x).2 = x := by
  induction qs generalizing x with
  | nil => simp [sweepThenExecute]
  | cons q qs ih =>
      simp only [sweepThenExecute]
      split
      · simp only [List.sum_cons]; have := ih (x - min q.size x); have := Nat.min_le_right q.size x; omega
      · simp only [List.sum_cons]; have := ih x; omega

/-- **ISO compliance.**  If quantity is executed at `px` (leftover > 0), then every
    protected quote better than `px` received an ISO for its full size. -/
theorem iso_compliance (L px : Nat) (qs : List Quote) (x : Nat)
    (h : 0 < (sweepThenExecute L px qs x).2) :
    Pw (fun f s => f = s)
      (sweepThenExecute L px qs x).1
      (qs.map (fun q => if protected_ L q && decide (q.price < px) then q.size else 0)) := by
  induction qs generalizing x with
  | nil => exact Pw.nil
  | cons q qs ih =>
      simp only [sweepThenExecute, List.map_cons] at h ⊢
      split
      · rename_i hc
        simp only [hc, if_true] at h ⊢
        have hc2 := sweep_conserve L px qs (x - min q.size x)
        have hpos : 0 < x - min q.size x := by omega
        have hm : min q.size x = q.size := by
          by_cases hs : q.size ≤ x
          · exact Nat.min_eq_left hs
          · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hs))] at hpos; omega
        exact Pw.cons hm (ih _ h)
      · rename_i hc
        simp only [hc] at h ⊢
        exact Pw.cons rfl (ih _ h)

/-! ## Rule 610(d): price sliding -/

/-- A buy limit that would lock or cross the NBO is displayed one tick below it. -/
def slideBuy (tick limit nbo : Nat) : Nat := if nbo ≤ limit then nbo - tick else limit

theorem slide_no_lock (tick limit nbo : Nat) (ht : 0 < tick) (hn : tick ≤ nbo) :
    slideBuy tick limit nbo < nbo := by
  unfold slideBuy; split <;> omega

theorem slide_le_limit (tick limit nbo : Nat) : slideBuy tick limit nbo ≤ limit := by
  unfold slideBuy; split <;> omega

/-! ## Worked book -/

def exAsksBook : List (Nat × List Nat) := [(1000, [200, 300]), (1001, [400]), (1003, [500])]
theorem ex_book :
    matchAsks 1001 exAsksBook 700 = ([(1000, [200, 300]), (1001, [200]), (1003, [0])], 0) ∧
    matchAsks 1000 exAsksBook 700 = ([(1000, [200, 300]), (1001, [0]), (1003, [0])], 200) := by
  decide

def exQuotes : List Quote :=
  [⟨1, 1002, 300, true⟩, ⟨2, 1001, 50, true⟩, ⟨3, 1001, 200, false⟩, ⟨4, 1003, 500, true⟩]
theorem ex_nbo : nbo 100 exQuotes = some 1002 := by decide
theorem ex_sweep : sweepThenExecute 100 1003 exQuotes 1000 = ([300, 0, 0, 0], 700) := by decide

end Rule737
