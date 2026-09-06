import PathIndependence

namespace Rule737

/-- Total cumulative allocation under one participant label.  Valid labelled
    books have unique labels; summing also makes the definition total. -/
def allocatedList (id : Nat) (S : List (Nat × Nat × Nat)) : Nat :=
  (S.map (fun p => if p.1 = id then p.2.1 else 0)).sum

def allocatedW (id : Nat) (st : WState) : Nat := allocatedList id st.S

/-- New, label-aligned fill in a canonical execution. -/
def nextWFill (L : Nat) (st : WState) (x id : Nat) : Nat :=
  allocatedW id (runWFull L st x).1 - allocatedW id st

theorem allocatedList_append (id : Nat) (S T : List (Nat × Nat × Nat)) :
    allocatedList id (S ++ T) = allocatedList id S + allocatedList id T := by
  induction S with
  | nil => simp [allocatedList]
  | cons p S ih =>
    simp only [List.cons_append, allocatedList, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem runWFull_consuming_step (L : Nat) (st : WState) (x : Nat)
    (hx : 0 < x) (ht : 0 < totW st.S) (hg : (stepW L st x).2 = x) :
    runWFull L st x = ((stepW L st x).1, 0) := by
  unfold runWFull
  simp only [runW]
  rw [if_neg (by omega), hg, Nat.sub_self, runW_x0]

theorem runWFull_partial_head (L a id A r x : Nat)
    (T : List (Nat × Nat × Nat)) (hxa : x < a) (hxr : x < r) :
    runWFull L ⟨(id, A, r) :: T, a⟩ x =
      (⟨(id, A + x, r - x) :: T, a - x⟩, 0) := by
  by_cases hx : x = 0
  · subst x
    simp [runWFull, runW_x0]
  · have hf : findLive ((id, A, r) :: T) = (id, A, r) :: T :=
      findLive_of_live _ _ (by simp [live]; omega)
    have he := stepW_partial L ⟨(id, A, r) :: T, a⟩ id A r T x hf (by simp; omega)
    rw [runWFull_consuming_step L _ x (by omega)
      (by simp [totW]; omega) (by rw [he])]
    rw [he]

theorem runWFull_advance_head (L a id A r : Nat)
    (T : List (Nat × Nat × Nat)) (ha : 0 < a) (har : a ≤ r) :
    runWFull L ⟨(id, A, r) :: T, a⟩ a =
      (⟨T ++ [(id, A + a, r - a)], L⟩, 0) := by
  have hf : findLive ((id, A, r) :: T) = (id, A, r) :: T :=
    findLive_of_live _ _ (by simp [live]; omega)
  have he := stepW_adv L ⟨(id, A, r) :: T, a⟩ id A r T a hf (Nat.min_le_left _ _)
  simp only [Nat.min_eq_left har] at he
  rw [runWFull_consuming_step L _ a ha
    (by simp [totW]; omega) (by rw [he])]
  rw [he]

theorem runWFull_head_allocation (L a id A r x j : Nat)
    (T : List (Nat × Nat × Nat)) (hxa : x ≤ a) (hxr : x < r) :
    allocatedW j (runWFull L ⟨(id, A, r) :: T, a⟩ x).1 =
      allocatedW j ⟨(id, A, r) :: T, a⟩ + (if id = j then x else 0) := by
  by_cases hlt : x < a
  · rw [runWFull_partial_head L a id A r x T hlt hxr]
    simp only [allocatedW, allocatedList, List.map_cons, List.sum_cons]
    split <;> omega
  · have hax : a = x := by omega
    subst a
    by_cases hx : x = 0
    · subst x
      simp [runWFull, runW_x0]
    · rw [runWFull_advance_head L x id A r T (by omega) (by omega)]
      simp only [allocatedW, allocatedList_append]
      simp only [allocatedList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      split <;> omega

theorem nextWFill_head (L a id A r x j : Nat)
    (T : List (Nat × Nat × Nat)) (hxa : x ≤ a) (hxr : x < r) :
    nextWFill L ⟨(id, A, r) :: T, a⟩ x j = if id = j then x else 0 := by
  unfold nextWFill
  rw [runWFull_head_allocation L a id A r x j T hxa hxr]
  omega

/-- A finite probe crosses the current lot boundary and gives its next unit
    to the successor.  Both claims exceed the probe horizon. -/
theorem nextWFill_crosses_allowance (L a p A r q B s : Nat)
    (T : List (Nat × Nat × Nat)) (hL : 0 < L) (ha : 0 < a)
    (har : a < r) (hs : 1 < s) (hpq : p ≠ q) :
    nextWFill L ⟨(p, A, r) :: (q, B, s) :: T, a⟩ (a + 1) p = a := by
  let st : WState := ⟨(p, A, r) :: (q, B, s) :: T, a⟩
  have hfirst := runWFull_advance_head L a p A r ((q, B, s) :: T) ha (by omega)
  have hc := runWFull_comp L st a 1 hL ha (by dsimp [st]; simp [totW]; omega)
  change nextWFill L st (a + 1) p = a
  unfold nextWFill
  rw [hc]
  change allocatedW p (runWFull L (runWFull L
    ⟨(p, A, r) :: (q, B, s) :: T, a⟩ a).1 1).1 - allocatedW p st = a
  rw [hfirst]
  simp only [List.cons_append]
  rw [runWFull_head_allocation L L q B s 1 p (T ++ [(p, A + a, r - a)])
    (by omega) hs]
  have hqp : q ≠ p := Ne.symm hpq
  simp only [hqp, if_false, Nat.add_zero, allocatedW, st, allocatedList,
    List.map_cons, List.sum_cons, ite_true]
  have he := allocatedList_append p T [(p, A + a, r - a)]
  simp only [allocatedList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ite_true, Nat.add_zero] at he
  omega

/-- Fixed cyclic continuation after the first two labels. -/
def phaseRest (m L p : Nat) : List (Nat × Nat × Nat) :=
  (List.range (m - 2)).map (fun k => ((p + k + 2) % m, 0, 2 * L + 1))

def phaseTail (m L p : Nat) : List (Nat × Nat × Nat) :=
  ((p + 1) % m, 0, 2 * L + 1) :: phaseRest m L p

/-- Finite, reachable phase family.  Every original claim is `2*L+1`;
    the current participant has already received `L-a` units. -/
def phaseState (m L p a : Nat) : WState :=
  ⟨(p, L - a, L + 1 + a) :: phaseTail m L p, a⟩

theorem phaseState_length (m L p a : Nat) (hm : 2 ≤ m) :
    (phaseState m L p a).S.length = m := by
  simp [phaseState, phaseTail, phaseRest]
  omega

theorem phaseState_reachable (m L p a : Nat) (ha : 0 < a) (haL : a ≤ L) :
    runWFull L (initW L
      ((p, 2 * L + 1) :: (phaseTail m L p).map (fun v => (v.1, v.2.2))))
      (L - a) = (phaseState m L p a, 0) := by
  have ht : (initW L
      ((p, 2 * L + 1) :: (phaseTail m L p).map (fun v => (v.1, v.2.2)))) =
      ⟨(p, 0, 2 * L + 1) :: phaseTail m L p, L⟩ := by
    simp [initW, phaseTail, phaseRest, List.map_map]
  rw [ht, runWFull_partial_head L L p 0 (2 * L + 1) (L - a)
    (phaseTail m L p) (by omega) (by omega)]
  have hlot : L - (L - a) = a := by omega
  have hr : 2 * L + 1 - (L - a) = L + 1 + a := by omega
  simp [phaseState, hlot, hr]

theorem phaseState_first_fill (m L p a j : Nat) (ha : 0 < a) :
    nextWFill L (phaseState m L p a) 1 j = if p = j then 1 else 0 :=
  nextWFill_head L a p (L - a) (L + 1 + a) 1 j (phaseTail m L p)
    (by omega) (by omega)

theorem phaseState_allowance_probe (m L p a : Nat)
    (hm : 2 ≤ m) (hp : p < m) (ha : 0 < a) (haL : a ≤ L) :
    nextWFill L (phaseState m L p a) (a + 1) p = a := by
  apply nextWFill_crosses_allowance L a p (L - a) (L + 1 + a)
    ((p + 1) % m) 0 (2 * L + 1) (phaseRest m L p)
    (by omega) ha (by omega) (by omega)
  exact Ne.symm (succ_mod_ne_self m p hm hp)

/-- Equivalence uses the actual canonical executable wheel and label-aligned
    new fills, not a separately stipulated owner trace. -/
def WheelFutureEquivalent (L : Nat) (st su : WState) : Prop :=
  ∀ x id, nextWFill L st x id = nextWFill L su x id

/-- Only estates at most one lot are needed for separation. -/
def WheelProbeEquivalent (L : Nat) (st su : WState) : Prop :=
  ∀ x, x ≤ L → ∀ id, nextWFill L st x id = nextWFill L su x id

/-- A nondegenerate wheel phase has a live pointer, a distinct live successor,
    a positive within-lot allowance, and more than one lot remaining at every
    participant.  The final condition is stronger than the separating proof
    needs, but records the natural claim-boundary-free domain. -/
def ValidWheelPhase (L p a : Nat) (st : WState) : Prop :=
  ∃ A r q B s T,
    st = ⟨(p, A, r) :: (q, B, s) :: T, a⟩ ∧
    p ≠ q ∧ 0 < a ∧ a ≤ L ∧ L < r ∧ L < s ∧
    ∀ v ∈ T, L < v.2.2

/-- **General phase separation.**  On any two nondegenerate phase states,
    equality of all probes up to one lot forces equality of the pointer label
    and unused allowance.  The states may have arbitrary accumulated fills,
    claims, successor labels and tails satisfying `ValidWheelPhase`. -/
theorem validWheelPhase_probe_equiv_implies (L p a q b : Nat)
    (st su : WState) (hL : 0 < L)
    (hst : ValidWheelPhase L p a st) (hsu : ValidWheelPhase L q b su)
    (he : WheelProbeEquivalent L st su) :
    p = q ∧ a = b := by
  obtain ⟨A, r, pn, B, s, T, hst, hpn, ha, haL, hr, hs, _⟩ := hst
  obtain ⟨C, u, qn, D, v, U, hsu, hqn, hb, hbL, hu, hv, _⟩ := hsu
  subst st
  subst su
  have hfirst := he 1 (by omega) p
  rw [nextWFill_head L a p A r 1 p ((pn, B, s) :: T) (by omega) (by omega),
      nextWFill_head L b q C u 1 p ((qn, D, v) :: U) (by omega) (by omega)] at hfirst
  have hpq : p = q := by
    apply Classical.byContradiction
    intro hpq
    have hqp : q ≠ p := Ne.symm hpq
    simp [hqp] at hfirst
  subst q
  refine ⟨rfl, ?_⟩
  apply Classical.byContradiction
  intro hab
  rcases Nat.lt_or_gt_of_ne hab with hab | hab
  · have hx := he (a + 1) (by omega) p
    rw [nextWFill_crosses_allowance L a p A r pn B s T hL ha
          (by omega) (by omega) hpn,
        nextWFill_head L b p C u (a + 1) p ((qn, D, v) :: U)
          (by omega) (by omega)] at hx
    simp at hx
  · have hx := he (b + 1) (by omega) p
    rw [nextWFill_head L a p A r (b + 1) p ((pn, B, s) :: T)
          (by omega) (by omega),
        nextWFill_crosses_allowance L b p C u qn D v U hL hb
          (by omega) (by omega) hqn] at hx
    simp at hx

/-- A summary is future sufficient on an indexed state family when a single
    decoder, given the authenticated observation, summary, estate, and label,
    returns the actual canonical next fill. -/
def WheelFiberSufficient {α β : Type} (L m : Nat) (family : Nat → WState)
    (observation : WState → β) (summary : WState → α) : Prop :=
  ∃ predict : β → α → Nat → Nat → Nat,
    ∀ p, p < m → ∀ x id,
      predict (observation (family p)) (summary (family p)) x id =
        nextWFill L (family p) x id

/-- The participant at the live head, on the nondegenerate states used below. -/
def wheelPointerCode (st : WState) : Nat :=
  (st.S.headD (0, 0, 0)).1

/-- **Fiberwise necessity of the pointer.**  On any family indexed by distinct
    live-head labels, if every member is a nondegenerate wheel phase and the
    authenticated observation is common to the family, every future-sufficient
    summary is injective in the pointer index.  This is not tied to the concrete
    equal-claim phase family. -/
theorem wheelFiberSufficient_pointer_injective {α β : Type}
    (L m : Nat) (family : Nat → WState) (observation : WState → β)
    (summary : WState → α) (hL : 0 < L)
    (hvalid : ∀ p, p < m → ∃ a, ValidWheelPhase L p a (family p))
    (hobs : ∀ p, p < m → ∀ q, q < m →
      observation (family p) = observation (family q))
    (hs : WheelFiberSufficient L m family observation summary)
    (p q : Nat) (hp : p < m) (hq : q < m)
    (he : summary (family p) = summary (family q)) :
    p = q := by
  obtain ⟨predict, hpredict⟩ := hs
  obtain ⟨a, ha⟩ := hvalid p hp
  obtain ⟨b, hb⟩ := hvalid q hq
  have hprobe : WheelProbeEquivalent L (family p) (family q) := by
    intro x hx id
    rw [← hpredict p hp x id, ← hpredict q hq x id,
      hobs p hp q hq, he]
  exact (validWheelPhase_probe_equiv_implies L p a q b
    (family p) (family q) hL ha hb hprobe).1

/-- **Fiberwise sufficiency of the pointer.**  When the indexed family itself
    is fixed and each state has live head p, the head label is a complete
    predictive code: the decoder reconstructs the indexed state and executes
    the canonical wheel. -/
theorem wheelPointerCode_fiber_sufficient {β : Type}
    (L m : Nat) (family : Nat → WState) (observation : WState → β)
    (hvalid : ∀ p, p < m → ∃ a, ValidWheelPhase L p a (family p)) :
    WheelFiberSufficient L m family observation wheelPointerCode := by
  refine ⟨fun _ p x id => nextWFill L (family p) x id, ?_⟩
  intro p hp x id
  obtain ⟨a, A, r, q, B, s, T, hstate, _⟩ := hvalid p hp
  have hcode : wheelPointerCode (family p) = p := by
    rw [hstate]
    rfl
  rw [hcode]

theorem phaseState_probe_equiv_iff (m L p a q b : Nat)
    (hm : 2 ≤ m) (hp : ValidSaturatedPhase m L p a)
    (hq : ValidSaturatedPhase m L q b) :
    WheelProbeEquivalent L (phaseState m L p a) (phaseState m L q b) ↔
      p = q ∧ a = b := by
  constructor
  · intro he
    have hfirst := he 1 (by have := hp.2; omega) p
    rw [phaseState_first_fill m L p a p hp.2.1,
      phaseState_first_fill m L q b p hq.2.1] at hfirst
    have hpq : p = q := by split at hfirst <;> simp_all
    subst q
    refine ⟨rfl, ?_⟩
    apply Classical.byContradiction
    intro hab
    rcases Nat.lt_or_gt_of_ne hab with hab | hab
    · have hx := he (a + 1) (by have := hq.2; omega) p
      rw [phaseState_allowance_probe m L p a hm hp.1 hp.2.1 hp.2.2] at hx
      have hy := nextWFill_head L b p (L - b) (L + 1 + b) (a + 1) p
        (phaseTail m L p) (by omega) (by omega)
      change nextWFill L (phaseState m L p b) (a + 1) p = _ at hy
      rw [hy] at hx
      simp at hx
    · have hx := he (b + 1) (by have := hp.2; omega) p
      rw [phaseState_allowance_probe m L p b hm hp.1 hq.2.1 hq.2.2] at hx
      have hy := nextWFill_head L a p (L - a) (L + 1 + a) (b + 1) p
        (phaseTail m L p) (by omega) (by omega)
      change nextWFill L (phaseState m L p a) (b + 1) p = _ at hy
      rw [hy] at hx
      simp at hx
  · rintro ⟨rfl, rfl⟩
    intro x hx id
    rfl

theorem phaseState_future_equiv_iff (m L p a q b : Nat)
    (hm : 2 ≤ m) (hp : ValidSaturatedPhase m L p a)
    (hq : ValidSaturatedPhase m L q b) :
    WheelFutureEquivalent L (phaseState m L p a) (phaseState m L q b) ↔
      p = q ∧ a = b := by
  constructor
  · intro h
    exact (phaseState_probe_equiv_iff m L p a q b hm hp hq).mp
      (fun x _ id => h x id)
  · rintro ⟨rfl, rfl⟩
    intro x id
    rfl

/-- No queue or cumulative-fill side information is supplied to this decoder.
    This is a bound on a complete predictive summary of the finite family. -/
def WheelPhaseSufficient {α : Type} (m L : Nat) (summary : WState → α) : Prop :=
  ∃ predict : α → Nat → Nat → Nat,
    ∀ p a, ValidSaturatedPhase m L p a →
      ∀ x id, predict (summary (phaseState m L p a)) x id =
        nextWFill L (phaseState m L p a) x id

def wheelPhaseCode (st : WState) : Nat × Nat :=
  ((st.S.headD (0, 0, 0)).1, st.lot)

theorem wheelPhaseCode_sufficient (m L : Nat) :
    WheelPhaseSufficient m L wheelPhaseCode := by
  refine ⟨fun code x id => nextWFill L (phaseState m L code.1 code.2) x id, ?_⟩
  intro p a hp x id
  rfl

theorem wheelPhaseSufficient_injective {α : Type} (m L : Nat)
    (summary : WState → α) (hm : 2 ≤ m) (hs : WheelPhaseSufficient m L summary)
    (p a q b : Nat) (hp : ValidSaturatedPhase m L p a)
    (hq : ValidSaturatedPhase m L q b)
    (he : summary (phaseState m L p a) = summary (phaseState m L q b)) :
    p = q ∧ a = b := by
  obtain ⟨predict, hpred⟩ := hs
  apply (phaseState_future_equiv_iff m L p a q b hm hp hq).mp
  intro x id
  rw [← hpred p a hp x id, ← hpred q b hq x id, he]

theorem phaseState_capacities (m L p a : Nat) (ha : a ≤ L) :
    ∀ v ∈ (phaseState m L p a).S, v.2.1 + v.2.2 = 2 * L + 1 := by
  intro v hv
  simp only [phaseState, phaseTail, List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · simp; omega
  · simp
  · simp only [phaseRest, List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    simp

theorem phaseState_claims_large (m L p a : Nat) :
    ∀ v ∈ (phaseState m L p a).S, L < v.2.2 := by
  intro v hv
  simp only [phaseState, phaseTail, List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · simp; omega
  · simp; omega
  · simp only [phaseRest, List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    simp; omega

/-- Every indexed phase state is an instance of the general nondegenerate
    phase contract.  The proof records the concrete accumulated fills,
    successor, and tail rather than appealing to computation. -/
theorem phaseState_validWheelPhase (m L p a : Nat)
    (hm : 2 ≤ m) (hp : p < m) (ha : 0 < a) (haL : a ≤ L) :
    ValidWheelPhase L p a (phaseState m L p a) := by
  refine ⟨L - a, L + 1 + a, (p + 1) % m, 0, 2 * L + 1,
    phaseRest m L p, rfl, ?_, ha, haL, by omega, by omega, ?_⟩
  · exact Ne.symm (succ_mod_ne_self m p hm hp)
  · intro v hv
    simp only [phaseRest, List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    simp
    omega

/-- Participant-aligned cumulative allocations, independent of the rotated
    list representation. -/
def alignedAllocationObservation (m : Nat) (st : WState) : List Nat :=
  (List.range m).map (fun id => allocatedW id st)

theorem phaseState_full_allocated_zero (m L p id : Nat) :
    allocatedW id (phaseState m L p L) = 0 := by
  simp [allocatedW, allocatedList, phaseState, phaseTail, phaseRest,
    List.map_map, Function.comp_def, List.map_const']

/-- At a fresh lot boundary, every pointer rotation has the same
    participant-aligned cumulative-allocation observation. -/
theorem phaseState_full_observation (m L p : Nat) :
    alignedAllocationObservation m (phaseState m L p L) =
      List.replicate m 0 := by
  unfold alignedAllocationObservation
  calc
    (List.range m).map (fun id => allocatedW id (phaseState m L p L)) =
        List.replicate (List.range m).length 0 := by
      rw [List.map_eq_replicate_iff]
      intro id _
      exact phaseState_full_allocated_zero m L p id
    _ = List.replicate m 0 := by simp

/-- On the reachable fresh-lot subfamily, the pointer label itself is a
    sufficient predictive code once the family is fixed. -/
theorem phaseState_full_pointer_sufficient (m L : Nat) (hm : 2 ≤ m)
    (hL : 0 < L) :
    WheelFiberSufficient L m (fun p => phaseState m L p L)
      (alignedAllocationObservation m) wheelPointerCode := by
  apply wheelPointerCode_fiber_sufficient
  intro p hp
  exact ⟨L, phaseState_validWheelPhase m L p L hm hp hL (by omega)⟩

/-- **Exact pointer lower bound on a reachable common-observation fiber.**
    Every future-sufficient summary of the fresh-lot phase family must
    distinguish all `m` live pointers, even though participant-aligned
    cumulative allocations are identical.  Together with
    `phaseState_full_pointer_sufficient`, this makes the pointer label an
    exact minimal code on this fiber. -/
theorem phaseState_full_summary_injective {α : Type} (m L : Nat)
    (summary : WState → α) (hm : 2 ≤ m) (hL : 0 < L)
    (hs : WheelFiberSufficient L m (fun p => phaseState m L p L)
      (alignedAllocationObservation m) summary)
    (p q : Nat) (hp : p < m) (hq : q < m)
    (he : summary (phaseState m L p L) =
      summary (phaseState m L q L)) :
    p = q := by
  apply wheelFiberSufficient_pointer_injective L m
    (fun p => phaseState m L p L) (alignedAllocationObservation m)
    summary hL
  · intro j hj
    exact ⟨L, phaseState_validWheelPhase m L j L hm hj hL (by omega)⟩
  · intro i hi j hj
    rw [phaseState_full_observation m L i,
      phaseState_full_observation m L j]
  · exact hs
  · exact hp
  · exact hq
  · exact he

/-- The current lot is derivable when cumulative allocation is known and the
    completed-cycle level is a multiple of L.  This contract distinguishes
    extra hidden metadata from a summary which must carry all predictive data. -/
theorem allowance_from_cumulative (L A a k : Nat) (_hL : 0 < L)
    (ha : 0 < a) (haL : a ≤ L) (hphase : A + a = k * L + L) :
    a = L - A % L := by
  have hm : A % L = L - a := (Nat.mod_eq_sub_iff ha haL).mpr
    ⟨k + 1, by rw [hphase, Nat.mul_succ, Nat.mul_comm L k]⟩
  omega

/-- **Reachable allowance-phase identity.**  Whenever a run from `initW` has a
    live head with cumulative allocation `A`, its current allowance is exactly
    `L - A % L`.  The completed-cycle equation is supplied by the executable
    `AllAtP` invariant, rather than assumed by the caller. -/
theorem runW_allowance_phase (L n : Nat) (R : List (Nat × Nat)) (x A : Nat)
    (T : List Nat) (hL : 0 < L)
    (hhead : liveAllocs (runW L n (initW L R) x).1.S = A :: T) :
    (runW L n (initW L R) x).1.lot = L - A % L := by
  have hreach := runW_atWheelPhase L n (initW L R) x hL
    (initW_atWheelPhase L R)
  obtain ⟨k, hInv⟩ := hreach
  have hphase := hInv.2.2
  rw [hhead] at hphase
  have hpos : 0 < (runW L n (initW L R) x).1.lot :=
    runW_lot_pos L n (initW L R) x hL (by simpa [initW] using hL)
  exact allowance_from_cumulative L A (runW L n (initW L R) x).1.lot k
    hL hpos hInv.1 hphase.1

theorem phaseState_labels (m L p a : Nat) (hm : 2 ≤ m) (hp : p < m) :
    (phaseState m L p a).S.map (·.1) =
      (List.range m).map (fun k => (p + k) % m) := by
  have hrange : List.range m = 0 :: 1 :: (List.range (m - 2)).map (fun k => k + 2) := by
    calc
      List.range m = List.range ((m - 2 + 1) + 1) := congrArg List.range (by omega)
      _ = 0 :: 1 :: (List.range (m - 2)).map (fun k => k + 2) := by
        rw [List.range_succ_eq_map, List.range_succ_eq_map]
        simp [List.map_map, Nat.succ_eq_add_one, Nat.add_assoc]
  rw [hrange]
  simp [phaseState, phaseTail, phaseRest, List.map_map,
    Nat.mod_eq_of_lt hp, Nat.add_assoc]

theorem cyclic_label_injective (m p i j : Nat) (hp : p < m)
    (hi : i < m) (hj : j < m) (he : (p + i) % m = (p + j) % m) : i = j := by
  have hpi : (p + i) % m = if p + i < m then p + i else p + i - m := by
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpj : (p + j) % m = if p + j < m then p + j else p + j - m := by
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hpi, hpj] at he
  split at he <;> split at he <;> omega

theorem phaseState_labels_unique (m L p a : Nat) (hm : 2 ≤ m) (hp : p < m) :
    ((phaseState m L p a).S.map (·.1)).Nodup := by
  rw [phaseState_labels m L p a hm hp]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  intro he
  have := cyclic_label_injective m p i j hp hi hj he
  omega

/-- Relabel identifiers while preserving claims, accumulated fills and order. -/
def relabelRecords (f : Nat → Nat) (S : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) := S.map (fun p => (f p.1, p.2.1, p.2.2))

def relabelW (f : Nat → Nat) (st : WState) : WState :=
  ⟨relabelRecords f st.S, st.lot⟩

theorem splitLive_relabel (f : Nat → Nat) (S : List (Nat × Nat × Nat)) :
    splitLive (relabelRecords f S) =
      (relabelRecords f (splitLive S).1, relabelRecords f (splitLive S).2) := by
  induction S with
  | nil => rfl
  | cons p T ih =>
    rcases p with ⟨id, A, r⟩
    simp only [relabelRecords, List.map_cons, splitLive, live] at ih ⊢
    split <;> simp_all

theorem findLive_relabel (f : Nat → Nat) (S : List (Nat × Nat × Nat)) :
    findLive (relabelRecords f S) = relabelRecords f (findLive S) := by
  unfold findLive
  rw [splitLive_relabel]
  simp [relabelRecords, List.map_append]

theorem totW_relabel (f : Nat → Nat) (S : List (Nat × Nat × Nat)) :
    totW (relabelRecords f S) = totW S := by
  simp [totW, relabelRecords, List.map_map, Function.comp_def]

theorem stepW_relabel (f : Nat → Nat) (L : Nat) (st : WState) (x : Nat) :
    stepW L (relabelW f st) x = (relabelW f (stepW L st x).1, (stepW L st x).2) := by
  simp only [stepW, relabelW, findLive_relabel]
  cases hf : findLive st.S with
  | nil => simp [relabelRecords]
  | cons p T =>
    rcases p with ⟨id, A, r⟩
    simp only [relabelRecords, List.map_cons]
    split <;> simp [List.map_append]

theorem runW_relabel (f : Nat → Nat) (L n : Nat) (st : WState) (x : Nat) :
    runW L n (relabelW f st) x =
      (relabelW f (runW L n st x).1, (runW L n st x).2) := by
  induction n generalizing st x with
  | zero => rfl
  | succ n ih =>
    simp only [runW, relabelW, totW_relabel]
    split
    · rfl
    · change runW L n (stepW L (relabelW f st) x).1
        (x - (stepW L (relabelW f st) x).2) = _
      rw [stepW_relabel]
      exact ih _ _

theorem runWFull_relabel (f : Nat → Nat) (L : Nat) (st : WState) (x : Nat) :
    runWFull L (relabelW f st) x =
      (relabelW f (runWFull L st x).1, (runWFull L st x).2) := by
  unfold runWFull
  simp only [relabelW, totW_relabel]
  exact runW_relabel f L (totW st.S + 1) st x

/-- The water-fill depth-share inequality does not transfer unchanged to the
    finite-increment wheel, including the persistent implementation. -/
theorem wheel_book_share_counterexample :
    (wheel 100 20 [1000, 100] 100).1 = [100, 0] ∧
    nextWFill 100 (initW 100 [(0, 1000), (1, 100)]) 100 0 = 100 ∧
    100 * (1000 + 100) > 1000 * 100 := by decide

theorem ex_phase_state_separation :
    nextWFill 100 (phaseState 3 100 1 40) 41 1 = 40 ∧
    nextWFill 100 (phaseState 3 100 1 80) 41 1 = 41 := by decide

end Rule737
