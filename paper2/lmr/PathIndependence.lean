/-
  PathIndependence.lean — allocation rules as rationing rules.  Estate-indexed
  composition means that allocating x then y from the residual equals allocating
  x + y at once. Price–time satisfies it; integer water-filling instead has a
  level-indexed semigroup identity and cannot represent every estate. The
  pass-reset wheel fails stream consistency; the pointer-and-lot wheel satisfies
  it under explicit completion and termination hypotheses. Lean 4.22.0, core only.
-/
import Rulebook
import Balance
namespace Rule737

/-! ## Estate composition versus water-level composition -/

theorem pt_zero (Q : List Nat) : priceTime Q 0 = Q.map (fun _ => 0) := by
  induction Q with
  | nil => rfl
  | cons a A ih => simp [priceTime, ih]

theorem pt_length (Q : List Nat) (x : Nat) : (priceTime Q x).length = Q.length := by
  induction Q generalizing x with
  | nil => rfl
  | cons q Q ih => simp [priceTime, ih]

theorem zip_sub_zero (Q : List Nat) : List.zipWith (fun q a => q - a) Q (Q.map fun _ => 0) = Q := by
  induction Q with
  | nil => rfl
  | cons a A ih => simp [ih]

theorem zip_zero_add (A B : List Nat) (h : A.length = B.length) :
    List.zipWith (fun a b => a + b) (A.map fun _ => 0) B = B := by
  induction A generalizing B with
  | nil => cases B <;> simp at h ⊢
  | cons a A ih => cases B with
    | nil => simp at h
    | cons b B => simp [ih B (by simpa using h)]

theorem priceTime_comp (Q : List Nat) (x y : Nat) :
    priceTime Q (x + y) =
      List.zipWith (fun a b => a + b) (priceTime Q x)
        (priceTime (List.zipWith (fun q a => q - a) Q (priceTime Q x)) y) := by
  induction Q generalizing x y with
  | nil => rfl
  | cons q Q ih =>
      simp only [priceTime, List.zipWith_cons_cons]
      by_cases hq : q ≤ x
      · rw [Nat.min_eq_left hq, Nat.sub_self, Nat.min_eq_left (Nat.zero_le _)]
        rw [Nat.min_eq_left (by omega : q ≤ x + y)]
        have : x + y - q = (x - q) + y := by omega
        rw [this, ih]; simp
      · have hx : min q x = x := Nat.min_eq_right (by omega)
        rw [hx, Nat.sub_self]
        have h2 : min q (x + y) = x + min (q - x) y := by omega
        have h3 : x + y - (x + min (q - x) y) = y - min (q - x) y := by omega
        rw [h2, h3, pt_zero, zip_sub_zero, zip_zero_add _ _ (by rw [pt_length])]

/-- **Sequential conformance composes.** If the first queue-aligned fill vector conforms to
    the original queue and the second conforms to the residual queue, their
    componentwise sum conforms to one execution of the combined quantity. -/
theorem conformsPT_comp (Q first second : List Nat) (x y : Nat)
    (hfirst : conformsPT Q first x = true)
    (hsecond : conformsPT
      (List.zipWith (fun q a => q - a) Q first) second y = true) :
    conformsPT Q (List.zipWith (fun a b => a + b) first second) (x + y) = true := by
  unfold conformsPT at hfirst hsecond ⊢
  have hf : first = priceTime Q x := by simpa using hfirst
  subst first
  have hs : second = priceTime
      (List.zipWith (fun q a => q - a) Q (priceTime Q x)) y := by
    simpa using hsecond
  subst second
  rw [priceTime_comp]
  simp

/-- Water-filling composes in its index: level s then level t on the residual is
    level s + t. This is not an estate-indexed rationing theorem. -/
theorem waterFill_level_comp (Q : List Nat) (s t : Nat) :
    waterFill (s + t) Q =
      List.zipWith (fun a b => a + b) (waterFill s Q)
        (waterFill t (List.zipWith (fun q a => q - a) Q (waterFill s Q))) := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
      simp only [waterFill, List.map_cons, List.zipWith_cons_cons] at ih ⊢
      rw [ih]; congr 1; omega

/-- Integer water levels do not encode every estate: for two ten-share claims,
    no natural-number water level allocates exactly one share. -/
theorem waterFill_two_equal_no_single_share (s : Nat) :
    (waterFill s [10, 10]).sum ≠ 1 := by
  simp [waterFill]
  omega

/-! ## The pass-reset wheel is NOT path independent -/

/-- Two participants of 300, L = 100.  100 then 100 (restarting the pass each
    time) gives (200, 0); 200 at once gives (100, 100). -/
theorem wheel_not_path_independent :
    let R : List Nat := [300, 300]
    let A := (wheel 100 10 R 100).1
    let B := (wheel 100 10 (List.zipWith (fun r a => r - a) R A) 100).1
    List.zipWith (fun a b => a + b) A B = [200, 0] ∧ (wheel 100 10 R 200).1 = [100, 100] := by
  decide

/-! ## The pointer-and-lot wheel composes for completed runs -/

/-- Participant: (id, allocated, remaining).  The list is kept rotated so that
    its head is the pointer.  `lot` is the round-lot allowance left for the head. -/
structure WState where
  S   : List (Nat × Nat × Nat)
  lot : Nat
  deriving DecidableEq, Repr

def live (p : Nat × Nat × Nat) : Bool := decide (0 < p.2.2)
def totW (S : List (Nat × Nat × Nat)) : Nat := (S.map (·.2.2)).sum

/-! ### Splitting off the dead prefix -/

def splitLive : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) × List (Nat × Nat × Nat)
  | [] => ([], [])
  | p :: T => if live p then ([], p :: T) else
      let r := splitLive T
      (p :: r.1, r.2)

theorem splitLive_append (S : List (Nat × Nat × Nat)) : (splitLive S).1 ++ (splitLive S).2 = S := by
  induction S with
  | nil => rfl
  | cons p T ih =>
      simp only [splitLive]
      split
      · rfl
      · simp only [List.cons_append]; rw [ih]

theorem splitLive_live (S : List (Nat × Nat × Nat)) (h : 0 < totW S) :
    ∃ p T, (splitLive S).2 = p :: T ∧ live p = true := by
  induction S with
  | nil => simp [totW] at h
  | cons p T ih =>
      simp only [splitLive]
      split
      · rename_i hl; exact ⟨p, T, rfl, hl⟩
      · rename_i hl
        have hp : p.2.2 = 0 := by simp [live] at hl; omega
        have hsum : totW (p :: T) = p.2.2 + totW T := by simp [totW]
        have : 0 < totW T := by omega
        exact ih this

theorem totW_append (A B : List (Nat × Nat × Nat)) : totW (A ++ B) = totW A + totW B := by
  induction A with
  | nil => simp [totW]
  | cons p A ih => simp only [totW, List.cons_append, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem length_append_eq (A B : List (Nat × Nat × Nat)) : (A ++ B).length = A.length + B.length :=
  List.length_append

/-- Rotate the dead prefix to the back. -/
def findLive (S : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) := (splitLive S).2 ++ (splitLive S).1

theorem mem_findLive_iff (p : Nat × Nat × Nat) (S : List (Nat × Nat × Nat)) :
    p ∈ findLive S ↔ p ∈ S := by
  unfold findLive
  rw [List.mem_append, or_comm, ← List.mem_append, splitLive_append]

theorem findLive_tot (S : List (Nat × Nat × Nat)) : totW (findLive S) = totW S := by
  unfold findLive; rw [totW_append, Nat.add_comm, ← totW_append, splitLive_append]

theorem findLive_head (S : List (Nat × Nat × Nat)) (h : 0 < totW S) :
    ∃ p T, findLive S = p :: T ∧ live p = true := by
  obtain ⟨p, T, hpt, hl⟩ := splitLive_live S h
  exact ⟨p, T ++ (splitLive S).1, by unfold findLive; rw [hpt]; rfl, hl⟩

theorem findLive_of_live (p : Nat × Nat × Nat) (T : List (Nat × Nat × Nat)) (h : live p = true) :
    findLive (p :: T) = p :: T := by
  simp [findLive, splitLive, h]

/-! ### Pointer-relative balance invariant -/

/-- Allocations of the live participants, in pointer order.  Dead records are
    retained in `WState.S` for identity and capacity accounting but do not
    occupy a turn in this list. -/
def liveAllocs : List (Nat × Nat × Nat) → List Nat
  | [] => []
  | p :: T => if live p then p.2.1 :: liveAllocs T else liveAllocs T

theorem liveAllocs_append (A B : List (Nat × Nat × Nat)) :
    liveAllocs (A ++ B) = liveAllocs A ++ liveAllocs B := by
  induction A with
  | nil => rfl
  | cons p A ih =>
      simp only [List.cons_append, liveAllocs]
      split <;> simp [ih]

theorem splitLive_fst_dead (S : List (Nat × Nat × Nat)) :
    ∀ p ∈ (splitLive S).1, live p = false := by
  induction S with
  | nil => intro p hp; simp [splitLive] at hp
  | cons p T ih =>
      simp only [splitLive]
      split
      · intro q hq; simp at hq
      · rename_i hp
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · cases hq : live q <;> simp_all
        · exact ih q hq

theorem liveAllocs_of_dead (S : List (Nat × Nat × Nat))
    (h : ∀ p ∈ S, live p = false) : liveAllocs S = [] := by
  induction S with
  | nil => rfl
  | cons p T ih =>
      rw [liveAllocs, if_neg (by simpa using h p (List.mem_cons_self ..))]
      exact ih (fun q hq => h q (List.mem_cons_of_mem p hq))

theorem liveAllocs_findLive (S : List (Nat × Nat × Nat)) :
    liveAllocs (findLive S) = liveAllocs S := by
  have hd := liveAllocs_of_dead (splitLive S).1 (splitLive_fst_dead S)
  unfold findLive
  rw [liveAllocs_append, hd, List.append_nil]
  rw [← List.nil_append (liveAllocs (splitLive S).2), ← hd, ← liveAllocs_append]
  rw [splitLive_append]

/-- `TwoPhase lo hi xs` means that `xs` contains zero or more entries at
    `lo`, followed by entries all at `hi`.  It is the exact shape of the live
    tail after the pointer during a round-robin cycle. -/
inductive TwoPhase (lo hi : Nat) : List Nat → Prop
  | high (xs : List Nat) (h : ∀ a ∈ xs, a = hi) : TwoPhase lo hi xs
  | low {xs : List Nat} (h : TwoPhase lo hi xs) : TwoPhase lo hi (lo :: xs)

theorem TwoPhase.allLow (lo hi : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, a = lo) : TwoPhase lo hi xs := by
  induction xs with
  | nil => exact .high [] (by simp)
  | cons a A ih =>
      have ha := h a (List.mem_cons_self ..)
      subst a
      exact .low (ih (fun b hb => h b (List.mem_cons_of_mem lo hb)))

theorem TwoPhase.appendHigh {lo hi : Nat} {xs : List Nat}
    (h : TwoPhase lo hi xs) : TwoPhase lo hi (xs ++ [hi]) := by
  induction h with
  | high xs hall =>
      apply TwoPhase.high
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hall a ha
      · simpa using ha
  | low h ih => exact TwoPhase.low ih

theorem TwoPhase.consCases {lo hi a : Nat} {xs : List Nat}
    (h : TwoPhase lo hi (a :: xs)) :
    (a = lo ∧ TwoPhase lo hi xs) ∨
      (a = hi ∧ ∀ b ∈ xs, b = hi) := by
  cases h with
  | low h => exact Or.inl ⟨rfl, h⟩
  | high _ hall =>
      exact Or.inr ⟨hall a (List.mem_cons_self ..),
        fun b hb => hall b (List.mem_cons_of_mem a hb)⟩

theorem TwoPhase.mem {lo hi : Nat} {xs : List Nat}
    (h : TwoPhase lo hi xs) : ∀ a ∈ xs, a = lo ∨ a = hi := by
  intro a ha
  induction h with
  | high xs hall => exact Or.inr (hall a ha)
  | low h ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      · exact ih ha

theorem mem_liveAllocs {p : Nat × Nat × Nat} {S : List (Nat × Nat × Nat)}
    (hp : p ∈ S) (hlive : live p = true) : p.2.1 ∈ liveAllocs S := by
  induction S with
  | nil => simp at hp
  | cons r R ih =>
      rw [liveAllocs]
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [if_pos hlive]; exact List.mem_cons_self
      · split
        · exact List.mem_cons_of_mem _ (ih hp)
        · exact ih hp

/-- Pointer-relative invariant.  Every allocation is below `v+L`.  If a live
    head exists, its allocation plus its unused lot allowance is exactly
    `v+L`; the remaining live allocations form a low-then-high two-phase list.
    This records the boundary between participants not yet visited in the
    current cycle and those already visited. -/
def AllAtP (L v : Nat) (st : WState) : Prop :=
  st.lot ≤ L ∧
  (∀ p ∈ st.S, p.2.1 ≤ v + L) ∧
  match liveAllocs st.S with
  | [] => True
  | a :: A => a + st.lot = v + L ∧ TwoPhase v (v + L) A

/-- The pointer-relative invariant implies the same one-lot band used for the
    pass-based wheel. -/
theorem AllAtP_band {L v : Nat} {st : WState} (h : AllAtP L v st) :
    Band L v (st.S.map (fun p => (p.2.1, p.2.2))) := by
  constructor
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact h.2.1 q hq
  · intro q hq hqr
    simp only [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hlive : live p = true := by simp [live]; exact hqr
    have hm : p.2.1 ∈ liveAllocs st.S := mem_liveAllocs hp hlive
    cases hla : liveAllocs st.S with
    | nil => rw [hla] at hm; simp at hm
    | cons a A =>
        rw [hla] at hm
        have hs := h.2.2
        rw [hla] at hs
        rcases List.mem_cons.mp hm with ha | hm
        · subst ha
          have := h.1
          omega
        · have hcases : ∀ b ∈ A, b = v ∨ b = v + L := TwoPhase.mem hs.2
          rcases hcases p.2.1 hm with hpv | hpv <;> omega

/-- One visit of the live head.  Returns new state and fill. -/
def stepW (L : Nat) (st : WState) (x : Nat) : WState × Nat :=
  match findLive st.S with
  | [] => (st, 0)
  | (id, a, r) :: T =>
      let g := min st.lot (min r x)
      if g = min st.lot r then (⟨T ++ [(id, a + g, r - g)], L⟩, g)   -- lot done: advance, reset
      else (⟨(id, a + g, r - g) :: T, st.lot - g⟩, g)                -- partial: stay

def runW (L : Nat) : Nat → WState → Nat → WState × Nat
  | 0, st, x => (st, x)
  | n + 1, st, x =>
      if x = 0 ∨ totW st.S = 0 then (st, x)
      else
        let r := stepW L st x
        runW L n r.1 (x - r.2)

/-- The counterexample of `wheel_not_path_independent`, now path independent. -/
def st0 : WState := ⟨[(1, 0, 300), (2, 0, 300)], 100⟩
theorem pointer_wheel_instance :
    (runW 100 10 (runW 100 10 st0 100).1 100).1 = (runW 100 10 st0 200).1 ∧
    (runW 100 10 st0 200).1.S.map (·.2.1) = [100, 100] := by decide
theorem pointer_wheel_odd_instance :
    (runW 100 10 (runW 100 10 st0 150).1 150).1 = (runW 100 10 st0 300).1 := by decide

/-! ### Pointer observability is necessary -/

/-- Allocation of participant `id`, independent of the state's rotated list
    representation.  This finite observer is used only for the four-party
    identification counterexample below. -/
def wAllocationOf (id : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | p :: T => if p.1 = id then p.2.1 else wAllocationOf id T

def wCapacityOf (id : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | p :: T => if p.1 = id then p.2.1 + p.2.2 else wCapacityOf id T

def wPrint4 (st : WState) : List Nat :=
  [wAllocationOf 1 st.S, wAllocationOf 2 st.S,
   wAllocationOf 3 st.S, wAllocationOf 4 st.S]

def wQueue4 (st : WState) : List Nat :=
  [wCapacityOf 1 st.S, wCapacityOf 2 st.S,
   wCapacityOf 3 st.S, wCapacityOf 4 st.S]

def pointerA : WState :=
  ⟨[(1, 0, 300), (2, 0, 500), (3, 0, 200), (4, 0, 1000)], 100⟩

def pointerC : WState :=
  ⟨[(3, 0, 200), (4, 0, 1000), (1, 0, 300), (2, 0, 500)], 100⟩

/-- **No pointer identification from prints.** The same participant-labelled
    queue and the same 1,100-share queue-aligned fill vector arise from two distinct initial
    pointer states, yet the terminal states and the next 100-share allocation
    differ.  Hence queue plus prints is not an injective observation of the
    parity state. -/
theorem parity_pointer_not_identified_from_prints :
    pointerA ≠ pointerC ∧ wQueue4 pointerA = wQueue4 pointerC ∧
    wPrint4 (runW 100 30 pointerA 1100).1 =
      wPrint4 (runW 100 30 pointerC 1100).1 ∧
    (runW 100 30 pointerA 1100).1 ≠ (runW 100 30 pointerC 1100).1 ∧
    wPrint4 (runW 100 30 (runW 100 30 pointerA 1100).1 100).1 ≠
      wPrint4 (runW 100 30 (runW 100 30 pointerC 1100).1 100).1 := by
  decide

def conformsW4 (st : WState) (x : Nat) (prints : List Nat) : Bool :=
  prints == wPrint4 (runW 100 30 st x).1

/-- No pointer-free Boolean checker can be correct even on the two displayed
    states: their participant-labelled queues and candidate aligned fill vector are
    identical, but that vector conforms under `pointerA` and fails under
    `pointerC`. -/
theorem no_parity_conformance_from_queue_and_prints :
    ¬ ∃ d : List Nat → List Nat → Bool,
      d (wQueue4 pointerA) [100, 0, 0, 0] =
          conformsW4 pointerA 100 [100, 0, 0, 0] ∧
      d (wQueue4 pointerC) [100, 0, 0, 0] =
          conformsW4 pointerC 100 [100, 0, 0, 0] := by
  intro h
  obtain ⟨d, hA, hC⟩ := h
  have hq : wQueue4 pointerA = wQueue4 pointerC := by decide
  have hcA : conformsW4 pointerA 100 [100, 0, 0, 0] = true := by decide
  have hcC : conformsW4 pointerC 100 [100, 0, 0, 0] = false := by decide
  rw [hcA] at hA
  rw [hcC, ← hq] at hC
  rw [hA] at hC
  contradiction

/-! ### A minimal-information lower bound -/

/-- The canonical information visible at one instant in the four-party model:
    participant-labelled capacities and participant-aligned cumulative fills. -/
def wObservation4 (st : WState) : List Nat × List Nat :=
  (wQueue4 st, wPrint4 st)

/-- A summary is future sufficient when, together with the current canonical
    observation and the next quantity, it predicts every next fill vector in
    the four-party pointer-wheel model.  The summary may have any codomain. -/
def FutureSufficient4 {α : Type} (summary : WState → α) : Prop :=
  ∃ predict : (List Nat × List Nat) → α → Nat → List Nat,
    ∀ st x, predict (wObservation4 st) (summary st) x =
      wPrint4 (runW 100 30 st x).1

/-- **Pointer information is necessary.** Every future-sufficient summary must
    distinguish the two pointer states that canonical queue and fills identify.
    This is an information lower bound: it does not claim that the concrete
    `WState` representation, or its `lot` field separately, is globally minimal. -/
theorem future_sufficient_summary_requires_pointer_information
    {α : Type} (summary : WState → α) (h : FutureSufficient4 summary) :
    summary pointerA ≠ summary pointerC := by
  intro heq
  obtain ⟨predict, hpredict⟩ := h
  have hobs : wObservation4 pointerA = wObservation4 pointerC := by decide
  have hA := hpredict pointerA 100
  have hC := hpredict pointerC 100
  have hfuture :
      wPrint4 (runW 100 30 pointerA 100).1 ≠
        wPrint4 (runW 100 30 pointerC 100).1 := by decide
  apply hfuture
  rw [← hA, ← hC, hobs, heq]

/-! ### A general Myhill--Nerode lower bound on the saturated phase state

The full `WState` automaton contains exhausted and one-live-participant states
in which some raw pointer/allowance values are observationally redundant.  The
following subsystem isolates the nondegenerate case: at least two live
participants, each with enough remaining size that the future owner trace does
not hit a claim boundary.  Its phase state is a pointer `p < m` and an unused
allowance `0 < a ≤ L`. -/

def ValidSaturatedPhase (m L p a : Nat) : Prop :=
  p < m ∧ 0 < a ∧ a ≤ L

/-- Owner of the `t`-th future unit in the saturated wheel.  The first `a`
    units go to the current pointer; later units advance in blocks of `L`. -/
def saturatedOwner (m L p a t : Nat) : Nat :=
  if t < a then p else (p + 1 + (t - a) / L) % m

def SaturatedFutureEquivalent (m L p a q b : Nat) : Prop :=
  ∀ t, saturatedOwner m L p a t = saturatedOwner m L q b t

theorem succ_mod_ne_self (m p : Nat) (hm : 2 ≤ m) (hp : p < m) :
    (p + 1) % m ≠ p := by
  by_cases hnext : p + 1 < m
  · rw [Nat.mod_eq_of_lt hnext]
    omega
  · have hwrap : p + 1 = m := by omega
    rw [hwrap, Nat.mod_self]
    omega

/-- **Exact future quotient on the saturated phase subsystem.**  Two valid
    phase states have the same owner for every future unit iff both their
    pointer and unused allowance agree. -/
theorem saturated_future_equiv_iff (m L p a q b : Nat)
    (hm : 2 ≤ m) (hp : ValidSaturatedPhase m L p a)
    (hq : ValidSaturatedPhase m L q b) :
    SaturatedFutureEquivalent m L p a q b ↔ p = q ∧ a = b := by
  constructor
  · intro heq
    have hzero := heq 0
    have hp0 : 0 < a := hp.2.1
    have hq0 : 0 < b := hq.2.1
    simp [saturatedOwner, hp0, hq0] at hzero
    subst q
    refine ⟨rfl, ?_⟩
    apply Classical.byContradiction
    intro hab
    rcases Nat.lt_or_gt_of_ne hab with hab | hab
    · have hprobe := heq a
      have hsucc := succ_mod_ne_self m p hm hp.1
      simp [saturatedOwner, hab] at hprobe
      exact hsucc hprobe
    · have hprobe := heq b
      have hsucc := succ_mod_ne_self m p hm hp.1
      simp [saturatedOwner, hab] at hprobe
      exact hsucc hprobe.symm
  · intro h
    rcases h with ⟨rfl, rfl⟩
    intro t
    rfl

/-- A summary is future sufficient for the saturated phase subsystem when a
    decoder can recover every future owner from the summary alone. -/
def SaturatedFutureSufficient {α : Type} (m L : Nat)
    (summary : Nat → Nat → α) : Prop :=
  ∃ predict : α → Nat → Nat,
    ∀ p a, ValidSaturatedPhase m L p a →
      ∀ t, predict (summary p a) t = saturatedOwner m L p a t

/-- **Cardinality lower-bound theorem.**  Any future-sufficient summary is
    injective on the `m × L` valid saturated phase states (`m ≥ 2`, `L > 0`).
    Thus its image has at least `m*L` classes; an implementation needs at least
    `ceil(log2(m*L))` bits to encode those classes. -/
theorem saturated_future_sufficient_injective {α : Type} (m L : Nat)
    (summary : Nat → Nat → α) (hm : 2 ≤ m)
    (hs : SaturatedFutureSufficient m L summary)
    (p a q b : Nat) (hp : ValidSaturatedPhase m L p a)
    (hq : ValidSaturatedPhase m L q b)
    (hsummary : summary p a = summary q b) :
    p = q ∧ a = b := by
  obtain ⟨predict, hpredict⟩ := hs
  apply (saturated_future_equiv_iff m L p a q b hm hp hq).mp
  intro t
  rw [← hpredict p a hp t, ← hpredict q b hq t, hsummary]

/-- A run is stopped if it ended with no quantity or no remaining size. -/
def Stopped (st : WState) (x : Nat) : Prop := x = 0 ∨ totW st.S = 0

theorem runW_x0 (L n : Nat) (st : WState) : runW L n st 0 = (st, 0) := by
  cases n <;> simp [runW]

theorem runW_stable (L n k : Nat) (st : WState) (x : Nat)
    (h : Stopped (runW L n st x).1 (runW L n st x).2) :
    runW L (n + k) st x = runW L n st x := by
  induction n generalizing st x k with
  | zero =>
      simp only [runW] at h
      unfold Stopped at h
      cases k with
      | zero => rfl
      | succ k => simp only [runW]; rw [if_pos h]
  | succ n ih =>
      simp only [runW] at h ⊢
      rw [Nat.succ_add]
      simp only [runW]
      split
      · rfl
      · rename_i hc
        rw [if_neg hc] at h
        exact ih _ _ _ h

theorem stepW_adv (L : Nat) (st : WState) (id a r : Nat) (T : List (Nat × Nat × Nat)) (x : Nat)
    (hpt : findLive st.S = (id, a, r) :: T) (h : min st.lot r ≤ x) :
    stepW L st x = (⟨T ++ [(id, a + min st.lot r, r - min st.lot r)], L⟩, min st.lot r) := by
  unfold stepW; rw [hpt]
  have e : min st.lot (min r x) = min st.lot r := by omega
  simp only [e, if_true]

theorem stepW_partial (L : Nat) (st : WState) (id a r : Nat) (T : List (Nat × Nat × Nat)) (x : Nat)
    (hpt : findLive st.S = (id, a, r) :: T) (h : x < min st.lot r) :
    stepW L st x = (⟨(id, a + x, r - x) :: T, st.lot - x⟩, x) := by
  unfold stepW; rw [hpt]
  have e : min st.lot (min r x) = x := by omega
  simp only [e]
  rw [if_neg (by omega)]

/-- A visit preserves the pointer-relative invariant, possibly advancing the
    completed water level by one lot when the pointer crosses the cycle
    boundary. -/
theorem stepW_allAtP (L v : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hInv : AllAtP L v st) (ht : 0 < totW st.S) :
    ∃ w, v ≤ w ∧ (w = v ∨ w = v + L) ∧ AllAtP L w (stepW L st x).1 := by
  obtain ⟨p, T, hpt, hlive⟩ := findLive_head st.S ht
  obtain ⟨id, a, r⟩ := p
  have hr : 0 < r := by simp [live] at hlive; exact hlive
  have hla : liveAllocs st.S = a :: liveAllocs T := by
    rw [← liveAllocs_findLive st.S, hpt]
    simp [liveAllocs, live, hr]
  have hlot : st.lot ≤ L := hInv.1
  have hupper : ∀ q ∈ st.S, q.2.1 ≤ v + L := hInv.2.1
  have hshape := hInv.2.2
  rw [hla] at hshape
  have haeq : a + st.lot = v + L := hshape.1
  have hphase : TwoPhase v (v + L) (liveAllocs T) := hshape.2
  have hTmem : ∀ q ∈ T, q ∈ st.S := by
    intro q hq
    apply (mem_findLive_iff q st.S).mp
    rw [hpt]
    exact List.mem_cons_of_mem (id, a, r) hq
  have hTupper : ∀ q ∈ T, q.2.1 ≤ v + L :=
    fun q hq => hupper q (hTmem q hq)
  by_cases hbig : min st.lot r ≤ x
  · rw [stepW_adv L st id a r T x hpt hbig]
    let g := min st.lot r
    have hg : g ≤ st.lot := Nat.min_le_left _ _
    have hu : a + g ≤ v + L := by dsimp [g]; omega
    let u : Nat × Nat × Nat := (id, a + g, r - g)
    have huUpper : u.2.1 ≤ v + L := by exact hu
    have hAllUpper : ∀ q ∈ T ++ [u], q.2.1 ≤ v + L := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hTupper q hq
      · have : q = u := by simpa using hq
        subst q
        exact huUpper
    change ∃ w, v ≤ w ∧ (w = v ∨ w = v + L) ∧ AllAtP L w ⟨T ++ [u], L⟩
    cases htail : liveAllocs T with
    | nil =>
        by_cases hrem : 0 < r - g
        · have hug : g = st.lot := by dsimp [g] at *; omega
          have hua : a + g = v + L := by omega
          have hulive : live u = true := by simp [u, live]; exact hrem
          have huaU : u.2.1 = v + L := by simpa [u] using hua
          have hLU : liveAllocs [u] = [v + L] := by
            simp [liveAllocs, hulive, huaU]
          refine ⟨v + L, by omega, Or.inr rfl, ?_⟩
          unfold AllAtP
          refine ⟨Nat.le_refl _, ?_, ?_⟩
          · intro q hq
            have := hAllUpper q hq
            omega
          · rw [liveAllocs_append, htail, hLU]
            exact ⟨rfl, TwoPhase.high [] (by simp)⟩
        · have hr0 : r - g = 0 := by omega
          have hulive : live u = false := by simp [u, live, hr0]
          have hLU : liveAllocs [u] = [] := by simp [liveAllocs, hulive]
          refine ⟨v, Nat.le_refl _, Or.inl rfl, ?_⟩
          unfold AllAtP
          refine ⟨Nat.le_refl _, hAllUpper, ?_⟩
          rw [liveAllocs_append, htail, hLU]
          simp
    | cons b B =>
        rcases TwoPhase.consCases (by simpa [htail] using hphase) with
          ⟨hb, hBphase⟩ | ⟨hb, hBhigh⟩
        · subst b
          by_cases hrem : 0 < r - g
          · have hug : g = st.lot := by dsimp [g] at *; omega
            have hua : a + g = v + L := by omega
            have hulive : live u = true := by simp [u, live]; exact hrem
            have huaU : u.2.1 = v + L := by simpa [u] using hua
            have hLU : liveAllocs [u] = [v + L] := by
              simp [liveAllocs, hulive, huaU]
            refine ⟨v, Nat.le_refl _, Or.inl rfl, ?_⟩
            unfold AllAtP
            refine ⟨Nat.le_refl _, hAllUpper, ?_⟩
            rw [liveAllocs_append, htail, hLU]
            simp only [List.cons_append]
            exact ⟨by trivial, hBphase.appendHigh⟩
          · have hr0 : r - g = 0 := by omega
            have hulive : live u = false := by simp [u, live, hr0]
            have hLU : liveAllocs [u] = [] := by simp [liveAllocs, hulive]
            refine ⟨v, Nat.le_refl _, Or.inl rfl, ?_⟩
            unfold AllAtP
            refine ⟨Nat.le_refl _, hAllUpper, ?_⟩
            rw [liveAllocs_append, htail, hLU]
            simp only [List.append_nil]
            exact ⟨by trivial, hBphase⟩
        · subst b
          by_cases hrem : 0 < r - g
          · have hug : g = st.lot := by dsimp [g] at *; omega
            have hua : a + g = v + L := by omega
            have hulive : live u = true := by simp [u, live]; exact hrem
            have huaU : u.2.1 = v + L := by simpa [u] using hua
            have hLU : liveAllocs [u] = [v + L] := by
              simp [liveAllocs, hulive, huaU]
            refine ⟨v + L, by omega, Or.inr rfl, ?_⟩
            unfold AllAtP
            refine ⟨Nat.le_refl _, ?_, ?_⟩
            · intro q hq
              have := hAllUpper q hq
              omega
            · rw [liveAllocs_append, htail, hLU]
              simp only [List.cons_append]
              refine ⟨by trivial, ?_⟩
              apply TwoPhase.allLow
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact hBhigh z hz
              · simpa using hz
          · have hr0 : r - g = 0 := by omega
            have hulive : live u = false := by simp [u, live, hr0]
            have hLU : liveAllocs [u] = [] := by simp [liveAllocs, hulive]
            refine ⟨v + L, by omega, Or.inr rfl, ?_⟩
            unfold AllAtP
            refine ⟨Nat.le_refl _, ?_, ?_⟩
            · intro q hq
              have := hAllUpper q hq
              omega
            · rw [liveAllocs_append, htail, hLU]
              simp only [List.append_nil]
              refine ⟨by trivial, ?_⟩
              exact TwoPhase.allLow _ _ _ hBhigh
  · have hlt : x < min st.lot r := by omega
    rw [stepW_partial L st id a r T x hpt hlt]
    have hnewlive : live (id, a + x, r - x) = true := by
      simp [live]
      omega
    refine ⟨v, Nat.le_refl _, Or.inl rfl, ?_⟩
    unfold AllAtP
    refine ⟨Nat.le_trans (Nat.sub_le _ _) hlot, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only
        omega
      · exact hTupper q hq
    · simp only [liveAllocs, if_pos hnewlive]
      refine ⟨by omega, hphase⟩

/-- Iterating visits preserves the pointer-relative invariant and can only
    raise its completed water level. -/
theorem runW_allAtP (L n : Nat) (st : WState) (x v : Nat)
    (hL : 0 < L) (hInv : AllAtP L v st) :
    ∃ w, v ≤ w ∧ AllAtP L w (runW L n st x).1 := by
  induction n generalizing st x v with
  | zero => exact ⟨v, Nat.le_refl _, hInv⟩
  | succ n ih =>
      simp only [runW]
      by_cases hstop : x = 0 ∨ totW st.S = 0
      · rw [if_pos hstop]
        exact ⟨v, Nat.le_refl _, hInv⟩
      · rw [if_neg hstop]
        have ht : 0 < totW st.S := by omega
        obtain ⟨w, hvw, _, hw⟩ := stepW_allAtP L v st x hL hInv ht
        obtain ⟨z, hwz, hz⟩ := ih (stepW L st x).1
          (x - (stepW L st x).2) w hw
        exact ⟨z, Nat.le_trans hvw hwz, hz⟩

/-- Initialized pointer wheel with explicit participant identifiers. -/
def initW (L : Nat) (R : List (Nat × Nat)) : WState :=
  ⟨R.map (fun p => (p.1, 0, p.2)), L⟩

theorem liveAllocs_initW_zero (R : List (Nat × Nat)) :
    ∀ a ∈ liveAllocs (R.map (fun p => (p.1, 0, p.2))), a = 0 := by
  induction R with
  | nil => intro a ha; simp [liveAllocs] at ha
  | cons p R ih =>
      intro a ha
      simp only [List.map_cons, liveAllocs] at ha
      split at ha
      · rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact ih a ha
      · exact ih a ha

theorem initW_allAtP (L : Nat) (R : List (Nat × Nat)) :
    AllAtP L 0 (initW L R) := by
  unfold initW AllAtP
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact Nat.zero_le _
  · cases hla : liveAllocs (R.map (fun p => (p.1, 0, p.2))) with
    | nil => trivial
    | cons a A =>
        have hall := liveAllocs_initW_zero R
        have ha : a = 0 := by
          apply hall a
          rw [hla]
          exact List.mem_cons_self
        subst a
        refine ⟨rfl, ?_⟩
        apply TwoPhase.allLow
        intro b hb
        apply hall b
        rw [hla]
        exact List.mem_cons_of_mem 0 hb

/-- Reachable wheel states lie at an integral cycle phase.  The witness `k`
    counts completed cycles, while `AllAtP` records the current within-cycle
    pointer and unused allowance. -/
def AtWheelPhase (L : Nat) (st : WState) : Prop :=
  ∃ k, AllAtP L (k * L) st

theorem initW_atWheelPhase (L : Nat) (R : List (Nat × Nat)) :
    AtWheelPhase L (initW L R) := by
  refine ⟨0, ?_⟩
  simpa using initW_allAtP L R

/-- Every fuel-bounded execution from an integral cycle phase remains at an
    integral cycle phase. -/
theorem runW_atWheelPhase (L n : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hphase : AtWheelPhase L st) :
    AtWheelPhase L (runW L n st x).1 := by
  induction n generalizing st x with
  | zero => simpa [runW] using hphase
  | succ n ih =>
      simp only [runW]
      by_cases hstop : x = 0 ∨ totW st.S = 0
      · rw [if_pos hstop]
        exact hphase
      · rw [if_neg hstop]
        obtain ⟨k, hk⟩ := hphase
        obtain ⟨w, _, hw, hInv⟩ :=
          stepW_allAtP L (k * L) st x hL hk (by omega)
        apply ih
        rcases hw with hw | hw
        · subst w
          exact ⟨k, hInv⟩
        · subst w
          refine ⟨k + 1, ?_⟩
          simpa [Nat.add_mul] using hInv

/-- **One operator now has both central guarantees.** From an initialized
    participant-labelled queue, every state returned by a fuel-bounded run of the
    pointer-and-lot wheel lies in a one-round-lot band.  Together with
    `runW_comp`, this is the same operator's balance and path-independence
    certificate. -/
theorem runW_band (L n : Nat) (R : List (Nat × Nat)) (x : Nat) (hL : 0 < L) :
    ∃ w, Band L w
      ((runW L n (initW L R) x).1.S.map (fun p => (p.2.1, p.2.2))) := by
  obtain ⟨w, _, hw⟩ := runW_allAtP L n (initW L R) x 0 hL (initW_allAtP L R)
  exact ⟨w, AllAtP_band hw⟩

theorem runW_balanced (L n : Nat) (R : List (Nat × Nat)) (x : Nat) (hL : 0 < L) :
    Balanced L
      ((runW L n (initW L R) x).1.S.map (fun p => (p.2.1, p.2.2))) := by
  obtain ⟨w, hw⟩ := runW_band L n R x hL
  exact Band_Balanced hw

theorem runW_unit_balanced (n : Nat) (R : List (Nat × Nat)) (x : Nat) :
    Balanced 1
      ((runW 1 n (initW 1 R) x).1.S.map (fun p => (p.2.1, p.2.2))) :=
  runW_balanced 1 n R x (by omega)

/-! ### Canonical fuel removes the composition theorem's operational premises -/

/-- Fills never exceed the quantity offered. -/
theorem stepW_le (L : Nat) (st : WState) (x : Nat) : (stepW L st x).2 ≤ x := by
  unfold stepW
  split
  · exact Nat.zero_le _
  · simp only; split <;> simp only <;> omega

/-- A visit conserves remaining book quantity: new remaining size plus the
    visit fill equals old remaining size. -/
theorem stepW_tot_conserve (L : Nat) (st : WState) (x : Nat) :
    totW (stepW L st x).1.S + (stepW L st x).2 = totW st.S := by
  unfold stepW
  cases hfl : findLive st.S with
  | nil => simp
  | cons p T =>
      obtain ⟨id, a, r⟩ := p
      have htot : totW st.S = r + totW T := by
        rw [← findLive_tot st.S, hfl]
        simp [totW]
      simp only
      split
      · rw [totW_append]
        have hsingle : totW [(id, a + min st.lot (min r x),
            r - min st.lot (min r x))] = r - min st.lot (min r x) := by
          simp [totW]
        rw [hsingle]
        rw [htot]
        omega
      · have hcons : totW ((id, a + min st.lot (min r x),
            r - min st.lot (min r x)) :: T) =
            r - min st.lot (min r x) + totW T := by
          simp [totW]
        rw [hcons]
        rw [htot]
        omega

/-- With positive lot size and allowance, every productive visit strictly
    decreases total remaining size. -/
theorem stepW_tot_lt (L : Nat) (st : WState) (x : Nat)
    (_hL : 0 < L) (hlot : 0 < st.lot) (hx : 0 < x) (ht : 0 < totW st.S) :
    totW (stepW L st x).1.S < totW st.S := by
  obtain ⟨p, T, hpt, hlive⟩ := findLive_head st.S ht
  obtain ⟨id, a, r⟩ := p
  have hr : 0 < r := by simp [live] at hlive; exact hlive
  have hfill : 0 < (stepW L st x).2 := by
    unfold stepW
    rw [hpt]
    simp only
    split <;> simp only <;> omega
  have hc := stepW_tot_conserve L st x
  omega

/-- Positive lot allowance is preserved by a productive visit. -/
theorem stepW_lot_pos (L : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) :
    0 < (stepW L st x).1.lot := by
  unfold stepW
  cases hfl : findLive st.S with
  | nil => simpa using hlot
  | cons p T =>
      obtain ⟨id, a, r⟩ := p
      simp only
      split
      · exact hL
      · rename_i hneq
        have hgle : min st.lot (min r x) ≤ st.lot := Nat.min_le_left _ _
        have hne : min st.lot (min r x) ≠ st.lot := by
          intro heq
          have hlr : st.lot ≤ r := by
            have := Nat.min_le_left r x
            omega
          apply hneq
          rw [heq, Nat.min_eq_left hlr]
        exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hgle hne)

theorem runW_lot_pos (L n : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) :
    0 < (runW L n st x).1.lot := by
  induction n generalizing st x with
  | zero => simpa [runW] using hlot
  | succ n ih =>
      simp only [runW]
      by_cases hstop : x = 0 ∨ totW st.S = 0
      · rw [if_pos hstop]
        exact hlot
      · rw [if_neg hstop]
        apply ih
        exact stepW_lot_pos L st x hL hlot

/-- Any run with more fuel than total remaining size reaches a stopped state.
    The proof uses strict descent of remaining size at every productive visit. -/
theorem runW_stops_of_tot_lt_fuel (L n : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) (hfuel : totW st.S < n) :
    Stopped (runW L n st x).1 (runW L n st x).2 := by
  induction n generalizing st x with
  | zero => omega
  | succ n ih =>
      simp only [runW]
      by_cases hstop : x = 0 ∨ totW st.S = 0
      · rw [if_pos hstop]
        exact hstop
      · rw [if_neg hstop]
        apply ih
        · exact stepW_lot_pos L st x hL hlot
        · have hdec := stepW_tot_lt L st x hL hlot (by omega) (by omega)
          omega

/-- Book/contra conservation for a whole fuel-bounded run. -/
theorem runW_tot_conserve (L n : Nat) (st : WState) (x : Nat) :
    totW (runW L n st x).1.S + x =
      totW st.S + (runW L n st x).2 := by
  induction n generalizing st x with
  | zero => simp [runW]
  | succ n ih =>
      simp only [runW]
      by_cases hstop : x = 0 ∨ totW st.S = 0
      · rw [if_pos hstop]
      · rw [if_neg hstop]
        have hs := stepW_tot_conserve L st x
        have hle := stepW_le L st x
        have hr := ih (stepW L st x).1 (x - (stepW L st x).2)
        omega

/-- Canonical execution: total remaining size plus one is sufficient fuel. -/
def runWFull (L : Nat) (st : WState) (x : Nat) : WState × Nat :=
  runW L (totW st.S + 1) st x

theorem runWFull_stopped (L : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) :
    Stopped (runWFull L st x).1 (runWFull L st x).2 := by
  apply runW_stops_of_tot_lt_fuel L (totW st.S + 1) st x hL hlot
  omega

theorem runWFull_allocates_first (L : Nat) (st : WState) (x : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) (hx : x ≤ totW st.S) :
    (runWFull L st x).2 = 0 := by
  have hs := runWFull_stopped L st x hL hlot
  have hc := runW_tot_conserve L (totW st.S + 1) st x
  unfold runWFull at hs ⊢
  rcases hs with hs | hs
  · exact hs
  · omega

/-- **Step composition.**  Either the first step of x and of x+y agree, or the
    step of x is partial and the step of x+y equals the step of y from the
    partial state, with fills adding. -/
theorem stepW_split (L : Nat) (st : WState) (x y : Nat) (ht : 0 < totW st.S) :
    (stepW L st (x + y) = stepW L st x) ∨
    ((stepW L st x).2 = x ∧ 0 < totW (stepW L st x).1.S ∧
      0 < (stepW L st x).1.lot ∧ findLive (stepW L st x).1.S = (stepW L st x).1.S ∧
      (stepW L st (x + y)).1 = (stepW L (stepW L st x).1 y).1 ∧
      (stepW L st (x + y)).2 = x + (stepW L (stepW L st x).1 y).2) := by
  obtain ⟨p, T, hpt, hl⟩ := findLive_head st.S ht
  obtain ⟨id, a, r⟩ := p
  have hr : 0 < r := by simp [live] at hl; exact hl
  by_cases hbig : min st.lot r ≤ x
  · left
    rw [stepW_adv L st id a r T x hpt hbig, stepW_adv L st id a r T (x + y) hpt (by omega)]
  · right
    have hlt : x < min st.lot r := by omega
    rw [stepW_partial L st id a r T x hpt hlt]
    have hl' : live (id, a + x, r - x) = true := by simp [live]; omega
    have hpt' : findLive ((id, a + x, r - x) :: T) = (id, a + x, r - x) :: T :=
      findLive_of_live _ _ hl'
    refine ⟨rfl, ?_, ?_, hpt', ?_⟩
    · show 0 < totW ((id, a + x, r - x) :: T)
      simp only [totW, List.map_cons, List.sum_cons]; omega
    · show 0 < st.lot - x; omega
    · by_cases hadv : min (st.lot - x) (r - x) ≤ y
      · have hxy : min st.lot r ≤ x + y := by clear hpt hpt' hl' hl; omega
        rw [stepW_adv L ⟨(id, a + x, r - x) :: T, st.lot - x⟩ id (a + x) (r - x) T y hpt' hadv]
        rw [stepW_adv L st id a r T (x + y) hpt hxy]
        have e : min st.lot r = x + min (st.lot - x) (r - x) := by clear hpt hpt' hl' hl; omega
        rw [e]
        simp [Nat.add_assoc, Nat.sub_sub]
      · have hlt2 : y < min (st.lot - x) (r - x) := by clear hpt hpt' hl' hl; omega
        have hxy : x + y < min st.lot r := by clear hpt hpt' hl' hl; omega
        rw [stepW_partial L ⟨(id, a + x, r - x) :: T, st.lot - x⟩ id (a + x) (r - x) T y hpt' hlt2]
        rw [stepW_partial L st id a r T (x + y) hpt hxy]
        simp [Nat.add_assoc, Nat.sub_sub]

/-- A zero-quantity step is the identity on a state whose head is live and whose
    lot allowance is positive. -/
theorem stepW_zero (L : Nat) (st : WState) (ht : 0 < totW st.S) (hlot : 0 < st.lot)
    (hfl : findLive st.S = st.S) : stepW L st 0 = (st, 0) := by
  obtain ⟨p, T, hpt, hl⟩ := findLive_head st.S ht
  obtain ⟨id, a, r⟩ := p
  have hr : 0 < r := by simp [live] at hl; exact hl
  rw [stepW_partial L st id a r T 0 hpt (by omega)]
  rw [hfl] at hpt
  cases st with
  | mk S lot =>
      simp only at hpt hlot ⊢
      subst hpt
      simp

/-- **Path independence of the pointer-and-lot wheel.**  Allocating x (fully)
    and then y from the resulting state equals allocating x + y at once. -/
theorem runW_comp (L n₁ n₂ : Nat) (st : WState) (x y : Nat)
    (h1 : (runW L n₁ st x).2 = 0)
    (h2 : Stopped (runW L n₂ (runW L n₁ st x).1 y).1 (runW L n₂ (runW L n₁ st x).1 y).2) :
    runW L (n₁ + n₂) st (x + y) = runW L n₂ (runW L n₁ st x).1 y := by
  induction n₁ generalizing st x with
  | zero =>
      simp only [runW] at h1 h2 ⊢
      subst h1; simp
  | succ n₁ ih =>
      rw [show n₁ + 1 + n₂ = (n₁ + n₂) + 1 by omega]
      simp only [runW] at h1 h2 ⊢
      by_cases hc : x = 0 ∨ totW st.S = 0
      · rw [if_pos hc] at h1 h2 ⊢
        have hx0 : x = 0 := by
          rcases hc with hc | hc
          · exact hc
          · exact h1
        subst hx0
        simp only [Nat.zero_add] at h2 ⊢
        show runW L (n₁ + n₂ + 1) st y = runW L n₂ st y
        rw [show n₁ + n₂ + 1 = n₂ + (n₁ + 1) by omega]
        exact runW_stable L n₂ (n₁ + 1) st y h2
      · rw [if_neg hc] at h1 h2 ⊢
        have hx : 0 < x := by omega
        have ht : 0 < totW st.S := by omega
        have hxy : ¬ (x + y = 0 ∨ totW st.S = 0) := by omega
        rw [if_neg hxy]
        rcases stepW_split L st x y ht with heq | ⟨hg, ht1, hlot1, hfl1, hs, hf⟩
        · rw [heq]
          have hle := stepW_le L st x
          have : x + y - (stepW L st x).2 = (x - (stepW L st x).2) + y := by omega
          rw [this]
          exact ih _ _ h1 h2
        · rw [hs, hf]
          rw [hg] at h1 h2 ⊢
          rw [Nat.sub_self, runW_x0] at h1 h2 ⊢
          simp only at h2 ⊢
          have : x + y - (x + (stepW L (stepW L st x).1 y).2) = y - (stepW L (stepW L st x).1 y).2 := by omega
          rw [this]
          cases n₂ with
          | zero =>
              simp only [runW] at h2 ⊢
              have hy : y = 0 := by
                rcases h2 with h2 | h2
                · exact h2
                · omega
              subst hy
              rw [stepW_zero L _ ht1 hlot1 hfl1]
              simp [runW_x0]
          | succ m =>
              simp only [runW] at h2 ⊢
              by_cases hy : y = 0 ∨ totW (stepW L st x).1.S = 0
              · rw [if_pos hy] at h2 ⊢
                have hy0 : y = 0 := by rcases hy with hy | hy; exact hy; omega
                subst hy0
                rw [stepW_zero L _ ht1 hlot1 hfl1]
                simp
              · rw [if_neg hy] at h2 ⊢
                change runW L (n₁ + m + 1) (stepW L (stepW L st x).1 y).1 (y - (stepW L (stepW L st x).1 y).2) = _
                rw [show n₁ + m + 1 = m + (n₁ + 1) by omega]
                exact runW_stable L m (n₁ + 1) _ _ h2

/-- **Unconditional canonical stream consistency.**  For a positive lot and
    a valid first estate, canonical fuel discharges the completion, stopped,
    and user-supplied fuel premises of `runW_comp`. -/
theorem runWFull_comp (L : Nat) (st : WState) (x y : Nat)
    (hL : 0 < L) (hlot : 0 < st.lot) (hx : x ≤ totW st.S) :
    runWFull L st (x + y) = runWFull L (runWFull L st x).1 y := by
  let n₁ := totW st.S + 1
  let r₁ := runW L n₁ st x
  let n₂ := totW r₁.1.S + 1
  have h1 : r₁.2 = 0 := by
    dsimp [r₁, n₁]
    exact runWFull_allocates_first L st x hL hlot hx
  have hlot1 : 0 < r₁.1.lot := by
    dsimp [r₁, n₁]
    exact runW_lot_pos L (totW st.S + 1) st x hL hlot
  have h2 : Stopped (runW L n₂ r₁.1 y).1 (runW L n₂ r₁.1 y).2 := by
    dsimp [n₂]
    apply runW_stops_of_tot_lt_fuel L (totW r₁.1.S + 1) r₁.1 y hL hlot1
    omega
  have hcomp := runW_comp L n₁ n₂ st x y h1 h2
  have hjointStop := runWFull_stopped L st (x + y) hL hlot
  have hstable := runW_stable L (totW st.S + 1) n₂ st (x + y) hjointStop
  dsimp [runWFull]
  dsimp [n₁, r₁, n₂] at hcomp hstable ⊢
  exact hstable.symm.trans hcomp

/-- **Canonical stream consistency on every reachable state.**  When `st` is
    obtained by running the wheel from `initW`, positivity of the current
    allowance is an invariant rather than an input.  Thus only a positive lot
    and an admissible first estate remain as hypotheses. -/
theorem runWFull_comp_reachable (L n : Nat) (R : List (Nat × Nat))
    (z x y : Nat) (hL : 0 < L)
    (hx : x ≤ totW (runW L n (initW L R) z).1.S) :
    runWFull L (runW L n (initW L R) z).1 (x + y) =
      runWFull L (runWFull L (runW L n (initW L R) z).1 x).1 y := by
  apply runWFull_comp L (runW L n (initW L R) z).1 x y hL
  · exact runW_lot_pos L n (initW L R) z hL (by simpa [initW] using hL)
  · exact hx

end Rule737
