import Nest.SessionUtils
import Nest.MonitorToolkit

/-!
# Drainability: drainability duality (`Can` iff `¬Cannot`).

Positive drainability (`CanAlwaysDrainInternalDeepRec`) states that a session
type can always drain its queue: `intC` needs every branch to drain under a
fresh queue, `extC` needs either an absent role with one draining branch or a
dequeue step to a draining target, and `tRec` unfolds. Failure
(`CannotAlwaysDrainInternalDeepSeen` / `CannotAlwaysDrainInternalDeepRec`)
dualizes this with a visited set plus a `cut` rule closing revisits.

Main results: the backward construction `drainrec_can_of_not_cannot`
(an open failure tableau builds drainage; needs `Monitorable` for the
termination measure) and the forward `drainrec_not_cannot_of_can` (a drainage
derivation builds a broad tree whose excision and transport refute every
failure tableau; needs only `WellFormed`), assembled into `drainrec_iff`.
-/

namespace Drainability

section DrainabilityQueue

/-- A dequeue scan skips a `p`-free prefix and fires at the target message,
    returning the queue with that message removed. -/
theorem dequeue_skip_seen {p : Role} {lab : Lab} {S : DataSort}
    {rest : Queue} {acc seen : Queue} (hseen : ∀ m ∈ seen, m.1 ≠ p) :
    Queue.dequeue.go acc (seen ++ QueueMessage.msg p lab S :: rest)
      (QueueMessage.msg p lab S) = some (acc ++ seen ++ rest) := by
  revert hseen
  induction seen generalizing acc with
  | nil =>
    intro hseen
    simp [Queue.dequeue.go]
  | cons s0 seen' ih =>
    intro hseen
    have h0 : s0.1 ≠ p := hseen _ (List.mem_cons.mpr (Or.inl rfl))
    have hne : s0 ≠ QueueMessage.msg p lab S := by
      intro hcon
      rw [hcon] at h0
      simp at h0
    have h0' : s0.1 ≠ (QueueMessage.msg p lab S).1 := h0
    have hrest : ∀ m ∈ seen', m.1 ≠ p := fun m hm =>
      hseen m (List.mem_cons.mpr (Or.inr hm))
    have hstep := ih (acc := acc ++ [s0]) hrest
    simp only [List.cons_append] at *
    simp only [Queue.dequeue.go, hne, h0'] at *
    simpa [List.append_assoc] using hstep

end DrainabilityQueue

section DrainabilityBranches

/-- Free variables of an internal branch target occur in the whole choice. -/
theorem fv_mem_of_mem_intBranches
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2.2) :
    y ∈ SessionType.fv (SessionType.internalChoice branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- Free variables of an external branch target occur in the whole choice. -/
theorem fv_mem_of_mem_extBranches
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2) :
    y ∈ SessionType.fv (SessionType.externalChoice p branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- Branch targets of a well-formed internal choice are well-formed. -/
theorem wf_of_mem_intBranches
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.internalChoice branches).WellFormed) :
    x.2.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | internalChoice _ _ hbr =>
    cases hCt with
    | internalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_intBranches hmem hmy
        have hCl' : SessionType.fv (SessionType.internalChoice branches) = [] :=
          hCl
        rw [hCl'] at hpar
        simp at hpar

/-- Branch targets of a well-formed external choice are well-formed. -/
theorem wf_of_mem_extBranches
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.externalChoice p branches).WellFormed) :
    x.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | externalChoice _ _ hbr =>
    cases hCt with
    | externalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_extBranches (p := p) hmem hmy
        have hCl' : SessionType.fv (SessionType.externalChoice p branches) = [] :=
          hCl
        rw [hCl'] at hpar
        simp at hpar

end DrainabilityBranches

section DrainabilityMonitorable

/-- Pruning reachability (single steps): branch descent into choice targets,
    and recursion unfolding. `tEnd`/`tVar` have no steps. -/
inductive PruneStep : SessionType → SessionType → Prop where
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches) :
      PruneStep (SessionType.internalChoice branches) x.2.2.2
  | extC {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {x : Lab × DataSort × SessionType} (hmem : x ∈ branches) :
      PruneStep (SessionType.externalChoice p branches) x.2.2
  | trec {X : String} {B : SessionType} :
      PruneStep (SessionType.tRec X B)
        (substSessionType B X (SessionType.tRec X B))

/-- A session type is monitorable when its pruning-reachability closure is
    finite. The backward construction below uses the closure as the finite
    cover driving its termination measure. -/
def Monitorable (T : SessionType) : Prop :=
  {U : SessionType | Relation.ReflTransGen PruneStep T U}.Finite

/-- Decidable equality on session types (classical; enables finite-set
    operations over pruning closures). -/
noncomputable instance : DecidableEq SessionType :=
  fun a b => Classical.dec (a = b)

/-- Single-step reachability into the closure (internal branch targets). -/
theorem PruneStep.rtc_intC_mem
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    Relation.ReflTransGen PruneStep
      (SessionType.internalChoice branches) x.2.2.2 :=
  Relation.ReflTransGen.single (PruneStep.intC hmem)

/-- Single-step reachability into the closure (external branch targets). -/
theorem PruneStep.rtc_extC_mem {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    Relation.ReflTransGen PruneStep
      (SessionType.externalChoice p branches) x.2.2 :=
  Relation.ReflTransGen.single (PruneStep.extC hmem)

/-- Single-step reachability into the closure (recursion unfolding). -/
theorem PruneStep.rtc_trec_unfold (X : String) (B : SessionType) :
    Relation.ReflTransGen PruneStep (SessionType.tRec X B)
      (substSessionType B X (SessionType.tRec X B)) :=
  Relation.ReflTransGen.single PruneStep.trec

/-- Monitorability transports down reachability: the closure of a reachable
    state is contained in the closure of the source (by transitivity). -/
theorem Monitorable.mono {T U : SessionType}
    (h : Relation.ReflTransGen PruneStep T U) (hFin : Monitorable T) :
    Monitorable U :=
  hFin.subset (fun _ hV => h.trans hV)

/-- Single-step transport of monitorability. -/
theorem Monitorable.of_step {T U : SessionType}
    (h : PruneStep T U) (hFin : Monitorable T) : Monitorable U :=
  hFin.mono (Relation.ReflTransGen.single h)

/-- First-step case split at an `internalChoice` head: any multi-step
    reachability either stays (refl) or passes through a branch target
    (only the `intC` constructor can fire at such a head). -/
theorem PruneStep.head_intC_inv {branches : List (Role × Lab × DataSort × SessionType)}
    {V : SessionType}
    (h : Relation.ReflTransGen PruneStep (SessionType.internalChoice branches) V) :
    V = SessionType.internalChoice branches ∨
      ∃ x ∈ branches, Relation.ReflTransGen PruneStep x.2.2.2 V := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hRTC hStep ih =>
    rcases ih with rfl | ⟨x, hmem, hRTCx⟩
    · cases hStep with
      | @intC _ x hmem =>
        exact Or.inr ⟨x, hmem, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨x, hmem, hRTCx.tail hStep⟩

/-- First-step case split at an `externalChoice` head (mirror of
    `head_intC_inv`; only the `extC` constructor fires there). -/
theorem PruneStep.head_extC_inv {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {V : SessionType}
    (h : Relation.ReflTransGen PruneStep (SessionType.externalChoice p branches) V) :
    V = SessionType.externalChoice p branches ∨
      ∃ x ∈ branches, Relation.ReflTransGen PruneStep x.2.2 V := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hRTC hStep ih =>
    rcases ih with rfl | ⟨x, hmem, hRTCx⟩
    · cases hStep with
      | @extC _ _ x hmem =>
        exact Or.inr ⟨x, hmem, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨x, hmem, hRTCx.tail hStep⟩

end DrainabilityMonitorable

section DrainabilityFailure

/-- Drain-failure tableaux with a visited set plus a `cut` rule closing
    revisits. `intC_blocked` exhibits a queued message matching a branch
    sender (a send can fire); `extC_missed` exhibits an oldest message whose
    key is absent; `intC_adv`/`extC_allFail` propagate failure from branch
    targets (one failing target, respectively all of them); `extC_deq`
    follows a dequeue step; `trec_new`/`trec_empty` unfold recursion
    (extending the visited set at fresh nonempty-queue points); `cut` closes
    exact revisits; `tEnd`/`tVar` are stuck with a nonempty queue. -/
inductive CannotAlwaysDrainInternalDeepSeen :
    List (SessionType × Queue) → SessionType → Queue → Prop where
  | cut (seen : List (SessionType × Queue)) (T : SessionType) (Q : Queue)
      (hmem : (T, Q) ∈ seen) :
      CannotAlwaysDrainInternalDeepSeen seen T Q
  | tEnd (seen : List (SessionType × Queue)) (Q : Queue)
      (hne : Q ≠ []) :
      CannotAlwaysDrainInternalDeepSeen seen SessionType.tEnd Q
  | tvar (seen : List (SessionType × Queue)) (X : String) (Q : Queue)
      (hne : Q ≠ []) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.tVar X) Q
  | intC_blocked (seen : List (SessionType × Queue))
      (branches : List (Role × Lab × DataSort × SessionType))
      (Q : Queue) (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
      (m : QueueMessage)
      (hmem : (p, lab, S, T') ∈ branches) (hmQ : m ∈ Q) (heq : m.1 = p) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.internalChoice branches) Q
  | extC_missed (seen : List (SessionType × Queue)) (p : Role)
      (branches : List (Lab × DataSort × SessionType)) (Q : Queue)
      (lab : Lab) (S : DataSort)
      (holdest : oldest_from p Q (QueueMessage.msg p lab S))
      (hmiss : ∀ (T' : SessionType), (lab, S, T') ∉ branches) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.externalChoice p branches) Q
  | trec_new (seen : List (SessionType × Queue)) (X : String) (B : SessionType)
      (Q : Queue)
      (hnmem : (SessionType.tRec X B, Q) ∉ seen) (hne : Q ≠ [])
      (hsub : CannotAlwaysDrainInternalDeepSeen
        ((SessionType.tRec X B, Q) :: seen)
        (substSessionType B X (SessionType.tRec X B)) Q) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.tRec X B) Q
  | trec_empty (seen : List (SessionType × Queue)) (X : String) (B : SessionType)
      (hsub : CannotAlwaysDrainInternalDeepSeen seen
        (substSessionType B X (SessionType.tRec X B)) []) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.tRec X B) []
  | intC_adv (seen : List (SessionType × Queue))
      (branches : List (Role × Lab × DataSort × SessionType))
      (Q : Queue) (x : Role × Lab × DataSort × SessionType)
      (hmemB : x ∈ branches)
      (hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
      (hsub : CannotAlwaysDrainInternalDeepSeen seen x.2.2.2 Q) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.internalChoice branches) Q
  | extC_allFail (seen : List (SessionType × Queue)) (p : Role)
      (branches : List (Lab × DataSort × SessionType)) (Q : Queue)
      (hne : branches ≠ [])
      (habs : ∀ m ∈ Q, m.1 ≠ p)
      (hall : ∀ x ∈ branches,
        CannotAlwaysDrainInternalDeepSeen seen x.2.2 Q) :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.externalChoice p branches) Q
  | extC_deq (seen : List (SessionType × Queue)) (p : Role)
      (branches : List (Lab × DataSort × SessionType))
      (Q Q' : Queue) (lab : Lab) (S : DataSort) (T' : SessionType)
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
      (hsub : CannotAlwaysDrainInternalDeepSeen seen T' Q') :
      CannotAlwaysDrainInternalDeepSeen seen (SessionType.externalChoice p branches) Q

/-- Drain-failure with the visited set hidden: the empty-seen specialisation
    of the tableau above. -/
def CannotAlwaysDrainInternalDeepRec (T : SessionType) (Q : Queue) : Prop :=
  CannotAlwaysDrainInternalDeepSeen [] T Q

/-- Drainage-failure needs a nonempty queue (given a seen-set with no
    empty-queue pairs): every constructor either demands `≠[]`, exhibits a
    queued message, or recurses on strict sub-derivations. In particular
    failure at `[]` is impossible at top level. -/
theorem cannotRec_nil_absurd {S : List (SessionType × Queue)}
    {T : SessionType} {Q : Queue}
    (hS : ∀ p ∈ S, p.2 ≠ []) (d : CannotAlwaysDrainInternalDeepSeen S T Q)
    (hQ : Q = []) :
    False := by
  induction d with
  | cut s T Q hmem =>
    subst hQ
    exact (hS _ hmem) rfl
  | tEnd s Q hne =>
    subst hQ
    exact hne rfl
  | tvar s X Q hne =>
    subst hQ
    exact hne rfl
  | intC_blocked s branches Q p lab S T' m hmem hmQ heq =>
    subst hQ
    simp at hmQ
  | extC_missed s p branches Q lab S holdest hmiss =>
    subst hQ
    obtain ⟨pre, post, hsplit, -⟩ := holdest
    have hlen := congrArg List.length hsplit
    simp at hlen
  | trec_new s X B Q hnmem hne hsub _ih =>
    subst hQ
    exact hne rfl
  | trec_empty s X B hsub ih =>
    exact ih hS rfl
  | intC_adv s branches Q x hmemB hfresh hsub ih =>
    subst hQ
    exact ih hS rfl
  | extC_allFail s p branches Q hne habs hall ih =>
    subst hQ
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    exact ih x hx hS rfl
  | extC_deq s p branches Q Q' lab S T' hmem hQd hsub _ih =>
    subst hQ
    simp [Queue.dequeue, Queue.dequeue.go] at hQd

end DrainabilityFailure

section DrainabilityPositive

/-- Positive drainability, dual of the failure tableau: `intC` needs every
    branch to drain under a fresh queue; `extC` with an absent role needs one
    draining branch, and with a dequeueable message steps to a draining
    target; `tRec` unfolds (matching single-step dynamics); the empty queue
    always drains. Deliberately seen-free: `nil` short-circuits every `[]`
    state, and `trec_step` requires a nonempty queue. -/
inductive CanAlwaysDrainInternalDeepRec : SessionType → Queue → Prop where
  | drained_nil (T : SessionType) :
      CanAlwaysDrainInternalDeepRec T []
  | intC_drain (branches : List (Role × Lab × DataSort × SessionType))
      (Q : Queue)
      (hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
      (hall : ∀ x ∈ branches, CanAlwaysDrainInternalDeepRec x.2.2.2 Q) :
      CanAlwaysDrainInternalDeepRec (SessionType.internalChoice branches) Q
  | extC_spec (p : Role)
      (branches : List (Lab × DataSort × SessionType)) (Q : Queue)
      (habs : ∀ m ∈ Q, m.1 ≠ p)
      (x : Lab × DataSort × SessionType) (hmemB : x ∈ branches)
      (hsub : CanAlwaysDrainInternalDeepRec x.2.2 Q) :
      CanAlwaysDrainInternalDeepRec (SessionType.externalChoice p branches) Q
  | extC_deq (p : Role)
      (branches : List (Lab × DataSort × SessionType)) (Q Q' : Queue)
      (lab : Lab) (S : DataSort) (T' : SessionType)
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
      (hsub : CanAlwaysDrainInternalDeepRec T' Q') :
      CanAlwaysDrainInternalDeepRec (SessionType.externalChoice p branches) Q
  | trec_step (X : String) (B : SessionType) (Q : Queue) (hne : Q ≠ [])
      (hsub : CanAlwaysDrainInternalDeepRec
        (substSessionType B X (SessionType.tRec X B)) Q) :
      CanAlwaysDrainInternalDeepRec (SessionType.tRec X B) Q

end DrainabilityPositive

section DrainabilityBackward

/-- Types visited at the current queue (exact-`Q` slice of `visited`).
    The termination-measure remainder is the closure minus this set. -/
noncomputable def visitedTypesAt (visited : List (SessionType × Queue)) (Q : Queue) :
    Finset SessionType :=
  ((visited.toFinset.filter (fun m => m.2 = Q)).image Prod.fst)

/-- Membership in the visited-types finset unfolds to list membership at the same queue. -/
theorem mem_visitedTypesAt {visited : List (SessionType × Queue)} {Q : Queue}
    {T : SessionType} :
    T ∈ visitedTypesAt visited Q ↔ (T, Q) ∈ visited := by
  unfold visitedTypesAt
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hmem, hfst⟩
    have hmemV : m ∈ visited.toFinset := (Finset.mem_filter.mp hmem).1
    have hQeq : m.2 = Q := (Finset.mem_filter.mp hmem).2
    have hmemVl : m ∈ visited := List.mem_toFinset.mp hmemV
    have hmeq : m = (T, Q) := Prod.ext hfst hQeq
    rw [hmeq] at hmemVl
    exact hmemVl
  · intro hmem
    refine ⟨(T, Q), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [List.mem_toFinset]
    exact hmem

/-- Extending `visited` at a fresh closure type strictly shrinks the remainder. -/
theorem card_visitedTypesAt_extend_lt {C : Finset SessionType}
    {visited : List (SessionType × Queue)} {Q : Queue} {T : SessionType}
    (hTC : T ∈ C) (hfr : (T, Q) ∉ visited) :
    (C \ visitedTypesAt ((T, Q) :: visited) Q).card <
      (C \ visitedTypesAt visited Q).card := by
  have hEq : visitedTypesAt ((T, Q) :: visited) Q =
      insert T (visitedTypesAt visited Q) := by
    ext U
    rw [mem_visitedTypesAt]
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with heq | hmemV
      · have hUT : U = T := congrArg Prod.fst heq
        exact Finset.mem_insert.mpr (Or.inl hUT)
      · exact Finset.mem_insert.mpr (Or.inr (mem_visitedTypesAt.mpr hmemV))
    · intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with rfl | hmemO
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (mem_visitedTypesAt.mp hmemO))
  rw [hEq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · exact Finset.sdiff_subset_sdiff (fun _ h => h) (fun _ h => Finset.mem_insert_of_mem h)
  · intro heq
    have h1 : T ∈ C \ visitedTypesAt visited Q :=
      Finset.mem_sdiff.mpr ⟨hTC, fun hT => hfr (mem_visitedTypesAt.mp hT)⟩
    have h2 : T ∉ C \ insert T (visitedTypesAt visited Q) := by
      intro hcon
      exact (Finset.mem_sdiff.mp hcon).2 (Finset.mem_insert_self T _)
    rw [heq] at h2
    exact h2 h1

attribute [irreducible] visitedTypesAt

/-- Oldest matching message dequeues (a scan cannot block on a same-sender
    mismatch: oldest-from-`p` means no `p` message precedes it). -/
theorem deq_of_oldest {p : Role} {lab : Lab} {S : DataSort} {Q : Queue}
    (hold : oldest_from p Q (QueueMessage.msg p lab S)) :
    ∃ Q', Q.dequeue (QueueMessage.msg p lab S) = some Q' := by
  obtain ⟨pre, post, heqQ, -, hfree⟩ := hold
  refine ⟨[] ++ pre ++ post, ?_⟩
  show Queue.dequeue.go [] Q (QueueMessage.msg p lab S) = some _
  rw [heqQ]
  exact dequeue_skip_seen hfree

/-- Backward construction: an open failure tableau (`¬Seen`) builds a
    drainage derivation. Well-founded on queue length, closure remainder,
    and type size, with a threaded `visited` set: `Q = []` closes by `nil`;
    `Q ≠ []`-revisits close by `cut`-contradiction; stuck ends close by
    contradiction via their constructors; `trec` extends the visited set
    (remainder drops); `deq` shrinks the queue; branches shrink. -/
private theorem buildCanRec (C : Finset SessionType)
    (T₀ : SessionType) (hCU : ∀ U : SessionType, U ∈ C ↔ Relation.ReflTransGen PruneStep T₀ U) :
    ∀ (visited : List (SessionType × Queue)) (T : SessionType) (Q : Queue)
    (hN : ¬ CannotAlwaysDrainInternalDeepSeen visited T Q)
    (hWF : T.WellFormed) (hRTC : Relation.ReflTransGen PruneStep T₀ T),
    CanAlwaysDrainInternalDeepRec T Q
  | visited, T, [], _, _, _ =>
      CanAlwaysDrainInternalDeepRec.drained_nil _
  | visited, SessionType.tEnd, mh :: Qt, hN, hWF, hRTC => by
          have hneQ : (mh :: Qt) ≠ [] :=
            List.ne_nil_of_mem (List.mem_cons.mpr (Or.inl rfl))
          have hR : CannotAlwaysDrainInternalDeepSeen visited
              SessionType.tEnd (mh :: Qt) :=
            CannotAlwaysDrainInternalDeepSeen.tEnd _ _ hneQ
          exact absurd hR hN
  | visited, SessionType.tVar X, mh :: Qt, hN, hWF, hRTC => by
          have hneQ : (mh :: Qt) ≠ [] :=
            List.ne_nil_of_mem (List.mem_cons.mpr (Or.inl rfl))
          have hR : CannotAlwaysDrainInternalDeepSeen visited
              (SessionType.tVar X) (mh :: Qt) :=
            CannotAlwaysDrainInternalDeepSeen.tvar _ _ _ hneQ
          exact absurd hR hN
  | visited, SessionType.internalChoice branches, mh :: Qt, hN, hWF, hRTC => by
          rcases Classical.em
              (∃ br ∈ branches, ∃ mq ∈ (mh :: Qt), mq.1 = br.1) with hB | hNB
          · obtain ⟨br, hmemB, mq, hmemQ, heqM⟩ := hB
            obtain ⟨p, lab, S, T0⟩ := br
            have heqM' : mq.1 = p := heqM
            have hR : CannotAlwaysDrainInternalDeepSeen visited
                (SessionType.internalChoice branches) (mh :: Qt) :=
              CannotAlwaysDrainInternalDeepSeen.intC_blocked _ _ _ _ _ _ _ _
                hmemB hmemQ heqM'
            exact absurd hR hN
          · have hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
                (r', l', s', U) ∈ branches → ∀ mq ∈ (mh :: Qt), mq.1 ≠ r' := by
              intro r' l' s' U' hmemU mq hmemQ heqM
              exact hNB ⟨(r', l', s', U'), hmemU, mq, hmemQ, heqM⟩
            have hall : ∀ x ∈ branches,
                CanAlwaysDrainInternalDeepRec x.2.2.2 (mh :: Qt) := by
              intro x hx
              obtain ⟨p, lab, S, T0⟩ := x
              have hNx : ¬ CannotAlwaysDrainInternalDeepSeen visited T0 (mh :: Qt) :=
                fun hRb => hN
                  (CannotAlwaysDrainInternalDeepSeen.intC_adv _ _ _ _ hx hfresh hRb)
              have hWFx : T0.WellFormed := wf_of_mem_intBranches hx hWF
              have hRTCx : Relation.ReflTransGen PruneStep T₀ T0 :=
                hRTC.trans (PruneStep.rtc_intC_mem hx)
              have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
                sizeOf_SessionType_lt_sizeOf_internalChoice hx
              show CanAlwaysDrainInternalDeepRec T0 (mh :: Qt)
              exact buildCanRec C T₀ hCU visited T0 (mh :: Qt) hNx hWFx hRTCx
            exact CanAlwaysDrainInternalDeepRec.intC_drain _ _ hfresh hall
  | visited, SessionType.externalChoice p branches, mh :: Qt, hN, hWF, hRTC => by
          rcases Classical.em (∀ mq ∈ (mh :: Qt), mq.1 ≠ p) with habs | hnabs
          · rcases Classical.em (∃ x ∈ branches,
                ¬ CannotAlwaysDrainInternalDeepSeen visited x.2.2 (mh :: Qt)) with
              hex | hnhex
            · obtain ⟨x, hmemB, hNx⟩ := hex
              obtain ⟨lab, S, T'⟩ := x
              have hNx' : ¬ CannotAlwaysDrainInternalDeepSeen visited T' (mh :: Qt) := hNx
              have hWFx : T'.WellFormed := wf_of_mem_extBranches hmemB hWF
              have hRTCx : Relation.ReflTransGen PruneStep T₀ T' :=
                hRTC.trans (PruneStep.rtc_extC_mem hmemB)
              have hlt : sizeOf T' < sizeOf (SessionType.externalChoice p branches) :=
                sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
              have hCanX := buildCanRec C T₀ hCU visited T' (mh :: Qt) hNx' hWFx hRTCx
              exact CanAlwaysDrainInternalDeepRec.extC_spec _ _ _ habs _ hmemB hCanX
            · have hAll : ∀ x ∈ branches,
                  CannotAlwaysDrainInternalDeepSeen visited x.2.2 (mh :: Qt) := by
                intro x hx
                by_contra hnx
                exact hnhex ⟨x, hx, hnx⟩
              have hne : branches ≠ [] := hWF.1.ne_of_externalChoice
              have hR : CannotAlwaysDrainInternalDeepSeen visited
                  (SessionType.externalChoice p branches) (mh :: Qt) :=
                CannotAlwaysDrainInternalDeepSeen.extC_allFail _ _ _ _ hne habs hAll
              exact absurd hR hN
          · have hex_mem : ∃ mq ∈ (mh :: Qt), mq.1 = p := by
              by_contra hcon
              apply hnabs
              intro mq hmemQ
              intro heqM
              exact hcon ⟨mq, hmemQ, heqM⟩
            obtain ⟨m₀, hOld, hm10⟩ := oldest_of_mem _ _ hex_mem
            obtain ⟨p', lab₀, S₀⟩ := m₀
            have hpeq : p' = p := hm10
            rw [hpeq] at hOld
            obtain ⟨pre, post, hsplit, -, hfree⟩ := hOld
            have holdQOF : oldest_from p (mh :: Qt) (QueueMessage.msg p lab₀ S₀) :=
              ⟨pre, post, hsplit, rfl, hfree⟩
            rcases Classical.em (∃ T', (lab₀, S₀, T') ∈ branches) with hkey | hnkey
            · obtain ⟨T', hmem⟩ := hkey
              obtain ⟨Qd, hQd⟩ := deq_of_oldest holdQOF
              have hdrop : Qd.length + 1 = (mh :: Qt).length :=
                Queue.dequeue_length_drop hQd
              have hNT' : ¬ CannotAlwaysDrainInternalDeepSeen visited T' Qd :=
                fun hRT' => hN
                  (CannotAlwaysDrainInternalDeepSeen.extC_deq _ _ _ _ _ _ _ _ hmem hQd
                    hRT')
              have hWFT' : T'.WellFormed := wf_of_mem_extBranches hmem hWF
              have hRTCT' : Relation.ReflTransGen PruneStep T₀ T' :=
                hRTC.trans (PruneStep.rtc_extC_mem hmem)
              have hCanT' := buildCanRec C T₀ hCU visited T' Qd hNT' hWFT' hRTCT'
              exact CanAlwaysDrainInternalDeepRec.extC_deq _ _ _ _ _ _ _ hmem hQd
                hCanT'
            · have hmiss : ∀ T', (lab₀, S₀, T') ∉ branches := by
                intro T'' hmem''
                exact hnkey ⟨T'', hmem''⟩
              have hR : CannotAlwaysDrainInternalDeepSeen visited
                  (SessionType.externalChoice p branches) (mh :: Qt) :=
                CannotAlwaysDrainInternalDeepSeen.extC_missed _ _ _ _ _ _ holdQOF hmiss
              exact absurd hR hN
  | visited, SessionType.tRec X B, mh :: Qt, hN, hWF, hRTC => by
          rcases Classical.em
              ((SessionType.tRec X B, mh :: Qt) ∈ visited) with hmemV | hfrV
          · have hR : CannotAlwaysDrainInternalDeepSeen visited
                (SessionType.tRec X B) (mh :: Qt) :=
              CannotAlwaysDrainInternalDeepSeen.cut _ _ _ hmemV
            exact absurd hR hN
          · have hNsub : ¬ CannotAlwaysDrainInternalDeepSeen
                (((SessionType.tRec X B, mh :: Qt)) :: visited)
                (substSessionType B X (SessionType.tRec X B)) (mh :: Qt) :=
              fun hRs => hN
                (CannotAlwaysDrainInternalDeepSeen.trec_new _ _ _ _ hfrV (List.ne_nil_of_mem (List.mem_cons.mpr (Or.inl rfl))) hRs)
            have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
              SessionType.wellFormedUnfold hWF
                (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
            have hRTCsub : Relation.ReflTransGen PruneStep T₀
                (substSessionType B X (SessionType.tRec X B)) :=
              hRTC.trans (PruneStep.rtc_trec_unfold X B)
            have hTC : (SessionType.tRec X B) ∈ C := (hCU _).mpr hRTC
            have hCanS := buildCanRec C T₀ hCU
              (((SessionType.tRec X B, mh :: Qt)) :: visited)
              (substSessionType B X (SessionType.tRec X B)) (mh :: Qt)
              hNsub hWFsub hRTCsub
            exact CanAlwaysDrainInternalDeepRec.trec_step _ _ _ (List.ne_nil_of_mem (List.mem_cons.mpr (Or.inl rfl))) hCanS
  termination_by visited T Q _ _ _ => (Q.length, ((C \ visitedTypesAt visited Q).card), sizeOf T)
  decreasing_by
    all_goals first
      | (exact Prod.Lex.left _ _ (by omega))
      | (exact Prod.Lex.right _ (Prod.Lex.left _ _ (card_visitedTypesAt_extend_lt hTC hfrV)))
      | (exact Prod.Lex.right _ (Prod.Lex.right _ (by assumption)))

end DrainabilityBackward

section DrainabilityIffBackward

/-- Backward direction: an open failure tableau builds a drainage derivation.
    The finite pruning closure (`Monitorable`) supplies the cover driving the
    construction's termination measure; `WellFormed` threads through. -/
theorem drainrec_can_of_not_cannot {T : SessionType} {Q : Queue}
    (hWF : T.WellFormed) (hMon : Monitorable T)
    (hN : ¬ CannotAlwaysDrainInternalDeepRec T Q) :
    CanAlwaysDrainInternalDeepRec T Q := by
  obtain ⟨C, hCfin⟩ := hMon.exists_finset_coe
  have hCU : ∀ U : SessionType, U ∈ C ↔ Relation.ReflTransGen PruneStep T U := by
    intro U
    constructor
    · intro hmem
      have hmemS : U ∈ (↑C : Set SessionType) := Finset.mem_coe.mpr hmem
      rw [hCfin] at hmemS
      exact hmemS
    · intro hrtc
      have hmemS : U ∈ ({U : SessionType | Relation.ReflTransGen PruneStep T U} : Set SessionType) :=
        hrtc
      rw [←hCfin] at hmemS
      exact Finset.mem_coe.mp hmemS
  have hRTC0 : Relation.ReflTransGen PruneStep T T :=
    Relation.ReflTransGen.refl
  exact buildCanRec C T hCU [] T Q hN hWF hRTC0
end DrainabilityIffBackward

section DrainabilityDequeue

/-- A successful dequeue fires the oldest message of its sender (the scan
    prefix is sender-free). -/
theorem dequeue_some_oldest_from {Q Q' : Queue} {p : Role} {lab : Lab} {S : DataSort}
    (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q') :
    oldest_from p Q (QueueMessage.msg p lab S) := by
  obtain ⟨seen, left, hQeq, -, hfree⟩ := queue_dequeue_some_iff hQ
  rw [List.append_assoc] at hQeq
  exact ⟨seen, left, hQeq, rfl, hfree⟩

/-- `NoDupl` external-choice labels pin branch targets: same key in the same
    branch list means the same target. -/
theorem ext_target_unique_aux
    : ∀ (bs : List (Lab × DataSort × SessionType))
    (lab : Lab) (S : DataSort) (T1 T2 : SessionType),
    (List.map (fun x : Lab × DataSort × SessionType => x.1) bs).Nodup →
    (lab, S, T1) ∈ bs → (lab, S, T2) ∈ bs → T1 = T2 := by
  intro bs
  induction bs with
  | nil =>
    intro lab S T1 T2 hn h1 h2
    simp at h1
  | cons b bs ih =>
    intro lab S T1 T2 hn h1 h2
    rw [List.mem_cons] at h1 h2
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hmem, hnod⟩ := hn
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl, rfl⟩ := h2
        rfl
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        have hcon : lab ∈
            List.map (fun x : Lab × DataSort × SessionType => x.1) bs :=
          List.mem_map.mpr ⟨(lab, S, T2), h2, rfl⟩
        exact absurd hcon hmem
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl⟩ := h2
        have hcon : lab ∈
            List.map (fun x : Lab × DataSort × SessionType => x.1) bs :=
          List.mem_map.mpr ⟨(lab, S, T1), h1, rfl⟩
        exact absurd hcon hmem
      · exact ih _ _ _ _ hnod h1 h2

/-- `NoDupl` external choices have unique targets per key. -/
theorem ext_target_unique {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T1 T2 : SessionType}
    (hND : SessionType.NoDupl (SessionType.externalChoice p branches))
    (h1 : (lab, S, T1) ∈ branches) (h2 : (lab, S, T2) ∈ branches) :
    T1 = T2 := by
  cases hND with
  | externalChoice h_nodup h_ne h_branches =>
    exact ext_target_unique_aux _ _ _ _ _ h_nodup h1 h2

end DrainabilityDequeue

section DrainabilityBroad

/-- State-pair abbreviation for the broad-tree development below. -/
private abbrev stQueue := SessionTypeWithQueue

/-- Broad trees: the same shape as `CanAlwaysDrainInternalDeepRec` derivations,
    but as state trees over
    type-with-queue pairs with seen-threading and no freshness constraints
    (repeats allowed; excision below makes them path-fresh). -/
inductive BroadTree : List stQueue → stQueue → Prop where
  | leaf (seen stq) : stq.2 = [] → BroadTree seen stq
  | intC_node {seen branches Q}
      (hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
      (hall : ∀ x ∈ branches,
        BroadTree ((SessionType.internalChoice branches, Q) :: seen) (x.2.2.2, Q)) :
      BroadTree seen (SessionType.internalChoice branches, Q)
  | spec_node {seen p branches Q T' lab S}
      (hAbs : ∀ m ∈ Q, m.1 ≠ p) (hmem : (lab, S, T') ∈ branches)
      (t : BroadTree ((SessionType.externalChoice p branches, Q) :: seen) (T', Q)) :
      BroadTree seen (SessionType.externalChoice p branches, Q)
  | deq_node {seen p branches Q Q' lab S T'}
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
      (t : BroadTree ((SessionType.externalChoice p branches, Q) :: seen) (T', Q')) :
      BroadTree seen (SessionType.externalChoice p branches, Q)
  | unfold_node {seen T U Q}
      (hU : Unfold1 T U)
      (t : BroadTree ((T, Q) :: seen) (U, Q)) :
      BroadTree seen (T, Q)

/-- Broad soundness: every `CanAlwaysDrainInternalDeepRec` derivation builds a broad tree
    (seen-threading is free — no freshness to discharge). -/
theorem broad_soundness : ∀ {T : SessionType} {Q : Queue} (seen : List stQueue),
    CanAlwaysDrainInternalDeepRec T Q → BroadTree seen (T, Q) := by
  intro T Q seen h
  induction h generalizing seen with
  | drained_nil T =>
    exact BroadTree.leaf _ _ rfl
  | intC_drain branches Q hfresh hall ih =>
    exact BroadTree.intC_node hfresh (fun x hx => ih x hx _)
  | extC_spec p branches Q habs x hmemB hsub ih =>
    obtain ⟨lab, S, T'⟩ := x
    exact BroadTree.spec_node habs hmemB (ih _)
  | extC_deq p branches Q Q' lab S T' hmem hQ hsub ih =>
    exact BroadTree.deq_node hmem hQ (ih _)
  | trec_step X B Q hne hsub ih =>
    exact BroadTree.unfold_node Unfold1.tRec (ih _)

/-- Simple broad drain trees: like `BroadTree` but with the seen-set
    freshness side conditions inlined at each node (no separate evidence
    structure), so trees stay valid under seen-shrinking. -/
inductive BroadSimple : List stQueue → stQueue → Prop where
  | leaf (seen stq) : stq.2 = [] → BroadSimple seen stq
  | intC_node {seen branches Q}
      (hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
      (hfreshN : ∀ x ∈ branches, (x.2.2.2, Q) ∉ (SessionType.internalChoice branches, Q) :: seen)
      (hall : ∀ x ∈ branches, BroadSimple ((SessionType.internalChoice branches, Q) :: seen) (x.2.2.2, Q)) :
      BroadSimple seen (SessionType.internalChoice branches, Q)
  | spec_node {seen p branches Q T' lab S}
      (hAbs : ∀ m ∈ Q, m.1 ≠ p) (hmem : (lab, S, T') ∈ branches)
      (hfreshN : (T', Q) ∉ (SessionType.externalChoice p branches, Q) :: seen)
      (t : BroadSimple ((SessionType.externalChoice p branches, Q) :: seen) (T', Q)) :
      BroadSimple seen (SessionType.externalChoice p branches, Q)
  | deq_node {seen p branches Q Q' lab S T'}
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
      (hfreshN : (T', Q') ∉ (SessionType.externalChoice p branches, Q) :: seen)
      (t : BroadSimple ((SessionType.externalChoice p branches, Q) :: seen) (T', Q')) :
      BroadSimple seen (SessionType.externalChoice p branches, Q)
  | unfold_node {seen T U Q}
      (hU : Unfold1 T U)
      (hfreshN : (U, Q) ∉ (T, Q) :: seen)
      (t : BroadSimple ((T, Q) :: seen) (U, Q)) :
      BroadSimple seen (T, Q)

/-- Seen-shrinking for simple trees: a proof valid at a big seen-set stays
    valid at any smaller one (freshness is monotone in shrinking; the evidence
    fields do not mention seen). -/
theorem broadSimple_shrink : ∀ (seenS seenB : List stQueue) (stq : stQueue),
    seenS ⊆ seenB → BroadSimple seenB stq → BroadSimple seenS stq := by
  intro seenS seenB stq hsub h
  induction h generalizing seenS with
  | leaf seen stq hEnd =>
    exact BroadSimple.leaf _ _ hEnd
  | @intC_node seen branches Q hfresh hfreshN hall ih =>
    refine BroadSimple.intC_node hfresh ?_ (fun x hx => ih x hx _ ?_)
    · intro x hx hcon
      rcases List.mem_cons.mp hcon with heq | hcon
      · exact hfreshN x hx (List.mem_cons.mpr (Or.inl heq))
      · exact hfreshN x hx (List.mem_cons.mpr (Or.inr (hsub hcon)))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hsub hy))
  | @spec_node seen p branches Q T' lab S hAbs hmem hfreshN t ih =>
    refine BroadSimple.spec_node hAbs hmem ?_ (ih _ ?_)
    · intro hcon
      rcases List.mem_cons.mp hcon with heq | hcon
      · exact hfreshN (List.mem_cons.mpr (Or.inl heq))
      · exact hfreshN (List.mem_cons.mpr (Or.inr (hsub hcon)))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hsub hy))
  | @deq_node seen p branches Q Q' lab S T' hmem hQ hfreshN t ih =>
    refine BroadSimple.deq_node hmem hQ ?_ (ih _ ?_)
    · intro hcon
      rcases List.mem_cons.mp hcon with heq | hcon
      · exact hfreshN (List.mem_cons.mpr (Or.inl heq))
      · exact hfreshN (List.mem_cons.mpr (Or.inr (hsub hcon)))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hsub hy))
  | @unfold_node seen T U Q hU hfreshN t ih =>
    refine BroadSimple.unfold_node hU ?_ (ih _ ?_)
    · intro hcon
      rcases List.mem_cons.mp hcon with heq | hcon
      · exact hfreshN (List.mem_cons.mpr (Or.inl heq))
      · exact hfreshN (List.mem_cons.mpr (Or.inr (hsub hcon)))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hsub hy))

/-- Disjunctive excision: every broad tree yields either a fresh proof at its
    own seen-set, or a repeat package (subtree plus membership plus a subset
    chain) for an ancestor to adopt. Structural induction on the derivation,
    no measures and no fuel. -/
theorem broad_excise : ∀ (seen : List stQueue) (stq : stQueue) (h : BroadTree seen stq),
    (∃ (t : BroadSimple seen stq), stq ∉ seen) ∨
    (∃ (s : stQueue) (S_deep : List stQueue) (t : BroadSimple S_deep s),
      s ∈ seen ∧ seen ⊆ S_deep) := by
  intro seen stq h
  induction h with
  | leaf seen stq hEnd =>
    by_cases hmem : stq ∈ seen
    · exact Or.inr ⟨stq, seen, BroadSimple.leaf _ _ hEnd, hmem, List.Subset.refl _⟩
    · exact Or.inl ⟨BroadSimple.leaf _ _ hEnd, hmem⟩
  | @intC_node seen branches Q hfresh hall ih =>
    by_cases Hm : ∃ (s : stQueue) (S_de : List stQueue) (t : BroadSimple S_de s),
        s ∈ ((SessionType.internalChoice branches, Q) :: seen) ∧
        ((SessionType.internalChoice branches, Q) :: seen) ⊆ S_de ∧
        s = (SessionType.internalChoice branches, Q)
    · obtain ⟨s, S_de, t, hmemR, hsubR, heqR⟩ := Hm
      subst heqR
      have hsubShrink : seen ⊆ S_de :=
        fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
      have tAdopt : BroadSimple seen (SessionType.internalChoice branches, Q) :=
        broadSimple_shrink _ _ _ hsubShrink t
      by_cases hself : (SessionType.internalChoice branches, Q) ∈ seen
      · exact Or.inr ⟨_, _, tAdopt, hself, List.Subset.refl _⟩
      · exact Or.inl ⟨tAdopt, hself⟩
    · by_cases Hf : ∃ (s : stQueue) (S_de : List stQueue) (t : BroadSimple S_de s),
          s ∈ ((SessionType.internalChoice branches, Q) :: seen) ∧
          ((SessionType.internalChoice branches, Q) :: seen) ⊆ S_de ∧
          s ≠ (SessionType.internalChoice branches, Q)
      · obtain ⟨s, S_de, t, hmemR, hsubR, hneR⟩ := Hf
        have hmemF : s ∈ seen := by
          rcases List.mem_cons.mp hmemR with heq | hmemR
          · exact absurd heq hneR
          · exact hmemR
        have hsubF : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        exact Or.inr ⟨s, S_de, t, hmemF, hsubF⟩
      · have hAll : ∀ (x : Role × Lab × DataSort × SessionType) (hx : x ∈ branches),
            ∃ (t : BroadSimple ((SessionType.internalChoice branches, Q) :: seen) (x.2.2.2, Q)),
              (x.2.2.2, Q) ∉ ((SessionType.internalChoice branches, Q) :: seen) := by
          intro x hx
          rcases ih x hx with ⟨t, hf⟩ | ⟨s, S_de, tt, hmemR, hsubR⟩
          · exact ⟨t, hf⟩
          · exfalso
            by_cases heqS : s = (SessionType.internalChoice branches, Q)
            · exact Hm ⟨s, S_de, tt, hmemR, hsubR, heqS⟩
            · exact Hf ⟨s, S_de, tt, hmemR, hsubR, heqS⟩
        have hSub : ∀ (x : Role × Lab × DataSort × SessionType) (hx : x ∈ branches),
            BroadSimple ((SessionType.internalChoice branches, Q) :: seen) (x.2.2.2, Q) := by
          intro x hx
          obtain ⟨t, _⟩ := hAll x hx
          exact t
        have hFresh : ∀ x ∈ branches,
            (x.2.2.2, Q) ∉ (SessionType.internalChoice branches, Q) :: seen := by
          intro x hx
          obtain ⟨_, hf⟩ := hAll x hx
          exact hf
        have tAsm : BroadSimple seen (SessionType.internalChoice branches, Q) :=
          BroadSimple.intC_node hfresh hFresh hSub
        by_cases hself : (SessionType.internalChoice branches, Q) ∈ seen
        · exact Or.inr ⟨_, _, tAsm, hself, List.Subset.refl _⟩
        · exact Or.inl ⟨tAsm, hself⟩
  | @spec_node seen p branches Q T' lab S hAbs hmem t ih =>
    rcases ih with ⟨tF, hFr⟩ | ⟨s, S_de, tt, hmemR, hsubR⟩
    · have tAsm : BroadSimple seen (SessionType.externalChoice p branches, Q) :=
        BroadSimple.spec_node hAbs hmem hFr tF
      by_cases hself : (SessionType.externalChoice p branches, Q) ∈ seen
      · exact Or.inr ⟨_, _, tAsm, hself, List.Subset.refl _⟩
      · exact Or.inl ⟨tAsm, hself⟩
    · by_cases heq : s = (SessionType.externalChoice p branches, Q)
      · subst heq
        have hsubShrink : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        have tAdopt : BroadSimple seen (SessionType.externalChoice p branches, Q) :=
          broadSimple_shrink _ _ _ hsubShrink tt
        by_cases hself : (SessionType.externalChoice p branches, Q) ∈ seen
        · exact Or.inr ⟨_, _, tAdopt, hself, List.Subset.refl _⟩
        · exact Or.inl ⟨tAdopt, hself⟩
      · have hmemF : s ∈ seen := by
          rcases List.mem_cons.mp hmemR with heq' | hmemR
          · exact absurd heq' heq
          · exact hmemR
        have hsubF : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        exact Or.inr ⟨s, S_de, tt, hmemF, hsubF⟩
  | @deq_node seen p branches Q Q' lab S T' hmem hQ t ih =>
    rcases ih with ⟨tF, hFr⟩ | ⟨s, S_de, tt, hmemR, hsubR⟩
    · have tAsm : BroadSimple seen (SessionType.externalChoice p branches, Q) :=
        BroadSimple.deq_node hmem hQ hFr tF
      by_cases hself : (SessionType.externalChoice p branches, Q) ∈ seen
      · exact Or.inr ⟨_, _, tAsm, hself, List.Subset.refl _⟩
      · exact Or.inl ⟨tAsm, hself⟩
    · by_cases heq : s = (SessionType.externalChoice p branches, Q)
      · subst heq
        have hsubShrink : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        have tAdopt : BroadSimple seen (SessionType.externalChoice p branches, Q) :=
          broadSimple_shrink _ _ _ hsubShrink tt
        by_cases hself : (SessionType.externalChoice p branches, Q) ∈ seen
        · exact Or.inr ⟨_, _, tAdopt, hself, List.Subset.refl _⟩
        · exact Or.inl ⟨tAdopt, hself⟩
      · have hmemF : s ∈ seen := by
          rcases List.mem_cons.mp hmemR with heq' | hmemR
          · exact absurd heq' heq
          · exact hmemR
        have hsubF : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        exact Or.inr ⟨s, S_de, tt, hmemF, hsubF⟩
  | @unfold_node seen T U Q hU t ih =>
    rcases ih with ⟨tF, hFr⟩ | ⟨s, S_de, tt, hmemR, hsubR⟩
    · have tAsm : BroadSimple seen (T, Q) :=
        BroadSimple.unfold_node hU hFr tF
      by_cases hself : (T, Q) ∈ seen
      · exact Or.inr ⟨_, _, tAsm, hself, List.Subset.refl _⟩
      · exact Or.inl ⟨tAsm, hself⟩
    · by_cases heq : s = (T, Q)
      · subst heq
        have hsubShrink : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        have tAdopt : BroadSimple seen (T, Q) :=
          broadSimple_shrink _ _ _ hsubShrink tt
        by_cases hself : (T, Q) ∈ seen
        · exact Or.inr ⟨_, _, tAdopt, hself, List.Subset.refl _⟩
        · exact Or.inl ⟨tAdopt, hself⟩
      · have hmemF : s ∈ seen := by
          rcases List.mem_cons.mp hmemR with heq' | hmemR
          · exact absurd heq' heq
          · exact hmemR
        have hsubF : seen ⊆ S_de :=
          fun y hy => hsubR (List.mem_cons.mpr (Or.inr hy))
        exact Or.inr ⟨s, S_de, tt, hmemF, hsubF⟩

/-- Fresh broad tree from any broad tree (top-level reports die since nothing
    is a member of `[]`). -/
theorem broad_simplify : ∀ {stq : stQueue} (h : BroadTree [] stq),
    ∃ (t : BroadSimple [] stq), stq ∉ [] := by
  intro stq h
  rcases broad_excise [] stq h with ⟨t, hf⟩ | ⟨s, S_de, t, hmem, hsub⟩
  · exact ⟨t, hf⟩
  · simp at hmem

/-- Full broad transport: a fresh broad tree refutes any `CannotAlwaysDrainInternalDeepSeen`
    derivation
    whose seen-set is contained in the trace's visited set. The `intC_adv`
    arm closes by child-selection; every other arm replays the failure
    tableau head-against-head. -/
theorem broad_transport : ∀ (seenST : List stQueue) (stq : stQueue),
    BroadSimple seenST stq →
    stq ∉ seenST →
    stq.1.WellFormed →
    ∀ (seenS : List (SessionType × Queue)),
      seenS ⊆ seenST →
      (∀ p ∈ seenS, p.2 ≠ []) →
      CannotAlwaysDrainInternalDeepSeen seenS stq.1 stq.2 → False := by
  intro seenST stq hT hFresh hWF seenS hSub hFree d
  induction hT generalizing seenS with
  | leaf seen stq hEnd =>
    exact cannotRec_nil_absurd hFree d hEnd
  | @intC_node seen branches Q hfresh hfreshN hall ih =>
    cases d
    case cut hmemC =>
      exact hFresh (hSub hmemC)
    case intC_blocked p' lab' S' T'' m heq hmemB hmQ =>
      exact (hfresh _ _ _ _ hmemB _ hmQ) heq
    case intC_adv x hmemB hsub hfresh =>
      have hChildFresh : (x.2.2.2, Q) ∉ (SessionType.internalChoice branches, Q) :: seen :=
        hfreshN x hmemB
      have hWFchild : (x.2.2.2, Q).1.WellFormed := by
        have hST : st_trans (SessionType.internalChoice branches) (st_label.out x.1 x.2.1 x.2.2.1) x.2.2.2 :=
          st_trans.intC hmemB
        have h := SessionType.wellFormedPreserved _ _ _ hWF hST
        simpa using h
      have hSubExt : ∀ (s : List (SessionType × Queue)), s ⊆ seen →
          s ⊆ (SessionType.internalChoice branches, Q) :: seen := by
        intro s hS y hy
        exact List.mem_cons.mpr (Or.inr (hS hy))
      exact ih x hmemB hChildFresh hWFchild _ (hSubExt _ hSub) hFree hsub
  | @spec_node seen p branches Q T' lab S hAbs hmem hfreshN t ih =>
    have hWF' : (T', Q).1.WellFormed :=
      SessionType.wellFormedPreserved _ _ _ hWF (st_trans.extC hmem)
    have hSub' : ∀ (s : List (SessionType × Queue)), s ⊆ seen →
        s ⊆ (SessionType.externalChoice p branches, Q) :: seen := by
      intro s hS y hy
      exact List.mem_cons.mpr (Or.inr (hS hy))
    have hFresh' : (T', Q) ∉ (SessionType.externalChoice p branches, Q) :: seen := hfreshN
    cases d
    case cut hmemC =>
      exact hFresh (hSub hmemC)
    case extC_missed lab0 S0 hmiss holdest =>
      obtain ⟨pre, post, hsplit, -⟩ := holdest
      have hsplit' : Q = pre ++ QueueMessage.msg p lab0 S0 :: post := hsplit
      have hmemQ : QueueMessage.msg p lab0 S0 ∈ Q := by
        rw [hsplit']
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      exact hAbs _ hmemQ rfl
    case extC_allFail hne habs hall =>
      exact ih hFresh' hWF' _ (hSub' _ hSub) hFree (hall _ hmem)
    case extC_deq Q0 lab2 S2 T2 hsub2 hmem2 hQ2 =>
      obtain ⟨pre, post, hsplit, _, _⟩ := queue_dequeue_some_iff hQ2
      have hsplit' : Q = pre ++ [QueueMessage.msg p lab2 S2] ++ post := hsplit
      have hmemQ : QueueMessage.msg p lab2 S2 ∈ Q := by
        rw [hsplit']
        simp
      exact hAbs _ hmemQ rfl
  | @deq_node seen p branches Q Q' lab S T' hmem hQ hfreshN t ih =>
    have hWF' : (T', Q').1.WellFormed :=
      SessionType.wellFormedPreserved _ _ _ hWF (st_trans.extC hmem)
    have hSub' : ∀ (s : List (SessionType × Queue)), s ⊆ seen →
        s ⊆ (SessionType.externalChoice p branches, Q) :: seen := by
      intro s hS y hy
      exact List.mem_cons.mpr (Or.inr (hS hy))
    have hFresh' : (T', Q') ∉ (SessionType.externalChoice p branches, Q) :: seen := hfreshN
    cases d
    case cut hmemC =>
      exact hFresh (hSub hmemC)
    case extC_missed lab0 S0 hmiss holdest =>
      have heqM : QueueMessage.msg p lab S = QueueMessage.msg p lab0 S0 :=
        oldest_from_unique
          (dequeue_some_oldest_from hQ) holdest
      obtain ⟨rfl, rfl, rfl⟩ := heqM
      exact hmiss _ hmem
    case extC_allFail hne habs hall =>
      obtain ⟨pre, post, hsplit, _⟩ := dequeue_some_oldest_from hQ
      have hsplit' : Q = pre ++ QueueMessage.msg p lab S :: post := hsplit
      have hmemQ : QueueMessage.msg p lab S ∈ Q := by
        rw [hsplit']
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      exact habs _ hmemQ rfl
    case extC_deq Q0 lab2 S2 T2 hsub2 hmem2 hQ2 =>
      obtain ⟨pre, post, hsplit, _, _⟩ := queue_dequeue_some_iff hQ
      obtain ⟨pre2, post2, hsplit2, _, _⟩ := queue_dequeue_some_iff hQ2
      have heqM : QueueMessage.msg p lab S = QueueMessage.msg p lab2 S2 :=
        oldest_from_unique
          (dequeue_some_oldest_from hQ) (dequeue_some_oldest_from hQ2)
      obtain ⟨rfl, rfl, rfl⟩ := heqM
      have hQeq : Q' = Q0 := Option.some.inj (hQ.symm.trans hQ2)
      have hTeq : T' = T2 := ext_target_unique hWF.1 hmem hmem2
      rw [←hQeq, ←hTeq] at hsub2
      exact ih hFresh' hWF' _ (hSub' _ hSub) hFree hsub2
  | @unfold_node seen T U Q hU hfreshN t ih =>
    cases hU
    case tRec X B =>
      have hWF' : (substSessionType B X (SessionType.tRec X B), Q).1.WellFormed :=
        SessionType.wellFormedUnfold hWF (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
      have hFresh' : (substSessionType B X (SessionType.tRec X B), Q) ∉
          (SessionType.tRec X B, Q) :: seen := hfreshN
      cases d
      case cut hmemC =>
        exact hFresh (hSub hmemC)
      case trec_new hne hnmemS hsubS =>
        have hSubExt : ((SessionType.tRec X B, Q) :: seenS) ⊆ ((SessionType.tRec X B, Q) :: seen) := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hSub hx)
        have hFreeExt : ∀ p ∈ ((SessionType.tRec X B, Q) :: seenS), p.2 ≠ [] := by
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hne
          · exact hFree _ hp
        exact ih hFresh' hWF' _ hSubExt hFreeExt hsubS
      case trec_empty hsubS =>
        have hSub0 : seenS ⊆ (SessionType.tRec X B, []) :: seen := by
          intro x hx
          exact List.mem_cons.mpr (Or.inr (hSub hx))
        exact ih hFresh' hWF' _ hSub0 hFree hsubS

end DrainabilityBroad

section DrainabilityIff

/-- Forward half of the iff (`Can → ¬Cannot`): a drainage derivation builds a
    broad tree, excision makes it path-fresh, and transport refutes every
    failure tableau. Needs only `WellFormed` (for dequeue–dequeue branch
    pinning). -/
theorem drainrec_not_cannot_of_can {T : SessionType} {Q : Queue}
    (hWF : T.WellFormed) (hCan : CanAlwaysDrainInternalDeepRec T Q) :
    ¬ CannotAlwaysDrainInternalDeepRec T Q := by
  intro hCannot
  obtain ⟨t, hf⟩ := broad_simplify (broad_soundness [] hCan)
  exact broad_transport [] (T, Q) t (by simp) hWF [] (by simp) (by simp) hCannot
end DrainabilityIff

end Drainability
