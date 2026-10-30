import Nest.Drainability
import Nest.FairScheduler

open Drainability

/-!
# DrainNonLiveness: drain failure refutes output liveness.

Proves `cannotdrain_implies_not_output_live`: in a well-formed, roles-present,
no-self-send, half-duplex network `N`, if role `p` has an entry `(p, (T, Q)) ∈ N`
with `T` well-formed, `Monitorable T`, and `CannotAlwaysDrainInternalDeepRec T Q`,
then `¬ IsOutputLiveNetwork N`. The fair scheduler (`FairScheduler`) drives the
never-firing path; the fixed-core invariant pins the undrainable message.
-/

section UnfoldSteerHelpers

/-- Absence transfers backward along unfold chains: if no `out`-step fires
    at `Tcur`, none fires at any `Tnet` unfolding to it. -/
private theorem adv_no_send_chain {Tcur : SessionType}
    (hBase : ∀ (q : Role) (lab : Lab) (S : DataSort) (T' : SessionType),
      ¬ st_trans Tcur (st_label.out q lab S) T')
    {Tnet : SessionType} (hU : UnfoldStar Tnet Tcur)
    {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (hST : st_trans Tnet (st_label.out q lab S) T') : False := by
  induction hU with
  | refl => exact hBase _ _ _ _ hST
  | step h1 _ ih =>
    cases h1 with
    | tRec =>
      cases hST with
      | tRec h => exact ih hBase h

/-- Out-step transport along unfold chains: a branch of the `intC` head
    at the end of the chain fires from the chain head. -/
private theorem adv_out_fire_unfold {Tnet Ttarg : SessionType}
    {branches : List (Role × Lab × DataSort × SessionType)}
    {s : Role} {lab : Lab} {S : DataSort} {T0 : SessionType}
    (hU : UnfoldStar Tnet Ttarg)
    (hT : Ttarg = SessionType.internalChoice branches)
    (hmemB : (s, lab, S, T0) ∈ branches) :
    st_trans Tnet (st_label.out s lab S) T0 := by
  induction hU with
  | refl =>
    subst hT
    exact st_trans.intC hmemB
  | step h1 _ ih =>
    cases h1 with
    | tRec => exact st_trans.tRec (ih hT)

/-- HD + presence exclude branch-sender junk through unfold chains. -/
private theorem hd_reachable_no_branch_junk_trec {N N' : Network} {r : Role}
    {T : SessionType} {Q : Queue}
    {branches : List (Role × Lab × DataSort × SessionType)}
    {s : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (hHD : IsHalfDuplex N) (hStar : net_trans_star N N')
    (hU : UnfoldStar T (SessionType.internalChoice branches))
    (hmem : (r, (T, Q)) ∈ N')
    (hmemB : (s, lab, S, T') ∈ branches)
    (hne : s ≠ r)
    (_hNS : N'.NoSelf) (_hRP : N'.RolesPresent)
    {stqs : SessionTypeWithQueue} (hmemS : (s, stqs) ∈ N')
    (hJunk : QueueContainsFrom Q s) : False := by
  have hSTout : st_trans T (st_label.out s lab S) T' :=
    adv_out_fire_unfold hU rfl hmemB
  have hComm : net_trans N' (net_label.τ_comm r s lab S)
      ((N'.replace r (T', Q)).replace s
        (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) :=
    net_trans.comm (p := r) (q := s) hne.symm (sq_trans.send hSTout)
      sq_trans.recv hmem hmemS
  have hStar'' : net_trans_star N ((N'.replace r (T', Q)).replace s
      (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) :=
    net_trans_star.trans hStar (net_trans_star.step (by trivial) hComm (net_trans_star.refl _))
  have hmidR : (r, (T', Q)) ∈ N'.replace r (T', Q) := by
    unfold Network.replace
    simp
  have hmemR : (r, (T', Q)) ∈ ((N'.replace r (T', Q)).replace s
      (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) :=
    mem_replace_other hmidR (Ne.symm hne)
  have hmemS' : (s, (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) ∈
      ((N'.replace r (T', Q)).replace s
        (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) := by
    unfold Network.replace
    simp
  have hNo := hHD _ hStar'' r s Q (stqs.2 ++ [QueueMessage.msg r lab S])
    ⟨T', hmemR⟩ ⟨stqs.1, hmemS'⟩ hJunk
  exact hNo ⟨lab, S, queueMem_append_single _ _⟩

/-- Send-absence at a linked entry via `adv_no_send_chain`. -/
private theorem adv_comm_absurd_at {Nmid : Network} {p : Role} {Tnet : SessionType}
    {Qnet : Queue} {Tcur : SessionType} (hU : UnfoldStar Tnet Tcur)
    (hBase : ∀ (q : Role) (lab : Lab) (S : DataSort) (T' : SessionType),
      ¬ st_trans Tcur (st_label.out q lab S) T')
    (hmem : (p, (Tnet, Qnet)) ∈ Nmid) (hWFm : Nmid.WellFormed)
    {q : Role} {lab : Lab} {So : DataSort} {N2 : Network}
    (hStep : net_trans Nmid (net_label.τ_comm p q lab So) N2) : False := by
  cases hStep with
  | comm _ h_send _ hmem_p _ =>
    have heq : _ = (Tnet, Qnet) := network_mem_unique hWFm hmem_p hmem
    subst heq
    cases h_send with
    | send hST => exact adv_no_send_chain hBase hU hST

/-- Other roles' dequeues leave `r`'s entry untouched. -/
private theorem adv_entry_untouched_deq {N N' : Network} {r s : Role} {p : Role}
    {lab : Lab} {S : DataSort} (hne : s ≠ r)
    (hTr : net_trans N (net_label.τ_dequeue s p lab S) N') :
    ∀ stq, (r, stq) ∈ N → (r, stq) ∈ N' := by
  intro stq hmem0
  cases hTr with
  | dequeue _ _ =>
    unfold Network.replace
    simp only [List.mem_cons, List.mem_filter]
    refine Or.inr ⟨hmem0, ?_⟩
    exact bne_iff_ne.mpr hne.symm

/-- Receives append only: `r`'s type is unchanged when `r` receives. -/
private theorem adv_type_untouched_recv {N N' : Network} {r s : Role}
    {lab : Lab} {S : DataSort}
    (hWF : N.WellFormed)
    (hTr : net_trans N (net_label.τ_comm s r lab S) N') :
    ∀ (T : SessionType) (Q : Queue), (r, (T, Q)) ∈ N →
      (r, (T, Q ++ [QueueMessage.msg s lab S])) ∈ N' := by
  intro T Q hmem0
  cases hTr with
  | comm _ _ h_recv _ hmem_q =>
    have hTEq : _ = (T, Q) := network_mem_unique hWF hmem_q hmem0
    subst hTEq
    cases h_recv with
    | recv =>
      unfold Network.replace
      exact List.mem_cons.mpr (Or.inl rfl)

/-- Peel all leading `tRec`s off a session step. -/
private theorem st_trans_peel_trec {T : SessionType} {α : st_label} {T' : SessionType}
    (hST : st_trans T α T') :
    ∃ T0, UnfoldStar T T0 ∧ st_trans T0 α T' ∧ IsHeadNF T0 := by
  induction hST with
  | intC hmem =>
    exact ⟨_, UnfoldStar.refl _, st_trans.intC hmem, trivial⟩
  | extC hmem =>
    exact ⟨_, UnfoldStar.refl _, st_trans.extC hmem, trivial⟩
  | tRec _ ih =>
    obtain ⟨T0, hU, hST0, hNF⟩ := ih
    exact ⟨T0, UnfoldStar.step Unfold1.tRec hU, hST0, hNF⟩

end UnfoldSteerHelpers

section QueueAppendDequeue

/-- Single-append dequeue persistence (scan commutes with a tail snoc). -/
theorem dequeue_go_append_single {acc Q Q' : Queue} {msg msg2 : QueueMessage}
    (h : Queue.dequeue.go acc Q msg = some Q') :
    Queue.dequeue.go acc (Q ++ [msg2]) msg = some (Q' ++ [msg2]) := by
  induction Q generalizing acc with
  | nil =>
    simp [Queue.dequeue.go] at h
  | cons m rest ih =>
    by_cases hm : m = msg
    · simp [Queue.dequeue.go, hm] at h ⊢
      cases h
      exact (List.append_assoc acc rest [msg2]).symm
    · by_cases hs : m.1 = msg.1
      · simp [Queue.dequeue.go, hm, hs] at h
      · simp [Queue.dequeue.go, hm, hs] at h ⊢
        exact ih h

/-- General-extension dequeue persistence. -/
theorem dequeue_appendList (E : Queue) :
    ∀ {Q Q' : Queue} {msg : QueueMessage},
    Q.dequeue msg = some Q' → (Q ++ E).dequeue msg = some (Q' ++ E) := by
  induction E with
  | nil =>
    intro Q Q' msg h
    simpa using h
  | cons m E' ih =>
    intro Q Q' msg h
    have hgo : Queue.dequeue.go [] Q msg = some Q' := by
      simpa [Queue.dequeue] using h
    have h1 : Queue.dequeue.go [] (Q ++ [m]) msg = some (Q' ++ [m]) :=
      dequeue_go_append_single hgo
    have h1' : (Q ++ [m]).dequeue msg = some (Q' ++ [m]) := by
      simpa [Queue.dequeue] using h1
    have h2 := ih h1'
    simpa [List.append_assoc] using h2

end QueueAppendDequeue

section RecSteer

/-- (2) Dequeue steps preserve failure. Needs `WellFormed` +
    `Monitorable` (both transport to the branch target). -/
theorem cannot_dequeue_step {T T' : SessionType} {Q Q' : Queue}
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort}
    (hWF : T.WellFormed) (hMon : Monitorable T)
    (hC : CannotAlwaysDrainInternalDeepRec T Q)
    (hT : T = SessionType.externalChoice p branches)
    (hmem : (lab, S, T') ∈ branches)
    (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q') :
    CannotAlwaysDrainInternalDeepRec T' Q' := by
  subst hT
  by_contra hCon
  have hWF' : T'.WellFormed := wf_of_mem_extBranches hmem hWF
  have hMon' : Monitorable T' := hMon.mono (PruneStep.rtc_extC_mem hmem)
  have hCanT' : CanAlwaysDrainInternalDeepRec T' Q' :=
    drainrec_can_of_not_cannot hWF' hMon' hCon
  have hCan : CanAlwaysDrainInternalDeepRec
      (SessionType.externalChoice p branches) Q :=
    CanAlwaysDrainInternalDeepRec.extC_deq p branches Q Q' lab S T' hmem hQ hCanT'
  exact (drainrec_not_cannot_of_can hWF hCan) hC

/-- (3) with freshness: at an `intC` head with no branch sender queued,
    the tableau cannot be `blocked` (freshness) nor `cut` (empty seen),
    so it is `adv` at some branch — the witness carried by `hC` itself.
    Proof-relevant inversion: no `WellFormed`/`Monitorable` needed. -/
theorem cannot_adv_branch {branches : List (Role × Lab × DataSort × SessionType)}
    {Q : Queue}
    (hC : CannotAlwaysDrainInternalDeepRec (SessionType.internalChoice branches) Q)
    (hfresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r') :
    ∃ x ∈ branches, CannotAlwaysDrainInternalDeepRec x.2.2.2 Q := by
  match hC with
  | .cut _ _ _ hmem => simp at hmem
  | .intC_blocked _ _ _ _ _ _ _ _ hmemB hmQ heq =>
    exact absurd heq (hfresh _ _ _ _ hmemB _ hmQ)
  | .intC_adv _ _ _ x hmemB _ hsub => exact ⟨x, hmemB, hsub⟩

/-- (4) Unfoldings preserve failure. The `Q = []` case is vacuous
    (`cannotRec_nil_absurd`); at `Q ≠ []` duality + `trec_step` closes.
    Needs `WellFormed` + `Monitorable` (both transport through unfold). -/
theorem cannot_unfold {X : String} {B : SessionType} {Q : Queue}
    (hWF : (SessionType.tRec X B).WellFormed)
    (hMon : Monitorable (SessionType.tRec X B))
    (hC : CannotAlwaysDrainInternalDeepRec (SessionType.tRec X B) Q) :
    CannotAlwaysDrainInternalDeepRec (substSessionType B X (SessionType.tRec X B)) Q := by
  by_contra hCon
  have hWFu : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
    SessionType.wellFormedUnfold hWF (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
  have hMonu : Monitorable (substSessionType B X (SessionType.tRec X B)) :=
    hMon.mono (PruneStep.rtc_trec_unfold X B)
  have hCanu : CanAlwaysDrainInternalDeepRec
      (substSessionType B X (SessionType.tRec X B)) Q :=
    drainrec_can_of_not_cannot hWFu hMonu hCon
  by_cases hQ : Q = []
  · subst hQ
    exact (cannotRec_nil_absurd (by simp) hC rfl).elim
  · have hCan : CanAlwaysDrainInternalDeepRec (SessionType.tRec X B) Q :=
      CanAlwaysDrainInternalDeepRec.trec_step X B Q hQ hCanu
    exact (drainrec_not_cannot_of_can hWF hCan) hC

end RecSteer

section PeelTransport

/-- Number of leading `tRec` binders (peel fuel). Substitution preserves
    the outer spine (Lemma `subst_preserves_tRecDepth`), so each head
    unfold strictly decreases this. -/
def tRecDepth : SessionType → Nat
  | .tEnd => 0
  | .tVar _ => 0
  | .internalChoice _ => 0
  | .externalChoice _ _ => 0
  | .tRec _ B => tRecDepth B + 1

/-- Substitution preserves the outer `tRec` spine. Needs guardedness:
    a bare `tVar X` would graft `R`. By induction on `B`; the `tVar`
    case uses `X ≠ Y`, the choice cases keep their head, the `tRec`
    case pushes through (or stops at shadowing). -/
theorem subst_preserves_tRecDepth : ∀ (B : SessionType) (X : String)
    (R : SessionType), SessionType.Guarded X B →
    tRecDepth (substSessionType B X R) = tRecDepth B
  | .tEnd, _, _, _ => by
    simp only [substSessionType, tRecDepth]
  | .tVar Y, X, _, hG => by
    have hne : X ≠ Y := hG
    simp only [substSessionType, ite_eq_right hne, tRecDepth]
  | .internalChoice _, _, _, _ => by
    simp only [substSessionType, tRecDepth]
  | .externalChoice _ _, _, _, _ => by
    simp only [substSessionType, tRecDepth]
  | .tRec Y C, X, R, hG => by
    have hGC : SessionType.Guarded X C := hG
    by_cases heq : X = Y
    · simp only [substSessionType, ite_eq_left heq]
    · have hC := subst_preserves_tRecDepth C X R hGC
      simp only [substSessionType, ite_eq_right heq, tRecDepth, hC]

/-- Unfold stars compose. -/
theorem unfoldStar_trans {T U V : SessionType} (h1 : UnfoldStar T U)
    (h2 : UnfoldStar U V) : UnfoldStar T V := by
  induction h1 with
  | refl => exact h2
  | step hU1 _ ih => exact UnfoldStar.step hU1 (ih h2)

/-- Peel to head-normal form. Needs full `WellFormed` (contractivity
    rules out unguarded loops like `tRec X (tVar X)`, for which peeling
    would cycle). Induction on the fuel `tRecDepth T`, which drops at
    each head unfold by `subst_preserves_tRecDepth`. -/
theorem peel_to_NF (T : SessionType) (hWF : T.WellFormed) :
    ∃ Tnf, UnfoldStar T Tnf ∧ IsHeadNF Tnf := by
  suffices key : ∀ (n : Nat) (T : SessionType), T.WellFormed → tRecDepth T = n →
      ∃ Tnf, UnfoldStar T Tnf ∧ IsHeadNF Tnf by
    exact key (tRecDepth T) T hWF rfl
  intro n
  induction n with
  | zero =>
    intro T _ hdepth
    cases T with
    | tEnd => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | tVar _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | internalChoice _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | externalChoice _ _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | tRec _ _ => simp [tRecDepth] at hdepth
  | succ n ih =>
    intro T hWF hdepth
    cases T with
    | tEnd => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | tVar _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | internalChoice _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | externalChoice _ _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
    | tRec X B =>
      have hCt : SessionType.Contractive (SessionType.tRec X B) := hWF.2.2
      cases hCt with
      | tRec _ h_guard =>
        have hU1 : UnfoldStar (SessionType.tRec X B)
            (substSessionType B X (SessionType.tRec X B)) :=
          UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)
        have hWF' : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
          SessionType.wellFormedUnfold hWF hU1
        have hBdepth : tRecDepth B = n := by
          have h2 := hdepth
          simp only [tRecDepth] at h2
          omega
        have hspine := subst_preserves_tRecDepth B X
          (SessionType.tRec X B) h_guard
        have hdep : tRecDepth (substSessionType B X
            (SessionType.tRec X B)) = n := by
          rw [hspine, hBdepth]
        obtain ⟨Tnf, hU2, hNF⟩ := ih _ hWF' hdep
        exact ⟨Tnf, unfoldStar_trans hU1 hU2, hNF⟩

/-- Unfold stars embed into pruning reachability (each `Unfold1.tRec`
    is a `PruneStep.trec`). -/
theorem unfoldStar_to_pruneRTC {T U : SessionType} (h : UnfoldStar T U) :
    Relation.ReflTransGen PruneStep T U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hU1 _ ih =>
    cases hU1 with
    | tRec => exact Relation.ReflTransGen.head PruneStep.trec ih

/-- Transport `Cannot`/`WellFormed`/`Monitorable` along an unfold star
    (the peel prelude: iterate (4) + preservation + `mono`). The caller
    never sees a seen set — this is pure `Rec`-level transport. -/
theorem rec_peel_transport {T Tnf : SessionType} {Q : Queue}
    (hU : UnfoldStar T Tnf) (hC : CannotAlwaysDrainInternalDeepRec T Q)
    (hWF : T.WellFormed) (hMon : Monitorable T) :
    CannotAlwaysDrainInternalDeepRec Tnf Q ∧ Tnf.WellFormed ∧
      Monitorable Tnf := by
  induction hU with
  | refl => exact ⟨hC, hWF, hMon⟩
  | step hU1 _ ih =>
    cases hU1
    have hC' := cannot_unfold hWF hMon hC
    have hWF' : (_ : SessionType).WellFormed :=
      SessionType.wellFormedUnfold hWF
        (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
    have hMon' : Monitorable (_ : SessionType) :=
      hMon.mono (unfoldStar_to_pruneRTC
        (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)))
    exact ih hC' hWF' hMon'

/-- `WellFormed` travels along unfold stars (no `Cannot` needed; used
    for non-`p` entries where only closedness/NoDupl matter). -/
theorem wf_unfold_star {T U : SessionType} (hU : UnfoldStar T U)
    (hWF : T.WellFormed) : U.WellFormed := by
  induction hU with
  | refl => exact hWF
  | step hU1 _ ih =>
    cases hU1
    exact ih (SessionType.wellFormedUnfold hWF
      (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)))

end PeelTransport

section StarFire

/-- Star-generalized adversarial send: an `intC` branch at the end of an
    unfold chain fires as a network `τ_comm`, preserving the queue. -/
theorem steer_intC_adv_star {N : Network} {p s : Role} {T : SessionType}
    {branches : List (Role × Lab × DataSort × SessionType)} {Q : Queue}
    {lab : Lab} {S : DataSort} {T0 : SessionType}
    (hNS : N.NoSelf) (hRP : N.RolesPresent)
    (hU : UnfoldStar T (SessionType.internalChoice branches))
    (hmem : (p, (T, Q)) ∈ N)
    (hmemB : (s, lab, S, T0) ∈ branches) :
    ∃ N', net_trans N (net_label.τ_comm p s lab S) N' ∧ (p, (T0, Q)) ∈ N' := by
  have hSTout : st_trans T (st_label.out s lab S) T0 :=
    adv_out_fire_unfold hU rfl hmemB
  have hOcc : T.Occurs s := st_trans_out_sender_occurs hSTout
  have hne : s ≠ p := fun heq => hNS _ _ _ hmem (heq ▸ hOcc)
  obtain ⟨stqs, hmemS⟩ := hRP _ _ _ _ hmem hOcc
  refine ⟨_, net_trans.comm (p := p) (q := s) (Ne.symm hne)
    (sq_trans.send hSTout) sq_trans.recv hmem hmemS, ?_⟩
  · have hmid : (p, (T0, Q)) ∈ N.replace p (T0, Q) := by
      unfold Network.replace
      simp
    exact mem_replace_other hmid (Ne.symm hne)

/-- Local `List.Mem` to `QueueMem` bridge. -/
private theorem listMem_to_queueMem {m : QueueMessage} {Q : Queue} :
    m ∈ Q → QueueMem m Q := by
  induction Q with
  | nil =>
    intro h
    simp at h
  | cons hd tl ih =>
    intro h
    simp at h
    rcases h with rfl | h
    · exact QueueMem.head
    · exact QueueMem.tail (ih h)

/-- Half-duplex discharges freshness: at an entry whose peel ends in an
    `intC` head, no queued message comes from any branch sender. -/
theorem fresh_of_HD {N0 Nmid : Network} {p : Role} {T : SessionType}
    {Q : Queue} {branches : List (Role × Lab × DataSort × SessionType)}
    (hHD0 : IsHalfDuplex N0) (hStar : net_trans_star N0 Nmid)
    (hmem : (p, (T, Q)) ∈ Nmid)
    (hU : UnfoldStar T (SessionType.internalChoice branches))
    (hNS : Nmid.NoSelf) (hRP : Nmid.RolesPresent) :
    ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
    (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r' := by
  intro r' l' s' U hmemB m hmQ heq
  obtain ⟨p0, lab0, S0⟩ := m
  have hpeq : p0 = r' := heq
  subst p0
  have hJunk : QueueContainsFrom Q r' :=
    ⟨lab0, S0, listMem_to_queueMem hmQ⟩
  have hSTout : st_trans T (st_label.out r' l' s') U :=
    adv_out_fire_unfold hU rfl hmemB
  have hOcc : T.Occurs r' := st_trans_out_sender_occurs hSTout
  have hne : r' ≠ p := fun heqP => hNS _ _ _ hmem (heqP ▸ hOcc)
  obtain ⟨stqs, hmemS⟩ := hRP _ _ _ _ hmem hOcc
  exact hd_reachable_no_branch_junk_trec hHD0 hStar hU
    hmem hmemB hne hNS hRP hmemS hJunk

end StarFire

section NonLivePrimitives

/-- A pinned dequeueable message refutes path liveness: if `m` is
    dequeueable at `i` but its exact dequeue label never fires after
    `i`, the liveness eventuality is contradicted directly. -/
theorem pinned_label_violates {π : InfiniteNetworkPath} {i : ℕ}
    {p : Role} {Qp : Queue} {q : Role} {lab : Lab} {S : DataSort}
    (hmem : NetworkHasQueue (π.seq i) p Qp)
    (hdeq : ∃ Q', Qp.dequeue (QueueMessage.msg q lab S) = some Q')
    (hnev : ∀ k, i ≤ k → π.δ k ≠ net_label.τ_dequeue p q lab S) :
    ¬ IsOutputLiveInfinitePath π := by
  intro hLive
  obtain ⟨Q', hQ'⟩ := hdeq
  obtain ⟨k, hk, hEq⟩ := hLive i p Qp hmem q lab S ⟨Q', hQ'⟩
  exact hnev k hk hEq

/-- Stuck states with a nonempty `p` entry refute output-liveness:
    the head message is dequeueable (`head_hit`) hence an orphan,
    contradicting the stuck-state conjunct. -/
theorem stuck_orphan_nonlive {Nst : Network} {p : Role} {T : SessionType}
    {Q : Queue} (hStuck : IsStuckNetwork Nst)
    (hmem : (p, (T, Q)) ∈ Nst) (hne : Q ≠ []) :
    ¬ IsOutputLiveNetwork Nst := by
  intro hLive
  obtain ⟨m0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨p0, lab0, S0⟩ := m0
  have hDeq : Queue.dequeue (QueueMessage.msg p0 lab0 S0 :: rest)
      (QueueMessage.msg p0 lab0 S0) = some rest := by
    simp [Queue.dequeue, Queue.dequeue.go]
  exact (hLive.2 Nst (net_trans_star.refl _) hStuck) p T _ p0 lab0 S0 rest hmem hDeq

end NonLivePrimitives

section UnconditionalNonLive

/-- Absent-sender branch transport: if `p` is absent from `Q`, any external-choice
    branch continuation preserves `Cannot` at the same queue `Q` (via `extC_spec` +
    duality). Used when a dequeue at `Qcore ++ Qextra` consumes a message from
    `Qextra` whose sender is absent from `Qcore`. -/
theorem cannot_dequeue_absent {T T' : SessionType} {Q : Queue}
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort}
    (hWF : T.WellFormed) (hMon : Monitorable T)
    (hC : CannotAlwaysDrainInternalDeepRec T Q)
    (hT : T = SessionType.externalChoice p branches)
    (hmem : (lab, S, T') ∈ branches)
    (habs : ∀ m ∈ Q, m.1 ≠ p) :
    CannotAlwaysDrainInternalDeepRec T' Q := by
  subst hT
  by_contra hCon
  have hWF' : T'.WellFormed := wf_of_mem_extBranches hmem hWF
  have hMon' : Monitorable T' := hMon.mono (PruneStep.rtc_extC_mem hmem)
  have hCanT' : CanAlwaysDrainInternalDeepRec T' Q :=
    drainrec_can_of_not_cannot hWF' hMon' hCon
  have hCan : CanAlwaysDrainInternalDeepRec
      (SessionType.externalChoice p branches) Q :=
    CanAlwaysDrainInternalDeepRec.extC_spec p branches Q habs (lab, S, T') hmem hCanT'
  exact (drainrec_not_cannot_of_can hWF hCan) hC

/-- Core-hit dequeue split: if `Qcore` contains a `q`-message, dequeuing a
    `q`-message from `Qcore ++ Qextra` dequeues it from `Qcore`. -/
private theorem dequeue_append_core_hit {Qcore Qextra Q' : Queue}
    {q : Role} {lab : Lab} {S : DataSort}
    (hHas : ∃ m ∈ Qcore, m.1 = q)
    (hQ : (Qcore ++ Qextra).dequeue (QueueMessage.msg q lab S) = some Q') :
    ∃ Qcore', Qcore.dequeue (QueueMessage.msg q lab S) = some Qcore' ∧
      Q' = Qcore' ++ Qextra := by
  obtain ⟨m0, hOld, hm10⟩ := oldest_of_mem Qcore q hHas
  obtain ⟨pre0, post0, hsplit0, -, hfree0⟩ := hOld
  obtain ⟨p0, lab0, S0⟩ := m0
  simp only at hm10
  subst p0
  have hold0 : oldest_from q Qcore (QueueMessage.msg q lab0 S0) :=
    ⟨pre0, post0, hsplit0, rfl, hfree0⟩
  obtain ⟨Qd0, hQd0⟩ := deq_of_oldest hold0
  have hQd0' : (Qcore ++ Qextra).dequeue (QueueMessage.msg q lab0 S0) =
      some (Qd0 ++ Qextra) :=
    dequeue_appendList Qextra hQd0
  have hOldFull : oldest_from q (Qcore ++ Qextra) (QueueMessage.msg q lab0 S0) :=
    dequeue_some_oldest_from hQd0'
  have hOldArm : oldest_from q (Qcore ++ Qextra) (QueueMessage.msg q lab S) :=
    dequeue_some_oldest_from hQ
  have heqM : QueueMessage.msg q lab0 S0 = QueueMessage.msg q lab S :=
    oldest_from_unique hOldFull hOldArm
  have hlab : lab0 = lab := by injection heqM
  have hSeq : S0 = S := by injection heqM
  subst hlab
  subst hSeq
  exact ⟨Qd0, hQd0, Option.some.inj (hQ.symm.trans hQd0')⟩

/-- Core-miss dequeue split: if `Qcore` has no `q`-messages, dequeuing a
    `q`-message from `Qcore ++ Qextra` leaves `Qcore` intact as a prefix. -/
private theorem dequeue_append_core_miss {Qcore Qextra Q' : Queue}
    {q : Role} {lab : Lab} {S : DataSort}
    (habs : ∀ m ∈ Qcore, m.1 ≠ q)
    (hQ : (Qcore ++ Qextra).dequeue (QueueMessage.msg q lab S) = some Q') :
    ∃ Qextra', Q' = Qcore ++ Qextra' := by
  obtain ⟨seen, left, hsplit, hQd, -⟩ := queue_dequeue_some_iff hQ
  have hsplit' : Qcore ++ Qextra = seen ++ ([QueueMessage.msg q lab S] ++ left) := by
    simpa [List.append_assoc] using hsplit
  rcases List.append_eq_append_iff.mp hsplit' with ⟨k, hsk, -⟩ | ⟨k, hQk, hEk⟩
  · refine ⟨k ++ left, ?_⟩
    rw [hQd, hsk, List.append_assoc]
  · cases k with
    | nil =>
      simp only [List.append_nil] at hQk
      refine ⟨left, ?_⟩
      rw [hQd, ← hQk]
    | cons a k' =>
      have ha : a = QueueMessage.msg q lab S := by
        simp only [List.cons_append] at hEk
        injection hEk with hhead _
        exact hhead.symm
      have haQ : a ∈ Qcore := by
        rw [hQk]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      rw [ha] at haQ
      exact (habs _ haQ rfl).elim

/-- Fixed-core steering invariant: `p`'s network queue decomposes as
    `Qcore ++ Qextra` for a fixed `Qcore` at which `p`'s session type is
    `Cannot`. Receives append to `Qextra`; sends and absent-sender dequeues
    preserve `Cannot` at the same `Qcore`. -/
def FixedCoreInv (N0 : Network) (p : Role) (Qcore : Queue) (N : Network) : Prop :=
  ∃ (T : SessionType) (Qextra : Queue),
    (p, (T, Qcore ++ Qextra)) ∈ N ∧
    CannotAlwaysDrainInternalDeepRec T Qcore ∧
    T.WellFormed ∧ Monitorable T ∧
    net_trans_star N0 N ∧
    N.WellFormed ∧ N.NoSelf ∧ N.RolesPresent

/-- Existence of a reachable fixed-core configuration with core length `k`. -/
def CoreConfig (N0 : Network) (p : Role) (k : ℕ) : Prop :=
  ∃ (N : Network) (Qcore : Queue),
    FixedCoreInv N0 p Qcore N ∧ Qcore.length = k

/-- At a minimal-length core `Qcore`, any `p`-dequeue step must miss `Qcore`
    (a core hit would shrink `Qcore` by one, contradicting minimality) and
    therefore preserves `FixedCoreInv` at the same `Qcore`. -/
theorem fixedCore_deq_step {N0 N1 N2 : Network} {p q : Role}
    {Qcore : Queue} {lab : Lab} {S : DataSort}
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k)
    (hWF1 : N1.WellFormed)
    (hInv : FixedCoreInv N0 p Qcore N1)
    (hStep : net_trans N1 (net_label.τ_dequeue p q lab S) N2) :
    FixedCoreInv N0 p Qcore N2 ∧ (∀ m ∈ Qcore, m.1 ≠ q) := by
  have hStep0 := hStep
  cases hStep with
  | @dequeue _ _ stq stq' _ _ hSQ hmem =>
    cases hSQ with
    | @dequeue T1 T1' Q1 Q1' _ _ _ hST hQ =>
      obtain ⟨T, Qextra, hmemP, hC, hTWF, hMon, hStar, hWF, hNS, hRP⟩ := hInv
      have hpair : (T1, Q1) = (T, Qcore ++ Qextra) :=
        network_mem_unique hWF1 hmem hmemP
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨T0, hU, hST0, hNF⟩ := st_trans_peel_trec hST
      obtain ⟨hC0, hWF0, hMon0⟩ := rec_peel_transport hU hC hTWF hMon
      cases hST0 with
      | @extC branches _ _ _ _ hmemB =>
        have hST0' : st_trans (SessionType.externalChoice q branches)
            (st_label.inp q lab S) T1' :=
          st_trans.extC hmemB
        have hmem' : (p, (T1', Q1')) ∈ Network.replace N1 p (T1', Q1') := by
          unfold Network.replace
          exact List.mem_cons.mpr (Or.inl rfl)
        have hWF' : (T1' : SessionType).WellFormed :=
          SessionType.wellFormedPreserved _ _ _ hWF0 hST0'
        have hMon' : Monitorable (T1' : SessionType) :=
          hMon0.mono (PruneStep.rtc_extC_mem hmemB)
        have hStar' : net_trans_star N0 (Network.replace N1 p (T1', Q1')) :=
          hStar.trans (net_trans_star.step (by trivial) hStep0 (net_trans_star.refl _))
        have hWF2 : (Network.replace N1 p (T1', Q1')).WellFormed :=
          Network.wellFormedPreserved _ _ _ hWF1 hStep0 (by trivial)
        have hNS2 : (Network.replace N1 p (T1', Q1')).NoSelf :=
          net_trans_preserves_no_self hStep0 hNS
        have hRP2 : (Network.replace N1 p (T1', Q1')).RolesPresent :=
          net_trans_preserves_roles_present hStep0 hRP
        by_cases hHas : ∃ m ∈ Qcore, m.1 = q
        · obtain ⟨Qcore', hQd0, hQ1'⟩ := dequeue_append_core_hit hHas hQ
          subst hQ1'
          have hC' := cannot_dequeue_step hWF0 hMon0 hC0 rfl hmemB hQd0
          have hdrop := Queue.dequeue_length_drop hQd0
          have hlt : Qcore'.length < Qcore.length := by omega
          have hCfg : CoreConfig N0 p Qcore'.length :=
            ⟨_, Qcore', ⟨T1', Qextra, hmem', hC', hWF', hMon', hStar',
              hWF2, hNS2, hRP2⟩, rfl⟩
          exact (hMin Qcore'.length hlt hCfg).elim
        · have habs : ∀ m ∈ Qcore, m.1 ≠ q :=
            fun m hm heq => hHas ⟨m, hm, heq⟩
          obtain ⟨Qextra', hQ1'⟩ := dequeue_append_core_miss habs hQ
          subst hQ1'
          have hC' := cannot_dequeue_absent hWF0 hMon0 hC0 rfl hmemB habs
          exact ⟨⟨T1', Qextra', hmem', hC', hWF', hMon', hStar',
            hWF2, hNS2, hRP2⟩, habs⟩
      | tRec _ => exact False.elim hNF

/-- Single-step drain preservation for `FixedCoreInv` at any role `r`. -/
theorem fixedCore_drain_step {N0 N1 N2 : Network} {p r q : Role}
    {Qcore : Queue} {lab : Lab} {S : DataSort}
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k)
    (hWF1 : N1.WellFormed)
    (hInv : FixedCoreInv N0 p Qcore N1)
    (hStep : net_trans N1 (net_label.τ_dequeue r q lab S) N2) :
    FixedCoreInv N0 p Qcore N2 := by
  by_cases heq : r = p
  · subst heq
    exact (fixedCore_deq_step hMin hWF1 hInv hStep).1
  · obtain ⟨T, Qextra, hmemP, hC, hTWF, hMon, hStar, _, hNS, hRP⟩ := hInv
    have hmemP' : (p, (T, Qcore ++ Qextra)) ∈ N2 :=
      adv_entry_untouched_deq heq hStep (T, Qcore ++ Qextra) hmemP
    have hStar' : net_trans_star N0 N2 :=
      hStar.trans (net_trans_star.step (by trivial) hStep (net_trans_star.refl _))
    have hWF2 : N2.WellFormed :=
      Network.wellFormedPreserved _ _ _ hWF1 hStep (by trivial)
    have hNS2 : N2.NoSelf := net_trans_preserves_no_self hStep hNS
    have hRP2 : N2.RolesPresent := net_trans_preserves_roles_present hStep hRP
    exact ⟨T, Qextra, hmemP', hC, hTWF, hMon, hStar', hWF2, hNS2, hRP2⟩

/-- Drain-trace preservation for `FixedCoreInv`. -/
theorem fixedCore_drain_preserve {N0 : Network} {p : Role} {Qcore : Queue}
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k) :
    ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
    N1.WellFormed → FixedCoreInv N0 p Qcore N1 → rr_drain_trace N1 N2 r ls →
    FixedCoreInv N0 p Qcore N2 := by
  intro N1 N2 r ls hWF1 hInv hTrace
  induction hTrace with
  | refl => exact hInv
  | step hStep _ ih =>
    have hWF2 := Network.wellFormedPreserved _ _ _ hWF1 hStep (by trivial)
    exact ih hWF2 (fixedCore_drain_step hMin hWF1 hInv hStep)

/-- Turn policy for `FixedCoreInv`: `p`-turns pick a branch preserving `Cannot`
    at `Qcore` (freshness on `Qcore` restricts from `Qcore ++ Qextra`);
    other roles' sends to `p` append to `Qextra` without touching `Qcore`. -/
theorem fixedCore_policy {N0 : Network} {p : Role} {Qcore : Queue}
    (hHD0 : IsHalfDuplex N0) : turn_policy (FixedCoreInv N0 p Qcore) := by
  intro r Nmid hInv hWFmid _hQuies
  obtain ⟨T, Qextra, hmem, hC, hTWF, hMon, hStar, hWF, hNS, hRP⟩ := hInv
  by_cases heq : r = p
  case pos =>
    subst heq
    obtain ⟨Tnf, hU, hNF⟩ := peel_to_NF T hTWF
    obtain ⟨hCnf, hWFnf, hMonnf⟩ := rec_peel_transport hU hC hTWF hMon
    cases Tnf with
    | tEnd =>
      refine Or.inr (fun qq lab S N2 hStep => ?_)
      exact adv_comm_absurd_at hU (fun _ _ _ _ hST => by cases hST) hmem hWF hStep
    | tVar X =>
      have hCl := hWFnf.2.1
      simp [SessionType.IsClosed, SessionType.fv] at hCl
    | tRec X B => exact False.elim hNF
    | internalChoice branches =>
      have hfreshFull := fresh_of_HD hHD0 hStar hmem hU hNS hRP
      have hfreshCore : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
          (r', l', s', U) ∈ branches → ∀ m ∈ Qcore, m.1 ≠ r' :=
        fun r' l' s' U hmemB m hm =>
          hfreshFull r' l' s' U hmemB m (List.mem_append.mpr (Or.inl hm))
      obtain ⟨⟨s, lab, S, T0⟩, hmemB, hC0⟩ := cannot_adv_branch hCnf hfreshCore
      obtain ⟨N', hStep, hmemR⟩ := steer_intC_adv_star hNS hRP hU hmem hmemB
      have hWF0 : T0.WellFormed := wf_of_mem_intBranches hmemB hWFnf
      have hMon0 : Monitorable T0 := hMonnf.mono (PruneStep.rtc_intC_mem hmemB)
      have hStar' : net_trans_star N0 N' :=
        hStar.trans (net_trans_star.step (by trivial) hStep (net_trans_star.refl _))
      have hWF' : N'.WellFormed :=
        Network.wellFormedPreserved _ _ _ hWF hStep (by trivial)
      have hNS' : N'.NoSelf := net_trans_preserves_no_self hStep hNS
      have hRP' : N'.RolesPresent := net_trans_preserves_roles_present hStep hRP
      exact Or.inl ⟨s, lab, S, N', hStep, T0, Qextra, hmemR, hC0, hWF0, hMon0,
        hStar', hWF', hNS', hRP'⟩
    | externalChoice q branches =>
      refine Or.inr (fun qq lab S N2 hStep => ?_)
      exact adv_comm_absurd_at hU (fun _ _ _ _ hST => by cases hST) hmem hWF hStep
  case neg =>
    by_cases hex : ∃ stq, (r, stq) ∈ Nmid
    case pos =>
      obtain ⟨⟨Tr, Qr⟩, hmemR⟩ := hex
      have hTrWF : Tr.WellFormed := hWFmid.2.1 _ hmemR
      obtain ⟨Tnf, hU, hNF⟩ := peel_to_NF Tr hTrWF
      have hWFnf : Tnf.WellFormed := wf_unfold_star hU hTrWF
      cases Tnf with
      | tEnd =>
        refine Or.inr (fun qq lab S N2 hStep => ?_)
        exact adv_comm_absurd_at hU (fun _ _ _ _ hST => by cases hST) hmemR hWFmid hStep
      | tVar X =>
        have hCl := hWFnf.2.1
        simp [SessionType.IsClosed, SessionType.fv] at hCl
      | tRec X B => exact False.elim hNF
      | internalChoice branches =>
        have hND : (SessionType.internalChoice branches).NoDupl := hWFnf.1
        have hne : branches ≠ [] := hND.ne_of_internalChoice
        obtain ⟨⟨s, lab, S, T0⟩, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨N', hStep, _⟩ := steer_intC_adv_star hNS hRP hU hmemR
          (List.mem_cons.mpr (Or.inl rfl))
        have hStep0 := hStep
        have hStar' : net_trans_star N0 N' :=
          hStar.trans (net_trans_star.step (by trivial) hStep0 (net_trans_star.refl _))
        have hWF' : N'.WellFormed :=
          Network.wellFormedPreserved _ _ _ hWF hStep0 (by trivial)
        have hNS' : N'.NoSelf := net_trans_preserves_no_self hStep0 hNS
        have hRP' : N'.RolesPresent := net_trans_preserves_roles_present hStep0 hRP
        by_cases heqS : s = p
        case pos =>
          subst s
          have hmemP' : (p, (T, (Qcore ++ Qextra) ++ [QueueMessage.msg r lab S])) ∈ N' :=
            adv_type_untouched_recv hWFmid hStep0 T (Qcore ++ Qextra) hmem
          rw [List.append_assoc] at hmemP'
          exact Or.inl ⟨p, lab, S, N', hStep0, T,
            Qextra ++ [QueueMessage.msg r lab S], hmemP', hC, hTWF, hMon,
            hStar', hWF', hNS', hRP'⟩
        case neg =>
          have hmem' : (p, (T, Qcore ++ Qextra)) ∈ N' := by
            cases hStep
            exact mem_replace_other (mem_replace_other hmem (Ne.symm heq))
              (Ne.symm heqS)
          exact Or.inl ⟨s, lab, S, N', hStep0, T, Qextra, hmem', hC, hTWF, hMon,
            hStar', hWF', hNS', hRP'⟩
      | externalChoice q branches =>
        refine Or.inr (fun qq lab S N2 hStep => ?_)
        exact adv_comm_absurd_at hU (fun _ _ _ _ hST => by cases hST) hmemR hWFmid hStep
    case neg =>
      refine Or.inr (fun qq lab S N2 hStep => ?_)
      cases hStep with
      | comm _ _ _ hpm _ =>
        exact hex ⟨_, hpm⟩

/-- Every label in a drain trace from a `FixedCoreInv` state avoids dequeuing
    any message whose sender appears in `Qcore`. -/
theorem fixedCore_traceLbl_ne {N0 N1 N2 : Network} {p r q0 : Role}
    {Qcore : Queue} {lab0 : Lab} {S0 : DataSort} {ls : List net_label}
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k)
    (hm0 : QueueMessage.msg q0 lab0 S0 ∈ Qcore)
    (t : RoundRobinDrainTraceT N1 N2 r ls) :
    N1.WellFormed → FixedCoreInv N0 p Qcore N1 →
      ∀ (dflt : net_label), dflt ≠ net_label.τ_dequeue p q0 lab0 S0 → ∀ (i : ℕ),
      traceLblD dflt t i ≠ net_label.τ_dequeue p q0 lab0 S0 := by
  induction t with
  | refl =>
    intro _ _ dflt hdflt i
    simp only [traceLblD]
    exact hdflt
  | @step N1 Nmid _ r q lab S _ hStep _ ih =>
    intro hWF1 hInv dflt hdflt i
    cases i with
    | zero =>
      simp only [traceLblD]
      by_cases heq : r = p
      · subst heq
        have habs := (fixedCore_deq_step hMin hWF1 hInv hStep).2
        have hne : q0 ≠ q := habs (QueueMessage.msg q0 lab0 S0) hm0
        intro hCon
        injection hCon with _ hq _ _
        exact hne hq.symm
      · intro hCon
        injection hCon with hr _ _ _
        exact heq hr
    | succ i =>
      simp only [traceLblD]
      have hWFmid := Network.wellFormedPreserved _ _ _ hWF1 hStep (by trivial)
      have hInvmid := fixedCore_drain_step hMin hWF1 hInv hStep
      exact ih hWFmid hInvmid dflt hdflt i

/-- Turn-level label avoidance for `FixedCoreInv`. -/
theorem fixedCore_turnLbl_ne {N0 N1 N2 : Network} {p r q0 : Role}
    {Qcore : Queue} {lab0 : Lab} {S0 : DataSort} {ls : List net_label}
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k)
    (hm0 : QueueMessage.msg q0 lab0 S0 ∈ Qcore)
    (hWF1 : N1.WellFormed) (hInv : FixedCoreInv N0 p Qcore N1)
    (o : RoundRobinTurnT N1 N2 r ls) (i : ℕ) :
    turnRelLbl o i ≠ net_label.τ_dequeue p q0 lab0 S0 := by
  cases o with
  | fire _ _ _ hTrace _ _ =>
    simp only [turnRelLbl]
    exact fixedCore_traceLbl_ne hMin hm0 hTrace hWF1 hInv _
      (fun h => by cases h) i
  | skip hTrace _ _ =>
    simp only [turnRelLbl]
    exact fixedCore_traceLbl_ne hMin hm0 hTrace hWF1 hInv _
      (fun h => by cases h) i

/-- Flattened-run label avoidance for `FixedCoreInv`. -/
theorem fixedCore_flatLbl_ne {N0 Nstar : Network} {p q0 : Role}
    {Qcore : Queue} {lab0 : Lab} {S0 : DataSort}
    (hHD0 : IsHalfDuplex N0)
    (hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N0 p k)
    (hm0 : QueueMessage.msg q0 lab0 S0 ∈ Qcore)
    (hWFstar : Nstar.WellFormed)
    (hInvstar : FixedCoreInv N0 p Qcore Nstar)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Nstar (FixedCoreInv N0 p Qcore)
      (fixedCore_drain_preserve hMin) (fixedCore_policy hHD0) hWFstar hInvstar j)
    (k : ℕ) :
    flatLbl Nstar (FixedCoreInv N0 p Qcore) (fixedCore_drain_preserve hMin)
      (fixedCore_policy hHD0) hWFstar hInvstar hUnbdd k ≠
      net_label.τ_dequeue p q0 lab0 S0 := by
  have hWFj := turn_wf Nstar (FixedCoreInv N0 p Qcore)
    (fixedCore_drain_preserve hMin) (fixedCore_policy hHD0) hWFstar hInvstar
    (flatBlk Nstar (FixedCoreInv N0 p Qcore) (fixedCore_drain_preserve hMin)
      (fixedCore_policy hHD0) hWFstar hInvstar hUnbdd k).1
  have hInvj := turn_inv Nstar (FixedCoreInv N0 p Qcore)
    (fixedCore_drain_preserve hMin) (fixedCore_policy hHD0) hWFstar hInvstar
    (flatBlk Nstar (FixedCoreInv N0 p Qcore) (fixedCore_drain_preserve hMin)
      (fixedCore_policy hHD0) hWFstar hInvstar hUnbdd k).1
  rw [flat_lbl_unfold]
  exact fixedCore_turnLbl_ne hMin hm0 hWFj hInvj _ _

/-- Unconditional non-liveness from `Cannot`: choose a reachable configuration
    `(Nstar, Qcore)` minimizing `Qcore.length`. From `Nstar`, steering with
    `FixedCoreInv` never dequeues any sender present in `Qcore` (otherwise
    `Qcore` would shrink, contradicting minimality), so the head of `Qcore`
    is a dequeueable message that never fires on the steered fair path (or
    survives into a stuck state as an orphan). -/
theorem cannotdrain_implies_not_output_live {N : Network}
    {p : Role} {T : SessionType} {Q : Queue}
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N)
    (hmem : (p, (T, Q)) ∈ N)
    (hTWF : T.WellFormed) (hMon : Monitorable T)
    (hC : CannotAlwaysDrainInternalDeepRec T Q) :
    ¬ IsOutputLiveNetwork N := by
  classical
  have hInv0 : FixedCoreInv N p Q N :=
    ⟨T, [], by simpa using hmem, hC, hTWF, hMon, net_trans_star.refl N, hWF, hNS, hRP⟩
  have hex : ∃ k, CoreConfig N p k := ⟨Q.length, N, Q, hInv0, rfl⟩
  obtain ⟨Nstar, Qcore, hInvstar, hk⟩ := Nat.find_spec hex
  have hMin : ∀ k, k < Qcore.length → ¬ CoreConfig N p k :=
    fun k hlt => Nat.find_min hex (hk ▸ hlt)
  have hInvstar0 := hInvstar
  obtain ⟨Tstar, Qextrastar, hmemstar, hCstar, _, _, hStar0, hWFstar, _, _⟩ := hInvstar0
  have hQne : Qcore ≠ [] := fun hQ => cannotRec_nil_absurd (by simp) hCstar hQ
  obtain ⟨⟨q0, lab0, S0⟩, restcore, hQcore⟩ := List.exists_cons_of_ne_nil hQne
  have hm0 : QueueMessage.msg q0 lab0 S0 ∈ Qcore := by
    rw [hQcore]
    exact List.mem_cons.mpr (Or.inl rfl)
  have hne : round_robin_roles Nstar ≠ [] := by
    have h1 : p ∈ Nstar.map Prod.fst :=
      List.mem_map.mpr ⟨(p, (Tstar, Qcore ++ Qextrastar)), hmemstar, rfl⟩
    exact List.ne_nil_of_mem (List.mem_eraseDups.mpr h1)
  by_cases hBdd : ∃ K, ∀ j, turnBound Nstar (FixedCoreInv N p Qcore)
      (fixedCore_drain_preserve hMin) (fixedCore_policy hHD) hWFstar hInvstar j ≤ K
  · obtain ⟨Nst, hStuck, hReach, hInvSt⟩ :=
      turn_run_stuck Nstar (FixedCoreInv N p Qcore)
        (fixedCore_drain_preserve hMin) (fixedCore_policy hHD) hWFstar hInvstar
        (hne := hne) hBdd
    obtain ⟨Tst, Qextrast, hmemSt, _, _, _, _, _, _, _⟩ := hInvSt
    have hQstNe : Qcore ++ Qextrast ≠ [] :=
      fun h => hQne (List.append_eq_nil_iff.mp h).1
    intro hLive
    exact stuck_orphan_nonlive hStuck hmemSt hQstNe
      (output_live_persistent hWF hLive (hStar0.trans hReach))
  · push Not at hBdd
    have hUnbdd : ∀ K, ∃ j, K < turnBound Nstar (FixedCoreInv N p Qcore)
        (fixedCore_drain_preserve hMin) (fixedCore_policy hHD) hWFstar hInvstar j :=
      fun K => by
        obtain ⟨j, hj⟩ := hBdd K
        exact ⟨j, by omega⟩
    obtain ⟨path, h0, hfair, hlab⟩ :=
      turn_run_fair Nstar (FixedCoreInv N p Qcore)
        (fixedCore_drain_preserve hMin) (fixedCore_policy hHD) hWFstar hInvstar
        (hne := hne) hUnbdd
    have hmemPath0 : NetworkHasQueue (path.seq 0) p (Qcore ++ Qextrastar) :=
      ⟨Tstar, by rw [h0]; exact hmemstar⟩
    have hDeq : (Qcore ++ Qextrastar).dequeue (QueueMessage.msg q0 lab0 S0) =
        some (restcore ++ Qextrastar) := by
      rw [hQcore, List.cons_append]
      simp [Queue.dequeue, Queue.dequeue.go]
    have hNev : ∀ k, 0 ≤ k → path.δ k ≠ net_label.τ_dequeue p q0 lab0 S0 := by
      intro k _
      rw [hlab k]
      exact fixedCore_flatLbl_ne hHD hMin hm0 hWFstar hInvstar hUnbdd k
    intro hLive
    have hLivestar : IsOutputLiveNetwork Nstar :=
      output_live_persistent hWF hLive hStar0
    exact pinned_label_violates hmemPath0 ⟨_, hDeq⟩ hNev
      (hLivestar.1 path h0 hfair)

end UnconditionalNonLive
