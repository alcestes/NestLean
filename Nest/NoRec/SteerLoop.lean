import Nest.SessionUtils
import Nest.NoRec.NoRecEncoder
import Nest.MonitorToolkit
import Nest.NoRec.DeepComplement
import Nest.NoRec.DrainSurvival

/-!
# tEnd/non-live starters, overTrStuck evidence, dequeue-blocking and queue-persistence helpers.
-/


-- ================================================================
-- Dead `(tEnd, _)` entries refute liveness, via
-- `msg_always_present_imples_not_output_live_norec` (all stuck/orphan
-- assembly internal to it), plus `QueueMem` persistence of
-- the dead entry's head message along stars.
-- ================================================================

section over_trans_traces

/-- Overapprox traces split at any point: a trace over `l1 ++ l2` factors through an intermediate
   state. -/
theorem over_trans_trace_split {stq stq'' : SessionTypeWithQueue} {l1 l2 : List st_label}
    (h : over_trans_trace stq (l1 ++ l2) stq'') :
    ∃ stq', over_trans_trace stq l1 stq' ∧ over_trans_trace stq' l2 stq'' := by
  induction l1 generalizing stq with
  | nil => exact ⟨stq, over_trans_trace.refl stq, h⟩
  | cons a t ih =>
    cases h with
    | step hStep hTail =>
      obtain ⟨mid, h1, h2⟩ := ih hTail
      exact ⟨mid, over_trans_trace.step hStep h1, h2⟩


/-- An overapprox trace with a distinguished step factors into prefix, that step, and suffix. -/
theorem over_trans_trace_suffix {stq stq'' : SessionTypeWithQueue}
    {pre : List st_label} {l : st_label} {suf : List st_label}
    (h : over_trans_trace stq (pre ++ l :: suf) stq'') :
    ∃ stqPre stqPost, over_trans_trace stq pre stqPre ∧ over_trans stqPre l stqPost ∧
      over_trans_trace stqPost suf stq'' := by
  obtain ⟨stqPre, hPre, hRest⟩ := over_trans_trace_split (l1 := pre) (l2 := l :: suf) h
  cases hRest with
  | step hStep hTail => exact ⟨stqPre, _, hPre, hStep, hTail⟩


/-- Queues only shrink along overapprox traces (dequeuing drops the head message). -/
theorem over_trans_trace_length_le {stq stq' : SessionTypeWithQueue} {ρ : List st_label}
    (h : over_trans_trace stq ρ stq') : stq'.2.length ≤ stq.2.length := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | @step stq mid stq' α ρ hStep hTail ih =>
    obtain ⟨Tmid, Qmid⟩ := mid
    cases hStep with
    | dequeue hEq hmem hQ =>
      have hlen := Queue.dequeue_length_drop hQ
      dsimp only at ih hlen ⊢
      omega
    | specInp hEq hmem hAbs => exact ih
    | sendFresh hEq hST hFresh => exact ih
    | tauUnfold _ => exact ih



end over_trans_traces

section TEndStarters

/-- Single-step `(tEnd, _)` + `QueueMem` preservation: steps touching `q`
    either die (`st_trans`-absurdity for sends/dequeues) or append behind `m`;
    other roles' steps transport the entry exactly. -/

private lemma tEnd_queueMem_step {N N' : Network} {δ : net_label} {q : Role} {m : QueueMessage}
    (hTr : net_trans N δ N') (hWF : N.WellFormed)
    (hmem : ∃ Q1, (q, (SessionType.tEnd, Q1)) ∈ N ∧ QueueMem m Q1) :
    ∃ Q1, (q, (SessionType.tEnd, Q1)) ∈ N' ∧ QueueMem m Q1 := by
  obtain ⟨Q1, hmemT, hqm⟩ := hmem
  cases hTr with
  | @io_send r p stq stq' lab S hSQ hmem0 =>
    by_cases heq : q = r
    · subst heq
      have heq0 : stq = (SessionType.tEnd, Q1) :=
        network_mem_unique hWF hmem0 hmemT
      rw [heq0] at hSQ
      cases hSQ with
      | @send T0 T0' Q0 _ _ _ hST =>
        exact absurd hST st_trans_t_end_absurd
    · exact ⟨Q1, mem_replace_other hmemT heq, hqm⟩
  | @io_recv r p stq stq' lab S hSQ hmem0 =>
    by_cases heq : q = r
    · subst heq
      have heq0 : stq = (SessionType.tEnd, Q1) :=
        network_mem_unique hWF hmem0 hmemT
      rw [heq0] at hSQ
      cases hSQ with
      | recv =>
        exact ⟨Q1 ++ [QueueMessage.msg p lab S], by unfold Network.replace; simp,
          queueMem_append_left hqm⟩
    · exact ⟨Q1, mem_replace_other hmemT heq, hqm⟩
  | @dequeue r p stq stq' lab S hSQ hmem0 =>
    by_cases heq : q = r
    · subst heq
      have heq0 : stq = (SessionType.tEnd, Q1) :=
        network_mem_unique hWF hmem0 hmemT
      rw [heq0] at hSQ
      cases hSQ with
      | @dequeue T0 T0' Q0 Q0' _ _ _ hST hQ =>
        exact absurd hST st_trans_t_end_absurd
    · exact ⟨Q1, mem_replace_other hmemT heq, hqm⟩
  | @comm p rr lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    by_cases heq_p : q = p
    · subst heq_p
      have heq0 : stqp = (SessionType.tEnd, Q1) :=
        network_mem_unique hWF hmem_p hmemT
      rw [heq0] at h_send
      cases h_send with
      | @send T0 T0' Q0 _ _ _ hST =>
        exact absurd hST st_trans_t_end_absurd
    · by_cases heq_r : q = rr
      · subst heq_r
        have heq0 : stqq = (SessionType.tEnd, Q1) :=
          network_mem_unique hWF hmem_q hmemT
        rw [heq0] at h_recv
        cases h_recv with
        | recv =>
          exact ⟨Q1 ++ [QueueMessage.msg p lab S], by unfold Network.replace; simp,
            queueMem_append_left hqm⟩
      · have hmid : (q, (SessionType.tEnd, Q1)) ∈ N.replace p stqp' :=
          mem_replace_other hmemT heq_p
        exact ⟨Q1, mem_replace_other hmid heq_r, hqm⟩


/-- Star-level `(tEnd, _)` + `QueueMem` tracking (well-formedness threads
    alongside for the uniqueness steps). -/
private lemma tEnd_queueMem_star {N1 N'' : Network} {q : Role} {m : QueueMessage}
    (hStar : net_trans_star N1 N'') (hWF1 : N1.WellFormed)
    (hmem : ∃ Q1, (q, (SessionType.tEnd, Q1)) ∈ N1 ∧ QueueMem m Q1) :
    ∃ Q1, (q, (SessionType.tEnd, Q1)) ∈ N'' ∧ QueueMem m Q1 := by
  revert hmem
  revert hWF1
  induction hStar with
  | refl =>
    intro hWF1 hmem
    exact hmem
  | step hInt hTr _ ih =>
    intro hWF1 hmem
    exact ih (Network.wellFormedPreserved _ _ _ hWF1 hTr hInt)
      (tEnd_queueMem_step hTr hWF1 hmem)


/-- A `QueueMem` message in a dead entry kills liveness (persistence +
    `msg_always_present_imples_not_output_live_norec`). -/
lemma tEnd_queueMem_not_live_norec {Ni N1 : Network} {q : Role} {Q : Queue} {m : QueueMessage}
    (hNR : Ni.NoRec) (hWF : Ni.WellFormed)
    (hStar : net_trans_star Ni N1) (hmem : (q, (SessionType.tEnd, Q)) ∈ N1)
    (hqm : QueueMem m Q) : ¬ IsOutputLiveNetwork Ni := by
  have hPersist : ∀ N'' T'' Q'', net_trans_star N1 N'' → (q, (T'', Q'')) ∈ N'' →
      QueueMem m Q'' := by
    intro N'' T'' Q'' hStar' hmem''
    obtain ⟨Q1, htrk, hqm1⟩ := tEnd_queueMem_star hStar' (wf_star hWF hStar)
      ⟨Q, hmem, hqm⟩
    have hWF'' : N''.WellFormed := wf_star (wf_star hWF hStar) hStar'
    have heq : (T'', Q'') = (SessionType.tEnd, Q1) :=
      network_mem_unique hWF'' hmem'' htrk
    have hQeq : Q'' = Q1 := congrArg Prod.snd heq
    subst hQeq
    exact hqm1
  exact msg_always_present_imples_not_output_live_norec hNR hWF hStar hmem hPersist


/-- A reachable dead entry with a nonempty queue refutes liveness. -/
lemma tEnd_nonempty_not_live_norec {Ni N1 : Network} {q : Role} {Q : Queue}
    (hNR : Ni.NoRec) (hWF : Ni.WellFormed)
    (hStar : net_trans_star Ni N1) (hmem : (q, (SessionType.tEnd, Q)) ∈ N1)
    (hne : Q ≠ []) : ¬ IsOutputLiveNetwork Ni := by
  obtain ⟨m, Q', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact tEnd_queueMem_not_live_norec hNR hWF hStar hmem QueueMem.head


/-- A no-orphan network has all queues empty: any nonempty queue's head is
    dequeueable (`Queue.dequeue_head_hit`), contradicting `NoOrphanMessages`.
    Closes the stuck-configuration half of the liveness contradiction. -/
theorem noOrphanMessages_nonempty_false {N : Network} {r : Role} {T : SessionType}
    {Q : Queue} (hNo : NoOrphanMessages N) (hmem : (r, (T, Q)) ∈ N)
    (hne : Q ≠ []) : False := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨p, lab, S⟩ := hd
  exact hNo r T (QueueMessage.msg p lab S :: tl) p lab S tl hmem
    Queue.dequeue_head_hit


/-- Example of `¬robust`: an ended session with a leftover message admits no
    overapprox step at all (`tEnd` has no `st_trans`), so with a nonempty queue no
    drain trace exists — robustness already fails at the drain half. -/
theorem not_robust_tEnd_nonempty {Q : Queue}
    (hne : Q ≠ []) : ¬ CanAlwaysDrainInternalDeep SessionType.tEnd Q := by
  intro h
  obtain ⟨T', ρ, hT⟩ := h.drains
  cases hT with
  | refl _ => exact hne rfl
  | step hStep _ =>
    cases hStep with
    | dequeue hEq _ _ => cases hEq
    | specInp hEq _ _ => cases hEq
    | sendFresh _ hST _ => exact absurd hST st_trans_t_end_absurd
    | tauUnfold hU => cases hU

/-- Concrete instance: ended `q`-side holding one orphan message. -/
example : ¬ CanAlwaysDrainInternalDeep SessionType.tEnd [QueueMessage.msg "q" "a" "s"] :=
  not_robust_tEnd_nonempty (by simp)

end TEndStarters

section QueuePersistence

/-- Failing-branch firing: an `intC` branch whose receiver is present
    fires as a network `τ_comm` step (needs distinct roles; receiver presence
    comes from `RolesPresent` via `T.Occurs`). -/
theorem intC_fire_as_tau_comm {N : Network} {r : Role} {T : SessionType} {Q : Queue}
    {branches : List (Role × Lab × DataSort × SessionType)}
    {s : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (hmemN : (r, (T, Q)) ∈ N)
    (hEq : T = SessionType.internalChoice branches)
    (hmemB : (s, lab, S, T') ∈ branches)
    (hne : s ≠ r)
    {stqs : SessionTypeWithQueue} (hmemS : (s, stqs) ∈ N) :
    ∃ N', net_trans N (net_label.τ_comm r s lab S) N' ∧ (r, (T', Q)) ∈ N' ∧
      (s, (stqs.1, stqs.2 ++ [QueueMessage.msg r lab S])) ∈ N' := by
  subst hEq
  refine ⟨_, net_trans.comm (p := r) (q := s) hne.symm
    (sq_trans.send (st_trans.intC hmemB)) sq_trans.recv hmemN hmemS, ?_, ?_⟩
  · have hmid : (r, (T', Q)) ∈ N.replace r (T', Q) := by
      unfold Network.replace
      simp
    exact mem_replace_other hmid (Ne.symm hne)
  · unfold Network.replace
    simp




-- ================================================================
-- over_trans-stuck states vs network hypotheses.
-- ================================================================

/-- List membership gives queue membership (direct induction on the queue). -/
private theorem mem_toQueueMem {m : QueueMessage} {Q : Queue} (h : m ∈ Q) :
    QueueMem m Q := by
  induction Q with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact QueueMem.head
    · exact QueueMem.tail (ih h)


/-- An over_trans-stuck `internalChoice` forces a freshness-blocking sender
    present in the queue: `dequeue`/`specInp` need `inp` (impossible from
    `intC`), so if `sendFresh` never fires either, freshness must fail.
    Needs a branch to build the would-be step (empty `intC` is stuck for
    lack of `st_trans`; that case goes the liveness route instead). -/
theorem overTrStuck_intC_blockedSender {T : SessionType} {Q : Queue}
    {branches : List (Role × Lab × DataSort × SessionType)}
    (hEq : T = SessionType.internalChoice branches)
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue), ¬ over_trans (T, Q) α stq')
    {br : Role × Lab × DataSort × SessionType} (hmemB : br ∈ branches) :
    ∃ (s0 : Role) (l0 : Lab) (S0 : DataSort) (U0 : SessionType) (m : QueueMessage),
      (s0, l0, S0, U0) ∈ branches ∧ m ∈ Q ∧ m.1 = s0 := by
  subst hEq
  by_contra hCon
  have hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r' := by
    intro r' l' s' U hmem m hm heq
    exact hCon ⟨r', l', s', U, m, hmem, hm, heq⟩
  obtain ⟨p, lab, S, T0⟩ := br
  exact hNo _ _ (over_trans.sendFresh rfl (st_trans.intC hmemB) hFresh)


/-- An over_trans-stuck `internalChoice` entry forces a half-duplex violation:
    the freshness-blocking branch's send is enabled as a network `τ_comm`
    (sends need no freshness), and its successor has messages flowing both
    ways. Hence half-duplex (+ presence, no-self) rules out over_trans-stuck
    nonempty-queue `intC` states. -/
theorem overTrStuck_intC_hd_false {r : Role} {T : SessionType} {Q : Queue}
    {N : Network}
    {branches : List (Role × Lab × DataSort × SessionType)}
    {br : Role × Lab × DataSort × SessionType}
    (hEq : T = SessionType.internalChoice branches)
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue), ¬ over_trans (T, Q) α stq')
    (hmemB : br ∈ branches)
    (hmemN : (r, (T, Q)) ∈ N)
    (hNS : N.NoSelf) (hPres : N.RolesPresent) :
    ¬ IsHalfDuplex N := by
  subst hEq
  obtain ⟨s0, l0, S0, U0, m, hmemS0, hmQ, hsender⟩ :=
    overTrStuck_intC_blockedSender rfl hNo hmemB
  have hne : s0 ≠ r := by
    intro heq
    apply (hNS r _ _ hmemN)
    exact SessionType.Occurs.intSender hmemS0 heq
  have hoccS0 : (SessionType.internalChoice branches).Occurs s0 :=
    SessionType.Occurs.intSender hmemS0 rfl
  obtain ⟨⟨T0, Q0⟩, hmemS0N⟩ := hPres r _ _ s0 hmemN hoccS0
  have hComm : net_trans N (net_label.τ_comm r s0 l0 S0)
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) :=
    net_trans.comm (Ne.symm hne) (sq_trans.send (st_trans.intC hmemS0)) sq_trans.recv hmemN hmemS0N
  intro hHD
  have hStar : net_trans_star N
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) :=
    net_trans_star.step (by simp [is_internal_net_label]) hComm (net_trans_star.refl _)
  have hmemR : (r, (U0, Q)) ∈
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) :=
    mem_replace_other (List.mem_cons.mpr (Or.inl rfl)) (Ne.symm hne)
  have hmemS : (s0, (T0, Q0 ++ [QueueMessage.msg r l0 S0])) ∈
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hHasR : NetworkHasQueue
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) r Q :=
    ⟨U0, hmemR⟩
  have hHasS : NetworkHasQueue
      ((N.replace r (U0, Q)).replace s0 (T0, Q0 ++ [QueueMessage.msg r l0 S0])) s0
      (Q0 ++ [QueueMessage.msg r l0 S0]) :=
    ⟨T0, hmemS⟩
  have hC1 : QueueContainsFrom (Q0 ++ [QueueMessage.msg r l0 S0]) r :=
    ⟨l0, S0, queueMem_append_single _ _⟩
  have hC2 := hHD _ hStar s0 r _ _ hHasS hHasR hC1
  obtain ⟨p', lab', S'⟩ := m
  have hp' : p' = s0 := hsender
  subst hp'
  exact hC2 ⟨lab', S', mem_toQueueMem hmQ⟩


-- ================================================================
-- Permanence: st_trans-free sessions never move except by receives.
-- ================================================================

/-- Single-step transport: a role whose session admits no `st_trans` steps
    keeps its session along any τ-step; its queue only grows by tail
    appends (dequeues/sends need `st_trans`, hence are impossible; receives
    append). `io` steps are pruned by internality. Needs well-formedness
    to align the step's session with ours (role uniqueness). -/
theorem nost_trans_entry_step {r : Role} {T : SessionType} {Q Qcur : Queue}
    {N N' : Network} {δ : net_label}
    (hST : ∀ (α : st_label) (T' : SessionType), ¬ st_trans T α T')
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ) (hWF : N.WellFormed)
    (hmem : (r, (T, Qcur)) ∈ N) (hsub : ∀ m ∈ Q, m ∈ Qcur) :
    ∃ Q'', (r, (T, Q'')) ∈ N' ∧ ∀ m ∈ Q, m ∈ Q'' := by
  cases hTr with
  | io_send _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ => simp [is_internal_net_label] at hInt
  | @dequeue r' p stq stq' lab S h hmem' =>
    by_cases heq : r' = r
    · rw [heq] at hmem'
      have hstq : stq = (T, Qcur) := network_mem_unique hWF hmem' hmem
      subst hstq
      cases h with
      | dequeue hST' hQ => exact absurd hST' (hST _ _)
    · exact ⟨Qcur, mem_replace_other hmem (Ne.symm heq), hsub⟩
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    by_cases heqp : r = p
    · rw [←heqp] at hmem_p
      have hstqp : stqp = (T, Qcur) := network_mem_unique hWF hmem_p hmem
      subst hstqp
      cases h_send with
      | send hST' => exact absurd hST' (hST _ _)
    · by_cases heqq : r = q
      · subst heqq
        have hstqq : stqq = (T, Qcur) := network_mem_unique hWF hmem_q hmem
        subst hstqq
        cases h_recv with
        | recv =>
          exact ⟨Qcur ++ [QueueMessage.msg p lab S],
            List.mem_cons.mpr (Or.inl rfl),
            fun m hm => List.mem_append.mpr (Or.inl (hsub m hm))⟩
      · exact ⟨Qcur,
          mem_replace_other (mem_replace_other hmem heqp) heqq, hsub⟩


-- ================================================================
-- Spec-only-to-dead exclusion (liveness route, second shape).
-- ================================================================




-- ================================================================
-- Progress: network hypotheses rule out over_trans-stuck nonempty states.
-- ================================================================

-- ================================================================
-- Scan-block persistence (extC-stuck route).
-- ================================================================


end QueuePersistence

section DequeueBlocking

/-- A scan that skips a prefix and dies at a same-sender mismatch fails
    regardless of the `seen` accumulator or the tail. -/
theorem Queue.dequeue_go_blocked (seen pre : Queue) (m0 : QueueMessage) (suf : Queue)
    (msg : QueueMessage)
    (hpre : ∀ x ∈ pre, x ≠ msg ∧ x.1 ≠ msg.1)
    (hne : m0 ≠ msg) (hsame : m0.1 = msg.1) :
    Queue.dequeue.go seen (pre ++ m0 :: suf) msg = none := by
  induction pre generalizing seen with
  | nil =>
    simp only [List.nil_append] at *
    simp [Queue.dequeue.go, hne, hsame]
  | cons hd tl ih =>
    have hhd := hpre hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ x ∈ tl, x ≠ msg ∧ x.1 ≠ msg.1 :=
      fun x hx => hpre x (List.mem_cons.mpr (Or.inr hx))
    have estep : Queue.dequeue.go seen ((hd :: tl) ++ m0 :: suf) msg =
        Queue.dequeue.go (seen ++ [hd]) (tl ++ m0 :: suf) msg := by
      simp [Queue.dequeue.go, hhd.1, hhd.2]
    rw [estep]
    exact ih _ htl


/-- A failed scan with a same-sender message present must die at a
    same-sender mismatch (not by exhaustion): the first same-sender
    message either matches (contradicting failure) or blocks, and
    exhaustion would mean no such message exists. -/
theorem Queue.dequeue_fail_block (Q : Queue) (msg : QueueMessage)
    (hfail : Q.dequeue msg = none)
    (hex : ∃ m ∈ Q, m.1 = msg.1) :
    ∃ pre m0 suf, Q = pre ++ m0 :: suf ∧
      (∀ x ∈ pre, x ≠ msg ∧ x.1 ≠ msg.1) ∧ m0 ≠ msg ∧ m0.1 = msg.1 := by
  have key : ∀ (seen : Queue) (Q : Queue),
      Queue.dequeue.go seen Q msg = none → (∃ m ∈ Q, m.1 = msg.1) →
      ∃ pre m0 suf, Q = pre ++ m0 :: suf ∧
        (∀ x ∈ pre, x ≠ msg ∧ x.1 ≠ msg.1) ∧ m0 ≠ msg ∧ m0.1 = msg.1 := by
    intro seen Q
    induction Q generalizing seen with
    | nil =>
      intro _ hex0
      obtain ⟨m, hm, _⟩ := hex0
      simp at hm
    | cons hd tl ih =>
      intro hfail hex0
      by_cases heq : hd = msg
      · subst heq
        simp [Queue.dequeue.go] at hfail
      · by_cases hsame : hd.1 = msg.1
        · exact ⟨[], hd, tl, rfl,
            fun x hx => by simp at hx, heq, hsame⟩
        · have hstep : Queue.dequeue.go seen (hd :: tl) msg =
              Queue.dequeue.go (seen ++ [hd]) tl msg := by
            simp [Queue.dequeue.go, heq, hsame]
          have hfail' : Queue.dequeue.go (seen ++ [hd]) tl msg = none := by
            rw [← hstep]; exact hfail
          have hex_tl : ∃ m ∈ tl, m.1 = msg.1 := by
            obtain ⟨m, hmem, hsender⟩ := hex0
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd hsender hsame
            · exact ⟨m, hmem, hsender⟩
          obtain ⟨pre, m0, suf, hsplit, hpre, hne, hsame'⟩ := ih _ hfail' hex_tl
          refine ⟨hd :: pre, m0, suf, ?_, ?_, hne, hsame'⟩
          · simp only [List.cons_append]
            rw [hsplit]
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨heq, hsame⟩
            · exact hpre x hx
  exact key [] Q (by simpa [Queue.dequeue] using hfail) hex


/-- An over_trans-stuck `externalChoice` with a branch present contradicts
    liveness: absence must already fail for the owner role (else some
    `specInp` fires), so a same-role message is present; dequeue scans for
    offered keys all die at same-sender mismatches (a match would fire),
    hence appends never unblock them and sends don't exist — the role only
    grows its queue, head fixed, always dequeueable. -/
theorem overTrStuck_extC_live_false_norec {r p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {T : SessionType} {Q : Queue} {N : Network}
    {br : Lab × DataSort × SessionType}
    (hEq : T = SessionType.externalChoice p branches)
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue), ¬ over_trans (T, Q) α stq')
    (hmemB : br ∈ branches)
    (hmemN : (r, (T, Q)) ∈ N)
    (hLive : IsOutputLiveNetwork N)
    (hNR : N.NoRec) (hWF : N.WellFormed) :
    False := by
  subst hEq
  obtain ⟨l0, S0, T0⟩ := br
  have habs : ∃ m ∈ Q, m.1 = p := by
    by_contra hC
    have hAbs : ∀ m ∈ Q, m.1 ≠ p := by
      intro m hm
      by_contra heq2
      exact hC ⟨m, hm, heq2⟩
    exact hNo _ _ (over_trans.specInp rfl hmemB hAbs)
  have hscan0 : ∀ (l : Lab) (s : DataSort) (T' : SessionType),
      (l, s, T') ∈ branches →
      Q.dequeue (QueueMessage.msg p l s) = none := by
    intro l s T' hmem
    by_contra hC
    match he : Q.dequeue (QueueMessage.msg p l s) with
    | some Q' => exact hNo _ _ (over_trans.dequeue rfl hmem he)
    | none => exact absurd he hC
  have htrans : ∀ (M M' : Network), net_trans_star M M' → M.WellFormed →
      ∀ (Qcur : Queue), (r, (SessionType.externalChoice p branches, Qcur)) ∈ M →
      (∀ (l : Lab) (s : DataSort) (T' : SessionType),
        (l, s, T') ∈ branches → Qcur.dequeue (QueueMessage.msg p l s) = none) →
      (∃ m ∈ Qcur, m.1 = p) →
      ∃ Q'', (r, (SessionType.externalChoice p branches, Q'')) ∈ M' ∧
        (∀ (l : Lab) (s : DataSort) (T' : SessionType),
          (l, s, T') ∈ branches → Q''.dequeue (QueueMessage.msg p l s) = none) ∧
        (∃ m ∈ Q'', m.1 = p) := by
    intro M M' hS
    induction hS with
    | refl => intro hWFM Qcur hmem hfail hpres; exact ⟨Qcur, hmem, hfail, hpres⟩
    | @step N1 N2 N3 δ hInt hTr hStar' ih =>
      intro hWFM Qcur hmem hfail hpres
      have hWF2 := Network.wellFormedPreserved N1 δ N2 hWFM hTr hInt
      cases hTr with
      | io_send _ _ => simp [is_internal_net_label] at hInt
      | io_recv _ _ => simp [is_internal_net_label] at hInt
      | @dequeue r' q stq stq' lab S h hmem' =>
        by_cases heq : r' = r
        · rw [heq] at hmem'
          have hstq : stq = (SessionType.externalChoice p branches, Qcur) :=
            network_mem_unique hWFM hmem' hmem
          subst hstq
          cases h with
          | dequeue hST' hQ =>
            cases hST' with
            | extC hmemK =>
              have hnone := hfail lab S _ hmemK
              rw [hQ] at hnone
              simp at hnone
        · have hmem2 : (r, (SessionType.externalChoice p branches, Qcur)) ∈
              N1.replace r' stq' :=
            mem_replace_other hmem (Ne.symm heq)
          obtain ⟨Q'', hmem'', hfail'', hpres''⟩ :=
            ih hWF2 Qcur hmem2 hfail hpres
          exact ⟨Q'', hmem'', hfail'', hpres''⟩
      | @comm p' q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
        by_cases heqp : r = p'
        · rw [←heqp] at hmem_p
          have hstqp : stqp =
              (SessionType.externalChoice p branches, Qcur) :=
            network_mem_unique hWFM hmem_p hmem
          subst hstqp
          cases h_send with
          | send hST' => cases hST'
        · by_cases heqq : r = q
          · subst heqq
            have hstqq : stqq =
                (SessionType.externalChoice p branches, Qcur) :=
              network_mem_unique hWFM hmem_q hmem
            subst hstqq
            cases h_recv with
            | recv =>
              have hmem1 : (r, (SessionType.externalChoice p branches,
                  Qcur ++ [QueueMessage.msg p' lab S])) ∈
                  (N1.replace p' stqp').replace r
                    (SessionType.externalChoice p branches,
                      Qcur ++ [QueueMessage.msg p' lab S]) :=
                List.mem_cons.mpr (Or.inl rfl)
              have hfail1 : ∀ (l : Lab) (s : DataSort) (T' : SessionType),
                  (l, s, T') ∈ branches →
                  (Qcur ++ [QueueMessage.msg p' lab S]).dequeue
                    (QueueMessage.msg p l s) = none := by
                intro l s T' hmemK
                obtain ⟨m0p, hm0p, hsenderp⟩ := hpres
                obtain ⟨pre, m0, suf, hsplit, hpre, hne', hsame⟩ :=
                  Queue.dequeue_fail_block Qcur (QueueMessage.msg p l s)
                    (hfail l s T' hmemK) ⟨m0p, hm0p, hsenderp⟩
                have happ : Qcur ++ [QueueMessage.msg p' lab S] =
                    pre ++ m0 :: (suf ++ [QueueMessage.msg p' lab S]) := by
                  simp [hsplit, List.append_assoc]
                rw [happ]
                have hgo := Queue.dequeue_go_blocked [] pre m0
                  (suf ++ [QueueMessage.msg p' lab S]) (QueueMessage.msg p l s)
                  hpre hne' hsame
                simpa [Queue.dequeue] using hgo
              have hpres1 : ∃ m ∈ Qcur ++ [QueueMessage.msg p' lab S], m.1 = p := by
                obtain ⟨m0p, hm0p, hsenderp⟩ := hpres
                exact ⟨m0p, List.mem_append.mpr (Or.inl hm0p), hsenderp⟩
              obtain ⟨Q'', hmem'', hfail'', hpres''⟩ :=
                ih hWF2 _ hmem1 hfail1 hpres1
              exact ⟨Q'', hmem'', hfail'', hpres''⟩
          · have hmem2 : (r, (SessionType.externalChoice p branches, Qcur)) ∈
                (N1.replace p' stqp').replace q stqq' :=
              mem_replace_other
                (mem_replace_other hmem heqp : (_, _) ∈ N1.replace p' stqp')
                heqq
            obtain ⟨Q'', hmem'', hfail'', hpres''⟩ :=
              ih hWF2 Qcur hmem2 hfail hpres
            exact ⟨Q'', hmem'', hfail'', hpres''⟩
  obtain ⟨N', hStar, hStuck⟩ := exists_stuck_reachable_of_NoRec hNR hWF
  obtain ⟨Q', hmem', hfail', hpres'⟩ :=
    htrans N N' hStar hWF Q hmemN hscan0 habs
  obtain ⟨m0, hm0, -⟩ := hpres'
  have hQne : Q' ≠ [] := List.ne_nil_of_mem hm0
  obtain ⟨hd', tl', hQ'eq⟩ := List.exists_cons_of_ne_nil hQne
  subst hQ'eq
  rcases hd' with ⟨p', lab', S'⟩
  have hscan : Queue.dequeue (QueueMessage.msg p' lab' S' :: tl')
      (QueueMessage.msg p' lab' S') = some tl' :=
    Queue.dequeue_head_hit
  exact hLive.2 N' hStar hStuck r _ _ p' lab' S' tl' hmem' hscan


/-- Cannot heads have nonempty queues (the witness end is nonempty and
    queues never grow along `over_trans`). -/
theorem cannot_head_nonempty {T : SessionType} {Q : Queue}
    (h : CannotAlwaysDrainInternalDeep T Q) : Q ≠ [] := by
  obtain ⟨Tn, Qn, ρ, hTr, hne, -, -⟩ := h
  intro hQ
  subst hQ
  have hle := over_trans_trace_length_le hTr
  simp at hle
  subst hle
  exact hne rfl


/-- No `st_trans` from empty `internalChoice`. -/
theorem nost_trans_int_c_nil :
    ∀ (α : st_label) (T' : SessionType),
      ¬ st_trans (SessionType.internalChoice []) α T' := by
  intro α T' h
  cases h with
  | intC hmem => simp at hmem


/-- No `st_trans` from empty `externalChoice`. -/
theorem nost_trans_ext_c_nil (p : Role) :
    ∀ (α : st_label) (T' : SessionType),
      ¬ st_trans (SessionType.externalChoice p []) α T' := by
  intro α T' h
  cases h with
  | extC hmem => simp at hmem


-- ================================================================
-- `Cannot` persists along queue extension.
-- ================================================================

/-- Queue extension preserves nonemptiness on the left. -/
theorem append_nonempty_left {Q extra : Queue} (hne : Q ≠ []) :
    Q ++ extra ≠ [] := by
  cases Q with
  | nil => exact absurd rfl hne
  | cons hd tl => simp


/-- Queue extension preserves nonemptiness on the right. -/
theorem append_nonempty_right {Q extra : Queue} (hne : extra ≠ []) :
    Q ++ extra ≠ [] := by
  cases extra with
  | nil => exact absurd rfl hne
  | cons hd tl => simp


end DequeueBlocking

/-!
# NoRec.SteerLoop: NoRec steering loop and non-liveness of deep failures.

Used by the NoRec soundness chain via `Nest.NoRec.CommCorrespondence`. The `tEnd_nonempty_not_live_norec`,
`overTrStuck_extC_live_false_norec`, `cannot_prepend_*` and queue-persistence
helpers are proved above; the shared shallow `Can` inductives and their bridges live in `Nest.SessionUtils`, the
`Cannot` inductives and prepend machinery in `Nest.NoRec.DrainCore` / `Nest.NoRec.DrainSurvival`
and are reused from there.
-/

section AppendPersist

/-- `Cannot` persists along queue extension: replay the witness trace
    from `(T, Q ++ extra)`; dequeues replay within `Q` (same key,
    result extended), specs replay while absence holds, sends replay
    while freshness holds; when extension messages block a step the
    state is stuck-nonempty (`cannot_of_nostep_norec`), and when an
    extension message converts a spec into a dequeue the target is
    bad by the head closure plus the outer size induction. Outer
    strong induction on `sizeOf T`, inner structural induction on
    the witness trace. -/
theorem cannot_append_persist_norec : ∀ (n : Nat) (T : SessionType) (Q extra : Queue),
    T.NoRec → T.WellFormed → sizeOf T ≤ n →
    CannotAlwaysDrainInternalDeep T Q →
    CannotAlwaysDrainInternalDeep T (Q ++ extra) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihOuter =>
    intro T Q extra hNR hWF hsize hC
    have replay : ∀ (ρ : List st_label) (T0 : SessionType) (Q0 : Queue)
        (Tn : SessionType) (Qn : Queue),
        over_trans_trace (T0, Q0) ρ (Tn, Qn) → Qn ≠ [] →
        (Tn = SessionType.tEnd ∨
          (∃ (branches : List (Role × Lab × DataSort × SessionType))
            (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
            (m : QueueMessage),
            Tn = SessionType.internalChoice branches ∧
            (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
          ((∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
            (lab : Lab) (S : DataSort) (m : QueueMessage),
            Tn = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
            m = QueueMessage.msg p lab S ∧
            ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
          (∃ (X : String) (B U : SessionType),
            Tn = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
            (U = SessionType.tEnd ∨
              (∃ (branches : List (Role × Lab × DataSort × SessionType))
                (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
                (m : QueueMessage),
                U = SessionType.internalChoice branches ∧
                (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
              (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
                (lab : Lab) (S : DataSort) (m : QueueMessage),
                U = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
                m = QueueMessage.msg p lab S ∧
                ∀ (T' : SessionType), (lab, S, T') ∉ branches))))) →
        (∀ (Ti : SessionType) (Qi : Queue) (σ1 σ2 : List st_label),
          over_trans_trace (T0, Q0) σ1 (Ti, Qi) →
          over_trans_trace (Ti, Qi) σ2 (Tn, Qn) →
          ρ = σ1 ++ σ2 →
          ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
            Ti = SessionType.internalChoice branches → branches ≠ [] →
            int_choice_fireable Ti Qi branches →
            ∃ (br : Role × Lab × DataSort × SessionType),
              br ∈ branches ∧ CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
          (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
            Ti = SessionType.externalChoice p branches → branches ≠ [] →
            (∀ m ∈ Qi, m.1 ≠ p) →
            ∀ (br : Lab × DataSort × SessionType),
              br ∈ branches → CannotAlwaysDrainInternalDeepCore br.2.2 Qi))) →
        T0.NoRec → T0.WellFormed → sizeOf T0 ≤ n →
        CannotAlwaysDrainInternalDeep T0 (Q0 ++ extra) := by
      intro ρ
      induction ρ with
      | nil =>
        intro T0 Q0 Tn Qn hTr hne hend hclos hNR0 hWF0 hsize0
        have heq0 := overTrTrace_nil_eq hTr
        have hTn : T0 = Tn := (congrArg Prod.fst heq0).symm
        have hQn : Q0 = Qn := (congrArg Prod.snd heq0).symm
        subst hTn
        subst hQn
        rcases hend with hT | hI | hA | hR
        · -- Ended head: still ended, still stuck.
          subst hT
          have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
              ¬ over_trans (SessionType.tEnd, Q0 ++ extra) α stq' := by
            intro α stq' hS
            cases hS with
            | dequeue hEq _ _ => cases hEq
            | specInp hEq _ _ => cases hEq
            | sendFresh hEq _ _ => cases hEq
            | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR0 hU
          exact cannot_of_nostep_norec hNR0 hWF0 hNo (append_nonempty_left hne)
        · obtain ⟨branches, p, lab, S, T', m, hTnEq, hmemB, hmemM,
            heqM⟩ := hI
          subst hTnEq
          have hmemA : m ∈ Q0 ++ extra :=
            List.mem_append.mpr (Or.inl hmemM)
          have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
              ¬ over_trans (SessionType.internalChoice branches, Q0 ++ extra)
                α stq' := by
            intro α stq' hS
            cases hS with
            | dequeue hEq _ _ => cases hEq
            | specInp hEq _ _ => cases hEq
            | sendFresh _hEq _hST hFresh =>
              cases _hEq with
              | refl =>
                exact absurd heqM (hFresh _ _ _ _ hmemB _ hmemA)
            | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR0 hU
          exact cannot_of_nostep_norec hNR0 hWF0 hNo (append_nonempty_left hne)
        · obtain ⟨p, branches, lab0, S0, m0, hTnEq, hOld, hmeq,
            habsK⟩ := hA
          subst hTnEq
          obtain ⟨seen, rest, hQeq, hm1, hseen⟩ := hOld
          have hOldA : oldest_from p (Q0 ++ extra) m0 := by
            refine ⟨seen, rest ++ extra, ?_, hm1, hseen⟩
            simp [hQeq, List.append_assoc, List.cons_append]
          have hmemM0 : m0 ∈ Q0 ++ extra := by
            have hmem0 : m0 ∈ Q0 := by rw [hQeq]; simp
            exact List.mem_append.mpr (Or.inl hmem0)
          have hm1b : m0.1 = p := by rw [hmeq]
          have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
              ¬ over_trans (SessionType.externalChoice p branches, Q0 ++ extra)
                α stq' := by
            intro α stq' hS
            cases hS with
            | @dequeue _ _ _ _ _ lab S _ hEq hmem hQd =>
              injection hEq with hpeq hbeq'
              subst hpeq
              subst hbeq'
              obtain ⟨seen', left', hQeq', hseen'⟩ :=
                dequeue_oldest_of_some hQd
              have hOld' : oldest_from p (Q0 ++ extra)
                  (QueueMessage.msg p lab S) :=
                ⟨seen', left', hQeq', rfl, hseen'⟩
              have hEqK := oldest_from_unique hOld' hOldA
              rw [hmeq] at hEqK
              rw [QueueMessage.msg.injEq] at hEqK
              obtain ⟨-, rfl, rfl⟩ := hEqK
              exact (habsK _ hmem).elim
            | specInp hEq hmem hAbs =>
              injection hEq with hpeq hbeq'
              subst hpeq
              subst hbeq'
              exact (hAbs _ hmemM0 hm1b).elim
            | sendFresh hEq _ _ => cases hEq
            | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR0 hU
          exact cannot_of_nostep_norec hNR0 hWF0 hNo (append_nonempty_left hne)
        · -- `tRec` end is impossible under `NoRec`.
          obtain ⟨X, B, _, hTnEq, -, -⟩ := hR
          subst hTnEq
          cases hNR0
      | cons α ρ' ihρ =>
        intro T0 Q0 Tn Qn hTr hne hend hclos hNR0 hWF0 hsize0
        obtain ⟨stqPre, stqPost, hPre, hStep, hTail⟩ :=
          over_trans_trace_suffix (pre := []) (l := α) (suf := ρ') hTr
        have hPreEq := overTrTrace_nil_eq hPre
        subst hPreEq
        rcases stqPost with ⟨T1, Q1⟩
        cases hStep with
        | @dequeue _ _ _ _ p lab S branchesW hEq hmem hQd =>
          -- Same key replays within `Q0` (result extended by `extra`).
          obtain ⟨seen, left, hQeq, hQ1eq, hseen⟩ :=
            queue_dequeue_some_iff hQd
          have hQeqA : Q0 ++ extra =
              seen ++ QueueMessage.msg p lab S :: (left ++ extra) := by
            simp [hQeq, List.append_assoc, List.cons_append]
          have hseenP : ∀ m ∈ seen, m.1 ≠ p := by simpa using hseen
          have hgo : Queue.dequeue.go [] (Q0 ++ extra)
              (QueueMessage.msg p lab S) =
              some ([] ++ seen ++ (left ++ extra)) := by
            rw [hQeqA]
            exact dequeue_skip_seen hseenP
          have hQdW : (Q0 ++ extra).dequeue (QueueMessage.msg p lab S) =
              some (Q1 ++ extra) := by
            have hfold : Q1 ++ extra = [] ++ seen ++ (left ++ extra) := by
              simp [hQ1eq, List.append_assoc]
            rw [hfold]
            simp only [Queue.dequeue]
            exact hgo
          have hStep1 : over_trans (T0, Q0) (st_label.inp p lab S) (T1, Q1) :=
            over_trans.dequeue hEq hmem hQd
          have h1 : over_trans_trace (T0, Q0) [st_label.inp p lab S] (T1, Q1) :=
            over_trans_trace.step hStep1 (over_trans_trace.refl _)
          have hNR1 : T1.NoRec := over_trans_preserves_norec hStep1 hNR0
          have hWF1 : T1.WellFormed := over_trans_preserves_wf hStep1 hWF0
          have hsize1 : sizeOf T1 ≤ n :=
            le_trans (le_of_lt (over_trans_session_shrink_norec hStep1 hNR0)) hsize0
          have hclos' : ∀ (Ti : SessionType) (Qi : Queue)
              (σ1 σ2 : List st_label),
              over_trans_trace (T1, Q1) σ1 (Ti, Qi) →
              over_trans_trace (Ti, Qi) σ2 (Tn, Qn) →
              ρ' = σ1 ++ σ2 →
              ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
                Ti = SessionType.internalChoice branches → branches ≠ [] →
                int_choice_fireable Ti Qi branches →
                ∃ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches ∧
                  CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
              (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
                Ti = SessionType.externalChoice p branches → branches ≠ [] →
                (∀ m ∈ Qi, m.1 ≠ p) →
                ∀ (br : Lab × DataSort × SessionType),
                  br ∈ branches →
                  CannotAlwaysDrainInternalDeepCore br.2.2 Qi)) := by
            intro Ti Qi σ1 σ2 g1 g2 geq2
            exact hclos Ti Qi ([st_label.inp p lab S] ++ σ1) σ2
              (over_trans_trace_append h1 g1) g2
              (by simp [geq2, List.cons_append])
          have hTailC := ihρ T1 Q1 Tn Qn hTail hne hend hclos' hNR1
            hWF1 hsize1
          subst hEq
          have hND : (SessionType.externalChoice p branchesW).NoDupl :=
            hWF0.1
          have hStepW : over_trans (SessionType.externalChoice p branchesW,
              Q0 ++ extra) (st_label.inp p lab S) (T1, Q1 ++ extra) :=
            over_trans.dequeue rfl hmem hQdW
          exact cannot_prepend_dequeue_at_extC hND hmem hQdW hTailC
        | @specInp _ _ _ p lab S branches hEq hmem hAbs =>
          subst hEq
          have hStep1 : over_trans (SessionType.externalChoice p branches, Q0)
              (st_label.inp p lab S) (T1, Q0) :=
            over_trans.specInp rfl hmem hAbs
          have h1 : over_trans_trace (SessionType.externalChoice p branches, Q0)
              [st_label.inp p lab S] (T1, Q0) :=
            over_trans_trace.step hStep1 (over_trans_trace.refl _)
          have hNR1 : T1.NoRec :=
            over_trans_preserves_norec hStep1 hNR0
          have hWF1 : T1.WellFormed :=
            over_trans_preserves_wf hStep1 hWF0
          have hsize1 : sizeOf T1 ≤ n :=
            le_trans (le_of_lt (over_trans_session_shrink_norec hStep1 hNR0)) hsize0
          have hclos' : ∀ (Ti : SessionType) (Qi : Queue)
              (σ1 σ2 : List st_label),
              over_trans_trace (T1, Q0) σ1 (Ti, Qi) →
              over_trans_trace (Ti, Qi) σ2 (Tn, Qn) →
              ρ' = σ1 ++ σ2 →
              ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
                Ti = SessionType.internalChoice branches → branches ≠ [] →
                int_choice_fireable Ti Qi branches →
                ∃ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches ∧
                  CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
              (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
                Ti = SessionType.externalChoice p branches → branches ≠ [] →
                (∀ m ∈ Qi, m.1 ≠ p) →
                ∀ (br : Lab × DataSort × SessionType),
                  br ∈ branches →
                  CannotAlwaysDrainInternalDeepCore br.2.2 Qi)) := by
            intro Ti Qi σ1 σ2 g1 g2 geq2
            exact hclos Ti Qi ([st_label.inp p lab S] ++ σ1) σ2
              (over_trans_trace_append h1 g1) g2
              (by simp [geq2, List.cons_append])
          -- Head closure at `(T0, Q0)` for the spec key's branch set.
          have hHeadClos := hclos (SessionType.externalChoice p branches)
            Q0 [] _ (over_trans_trace.refl _) hTr rfl
          obtain ⟨-, hExtC⟩ := hHeadClos
          have hneB : branches ≠ [] := by
            intro hcon
            rw [hcon] at hmem
            simp at hmem
          by_cases hExtraP : ∃ m ∈ extra, m.1 = p
          · -- Owner arrives: oldest-`p` of the extension decides.
            obtain ⟨mp, hmpE, hm1E⟩ := hExtraP
            obtain ⟨m0, hOldE, hm1E0⟩ := oldest_of_mem extra p
              ⟨mp, hmpE, hm1E⟩
            obtain ⟨seenE, restE, hQeqE, hm1Eb, hseenE⟩ := hOldE
            obtain ⟨p0, lab0, S0⟩ := m0
            have hEqP : p = p0 := hm1E0.symm
            subst hEqP
            have hOldA : oldest_from p (Q0 ++ extra)
                (QueueMessage.msg p lab0 S0) := by
              refine ⟨Q0 ++ seenE, restE, ?_, rfl, ?_⟩
              · simp [hQeqE, List.append_assoc]
              · intro x hx
                rcases List.mem_append.mp hx with h | h
                · exact hAbs _ h
                · exact hseenE _ h
            by_cases hKey : ∃ T', (lab0, S0, T') ∈ branches
            · -- Present key: dequeue fires; target bad by closure + outer IH.
              obtain ⟨V', hmemV'⟩ := hKey
              have hQeqA : Q0 ++ extra =
                  (Q0 ++ seenE) ++ QueueMessage.msg p lab0 S0 :: restE := by
                simp [hQeqE, List.append_assoc]
              have hseenA : ∀ m ∈ Q0 ++ seenE, m.1 ≠ p := by
                intro x hx
                rcases List.mem_append.mp hx with h | h
                · exact hAbs _ h
                · exact hseenE _ h
              have hQdA : (Q0 ++ extra).dequeue
                  (QueueMessage.msg p lab0 S0) =
                  some ((Q0 ++ seenE) ++ restE) := by
                rw [hQeqA]
                simp only [Queue.dequeue]
                exact dequeue_skip_seen hseenA
              have hCoreV' := hExtC p branches rfl hneB hAbs
                (lab0, S0, V') hmemV'
              have hC0 : CannotAlwaysDrainInternalDeep V' Q0 :=
                hCoreV'.toDef
              have hNRV' : V'.NoRec :=
                noRec_of_mem_extBranches hNR0 hmemV'
              have hWFV' : V'.WellFormed :=
                wf_of_mem_extBranches hmemV' hWF0
              have hltV : sizeOf V' < n :=
                lt_of_lt_of_le
                  (sizeOf_SessionType_lt_sizeOf_externalChoice hmemV')
                  hsize0
              have hQeq2 : (Q0 ++ seenE) ++ restE =
                  Q0 ++ (seenE ++ restE) := List.append_assoc _ _ _
              rw [hQeq2] at hQdA
              have hCapp := ihOuter (sizeOf V') hltV V' Q0
                (seenE ++ restE) hNRV' hWFV' (Nat.le_refl _) hC0
              have hND : (SessionType.externalChoice p
                  branches).NoDupl := hWF0.1
              exact cannot_prepend_dequeue_at_extC hND hmemV' hQdA hCapp
            · -- Absent key: every dequeue blocks at the oldest; stuck.
              push Not at hKey
              have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
                  ¬ over_trans (SessionType.externalChoice p branches,
                    Q0 ++ extra) α stq' := by
                intro α stq' hS
                cases hS with
                | @dequeue _ _ _ _ _ lab S _ hEq hmem hQd =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  obtain ⟨seen', left', hQeq', hseen'⟩ :=
                    dequeue_oldest_of_some hQd
                  have hOld' : oldest_from p (Q0 ++ extra)
                      (QueueMessage.msg p lab S) :=
                    ⟨seen', left', hQeq', rfl, hseen'⟩
                  have hEqK := oldest_from_unique hOld' hOldA
                  rw [QueueMessage.msg.injEq] at hEqK
                  obtain ⟨-, rfl, rfl⟩ := hEqK
                  exact (hKey _ hmem).elim
                | specInp hEq hmem hAbss =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  have hmemM0 : QueueMessage.msg p lab0 S0 ∈ Q0 ++ extra := by
                    have hmemE : QueueMessage.msg p lab0 S0 ∈ extra := by
                      rw [hQeqE]
                      simp
                    exact List.mem_append.mpr (Or.inr hmemE)
                  exact (hAbss _ hmemM0 rfl).elim
                | sendFresh hEqS _ _ => cases hEqS
                | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR0 hU
              have hneE : extra ≠ [] := List.ne_nil_of_mem
                (by rw [hQeqE]; simp : QueueMessage.msg p lab0 S0 ∈ extra)
              exact cannot_of_nostep_norec hNR0 hWF0 hNo
                (append_nonempty_right hneE)
          · -- Extension `p`-free: spec replays; all branches lift by outer IH.
            have hAbsA : ∀ m ∈ Q0 ++ extra, m.1 ≠ p := by
              intro m hm
              rcases List.mem_append.mp hm with h | h
              · exact hAbs _ h
              · by_contra hcon
                exact hExtraP ⟨m, h, hcon⟩
            have hTailC := ihρ T1 Q0 Tn Qn hTail hne hend hclos'
              hNR1 hWF1 hsize1
            have hAllBad : ∀ (br : Lab × DataSort × SessionType),
                br ∈ branches →
                CannotAlwaysDrainInternalDeepCore br.2.2 (Q0 ++ extra) := by
              intro br hmem
              have hCore0 := hExtC p branches rfl hneB hAbs br hmem
              have hCb0 : CannotAlwaysDrainInternalDeep br.2.2 Q0 :=
                hCore0.toDef
              have hNRb : br.2.2.NoRec :=
                noRec_of_mem_extBranches hNR0 hmem
              have hWFb : br.2.2.WellFormed :=
                wf_of_mem_extBranches hmem hWF0
              have hltb : sizeOf br.2.2 < n :=
                lt_of_lt_of_le
                  (sizeOf_SessionType_lt_sizeOf_externalChoice hmem)
                  hsize0
              have hCbapp := ihOuter (sizeOf br.2.2) hltb br.2.2 Q0 extra
                hNRb hWFb (Nat.le_refl _) hCb0
              exact hCbapp.toCore
            have hND : (SessionType.externalChoice p branches).NoDupl :=
              hWF0.1
            exact cannot_prepend_spec_at_extC hND hmem hAbsA hTailC hAllBad
        | @sendFresh _ _ _ q lab S branches hEq hST hFresh =>
          subst hEq
          have hmemSend : (q, lab, S, T1) ∈ branches := by
            cases hST with
            | intC h => exact h
          have hStep1 : over_trans (SessionType.internalChoice branches, Q0)
              (st_label.out q lab S) (T1, Q0) :=
            over_trans.sendFresh rfl hST hFresh
          have h1 : over_trans_trace (SessionType.internalChoice branches, Q0)
              [st_label.out q lab S] (T1, Q0) :=
            over_trans_trace.step hStep1 (over_trans_trace.refl _)
          have hNR1 : T1.NoRec := over_trans_preserves_norec hStep1 hNR0
          have hWF1 : T1.WellFormed := over_trans_preserves_wf hStep1 hWF0
          have hsize1 : sizeOf T1 ≤ n :=
            le_trans (le_of_lt (over_trans_session_shrink_norec hStep1 hNR0)) hsize0
          have hclos' : ∀ (Ti : SessionType) (Qi : Queue)
              (σ1 σ2 : List st_label),
              over_trans_trace (T1, Q0) σ1 (Ti, Qi) →
              over_trans_trace (Ti, Qi) σ2 (Tn, Qn) →
              ρ' = σ1 ++ σ2 →
              ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
                Ti = SessionType.internalChoice branches → branches ≠ [] →
                int_choice_fireable Ti Qi branches →
                ∃ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches ∧
                  CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
              (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
                Ti = SessionType.externalChoice p branches → branches ≠ [] →
                (∀ m ∈ Qi, m.1 ≠ p) →
                ∀ (br : Lab × DataSort × SessionType),
                  br ∈ branches →
                  CannotAlwaysDrainInternalDeepCore br.2.2 Qi)) := by
            intro Ti Qi σ1 σ2 g1 g2 geq2
            exact hclos Ti Qi ([st_label.out q lab S] ++ σ1) σ2
              (over_trans_trace_append h1 g1) g2
              (by simp [geq2, List.cons_append])
          have hTailC := ihρ T1 Q0 Tn Qn hTail hne hend hclos'
            hNR1 hWF1 hsize1
          by_cases hClean : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
              (U : SessionType),
              (r', l', s', U) ∈ branches → ∀ m ∈ extra, m.1 ≠ r'
          · -- Freshness persists: send replays; target lifts by inner IH.
            have hFreshA : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
                (U : SessionType),
                (r', l', s', U) ∈ branches →
                ∀ m ∈ Q0 ++ extra, m.1 ≠ r' := by
              intro r' l' s' U' hmem m hm
              rcases List.mem_append.mp hm with h | h
              · exact hFresh _ _ _ _ hmem _ h
              · exact hClean _ _ _ _ hmem _ h
            have hND : (SessionType.internalChoice branches).NoDupl :=
              hWF0.1
            exact cannot_prepend_send_at_intC hND hmemSend hFreshA hTailC
              hTailC.toCore
          · -- Junk in extension: sends die globally; stuck.
            push Not at hClean
            obtain ⟨r', l', s', U', hmemB, m0, hmemQ, hm1⟩ := hClean
            have hmemQ' : m0 ∈ Q0 ++ extra :=
              List.mem_append.mpr (Or.inr hmemQ)
            have hneE : extra ≠ [] := List.ne_nil_of_mem hmemQ
            have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
                ¬ over_trans (SessionType.internalChoice branches, Q0 ++ extra)
                  α stq' := by
              intro α stq' hS
              cases hS with
              | dequeue hST' _ => cases hST'
              | specInp hST' _ => cases hST'
              | sendFresh _hEq _hST hFresh' =>
                cases _hEq with
                | refl =>
                  exact absurd hm1 (hFresh' _ _ _ _ hmemB _ hmemQ')
              | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR0 hU
            exact cannot_of_nostep_norec hNR0 hWF0 hNo
              (append_nonempty_right hneE)
        | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR0 hU)
    obtain ⟨Tn, Qn, ρ, hTr, hne, hend, hclos⟩ := hC
    exact replay ρ T Q Tn Qn hTr hne hend hclos hNR hWF hsize
end AppendPersist
section SpecOnlyTransport

/-- Transport from a spec-only `extC` head: along any star the entry
    stays `(extC p, Qcur ++ E)` with `Cannot` — receives keep
    append-form (`Qcur ++ (E ++ [msg])`) with `Cannot` via
    `cannot_append_persist_norec`, others' steps leave `r` untouched,
    `r`-sends are impossible (`st_trans` analysis) — until the first
    `r`-move, which must be a `p`-dequeue to a branch target that is
    bad by the static pre-arrival closure, lifted via append-persist
    and closed by the outer size induction. Conclusion is
    disjunctive: still-`extC` with `Cannot`, or `False`. -/
theorem specOnly_transport_norec {n : Nat} {N1 : Network} {r p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Qcur : Queue}
    (hIH : ∀ (m : Nat), m < n → ∀ (N0 : Network) (r : Role)
      (T : SessionType) (Q : Queue),
      N0.NoRec → N0.WellFormed → IsOutputLiveNetwork N0 → IsHalfDuplex N0 →
      N0.NoSelf → N0.RolesPresent → sizeOf T ≤ m → (r, (T, Q)) ∈ N0 →
      CannotAlwaysDrainInternalDeep T Q → False)
    (hLive1 : IsOutputLiveNetwork N1) (hHD1 : IsHalfDuplex N1)
    (hNR1 : N1.NoRec) (hWF1 : N1.WellFormed)
    (habs0 : ∀ m ∈ Qcur, m.1 ≠ p)
    (hBad0 : ∀ br ∈ branches,
      CannotAlwaysDrainInternalDeepCore br.2.2 Qcur)
    (hsizeH : sizeOf (SessionType.externalChoice p branches) ≤ n) :
    ∀ (N' N'' : Network) (E : Queue),
    N'.NoRec → N'.WellFormed → N'.NoSelf → N'.RolesPresent →
    net_trans_star N1 N' → net_trans_star N' N'' →
    (r, (SessionType.externalChoice p branches, Qcur ++ E)) ∈ N' →
    CannotAlwaysDrainInternalDeep (SessionType.externalChoice p branches)
      (Qcur ++ E) →
    (∃ E', (r, (SessionType.externalChoice p branches, Qcur ++ E')) ∈ N'' ∧
      CannotAlwaysDrainInternalDeep (SessionType.externalChoice p branches)
        (Qcur ++ E')) ∨ False := by
  intro N' N'' E hNR' hWF' hNS' hRP' hStarAcc hStar2 hmem hC
  revert E hmem hC hStarAcc hRP' hNS' hWF' hNR'
  induction hStar2 with
  | refl =>
    intro E hNR' hWF' hNS' hRP' hStarAcc hmem hC
    exact Or.inl ⟨E, hmem, hC⟩
  | @step M1 M2 M3 _ hInt hTr hStar' ih =>
    intro E hNR' hWF' hNS' hRP' hStarAcc hmem hC
    have hNR2 := net_trans_preserves_norec hTr hNR'
    have hWF2 := Network.wellFormedPreserved _ _ _ hWF' hTr hInt
    have hNS2 := net_trans_preserves_no_self hTr hNS'
    have hRP2 := net_trans_preserves_roles_present hTr hRP'
    have hStarAcc2 := net_trans_star.trans hStarAcc
      (net_trans_star.step hInt hTr (net_trans_star.refl _))
    have hTrC := hTr
    have hTWF' : (SessionType.externalChoice p branches).WellFormed :=
      hWF'.2.1 _ hmem
    have hTNR' : (SessionType.externalChoice p branches).NoRec :=
      hNR' _ hmem
    cases hTr with
    | io_send _ _ => simp [is_internal_net_label] at hInt
    | io_recv _ _ => simp [is_internal_net_label] at hInt
    | @dequeue r0 p0 stq0 stq0' lab0 S0 hSQ hmem_d =>
      by_cases heq : r0 = r
      · subst r0
        -- First move: `r`'s own dequeue. Pin the entry and the branch.
        have hstq : stq0 = (SessionType.externalChoice p branches,
            Qcur ++ E) := network_mem_unique hWF' hmem_d hmem
        subst hstq
        cases hSQ with
        | @dequeue _ T1 _ Qmid _ _ _ hST hQd =>
          cases hST with
          | extC hmemU =>
            -- `hmemU : (lab0, S0, T1) ∈ branches` (owner pinned to `p`).
            -- The removed key-message is not in `Qcur` (static absence).
            have hmemKey : QueueMessage.msg p lab0 S0 ∈ Qcur ++ E := by
              obtain ⟨seenW, leftW, hQeqW, -, -⟩ :=
                queue_dequeue_some_iff hQd
              rw [hQeqW]
              simp
            have hnotQcur : QueueMessage.msg p lab0 S0 ∉ Qcur := by
              intro hcon
              exact (habs0 _ hcon) rfl
            have hmemE : QueueMessage.msg p lab0 S0 ∈ E := by
              rcases List.mem_append.mp hmemKey with h | h
              · exact absurd h hnotQcur
              · exact h
            -- Oldest-`p` of `E` is the removed message (uniqueness).
            obtain ⟨m0, hOldE, hm1E0⟩ := oldest_of_mem E p
              ⟨QueueMessage.msg p lab0 S0, hmemE, rfl⟩
            obtain ⟨seenE, restE, hQeqE, hm1Eb, hseenE⟩ := hOldE
            obtain ⟨seenD, leftD, hQeqD, hseenD⟩ :=
              dequeue_oldest_of_some hQd
            have hOldD : oldest_from p (Qcur ++ E)
                (QueueMessage.msg p lab0 S0) :=
              ⟨seenD, leftD, hQeqD, rfl, hseenD⟩
            have hOldA : oldest_from p (Qcur ++ E) m0 := by
              refine ⟨Qcur ++ seenE, restE, ?_, hm1E0, ?_⟩
              · rw [hQeqE]
                simp [List.append_assoc]
              · intro x hx
                rcases List.mem_append.mp hx with h | h
                · exact habs0 _ h
                · exact hseenE _ h
            have hEqM : QueueMessage.msg p lab0 S0 = m0 :=
              oldest_from_unique hOldD hOldA
            rw [← hEqM] at hQeqE
            -- Dequeue result in append-form.
            have hseenA : ∀ m ∈ Qcur ++ seenE, m.1 ≠ p := by
              intro x hx
              rcases List.mem_append.mp hx with h | h
              · exact habs0 _ h
              · exact hseenE _ h
            have hQeqA : Qcur ++ E =
                (Qcur ++ seenE) ++ QueueMessage.msg p lab0 S0 :: restE := by
              simp [hQeqE, List.append_assoc]
            have hQdA : (Qcur ++ E).dequeue (QueueMessage.msg p lab0 S0) =
                some ((Qcur ++ seenE) ++ restE) := by
              rw [hQeqA]
              simp only [Queue.dequeue]
              exact dequeue_skip_seen hseenA
            -- Pin the network result by determinism.
            have hQmid : Qmid = (Qcur ++ seenE) ++ restE :=
              (Option.some_inj.mp (hQdA.symm.trans hQd)).symm
            -- Target bad: static closure (`Qcur`) lifted via append-persist.
            have hCoreU : CannotAlwaysDrainInternalDeepCore T1 Qcur :=
              hBad0 _ hmemU
            have hCU : CannotAlwaysDrainInternalDeep T1 Qcur :=
              hCoreU.toDef
            have hNRT1 : T1.NoRec :=
              noRec_of_mem_extBranches (hNR' _ hmem) hmemU
            have hWFT1 : T1.WellFormed :=
              wf_of_mem_extBranches hmemU (hWF'.2.1 _ hmem)
            have hltU : sizeOf T1 < n :=
              lt_of_lt_of_le
                (sizeOf_SessionType_lt_sizeOf_externalChoice hmemU) hsizeH
            have hQmidA : Qmid = Qcur ++ (seenE ++ restE) := by
              rw [hQmid, List.append_assoc]
            have hCapp : CannotAlwaysDrainInternalDeep T1
                (Qcur ++ (seenE ++ restE)) :=
              cannot_append_persist_norec (sizeOf T1) T1 Qcur (seenE ++ restE)
                hNRT1 hWFT1 (Nat.le_refl _) hCU
            have hLiveMid : IsOutputLiveNetwork _ :=
              IsOutputLiveNetwork_stable_of_NoRec hLive1
                (net_trans_star.trans hStarAcc
                  (net_trans_star.step hInt hTrC (net_trans_star.refl _))) hNR1 hWF1
            have hHDMid : IsHalfDuplex _ := hHD1.star
              (net_trans_star.trans hStarAcc
                (net_trans_star.step hInt hTrC (net_trans_star.refl _)))
            have hCappQ : CannotAlwaysDrainInternalDeep T1 Qmid :=
              hQmidA.symm ▸ hCapp
            have hmemMid : (r, (T1, Qmid)) ∈
                Network.replace M1 r (T1, Qmid) := by
              unfold Network.replace
              simp
            exact Or.inr (hIH (sizeOf T1) hltU _ r T1 _
              hNR2 hWF2 hLiveMid hHDMid hNS2 hRP2 (Nat.le_refl _) hmemMid
              hCappQ)
      · exact ih E hNR2 hWF2 hNS2 hRP2 hStarAcc2
          (mem_replace_other hmem (Ne.symm heq)) hC
    | @comm p1 q1 lab1 S1 stqp stqp' stqq stqq' hne h_send h_recv hmem_p
        hmem_q =>
      by_cases heqp : r = p1
      · by_cases heqq : r = q1
        · have hpq : p1 = q1 := heqp.symm.trans heqq
          exact absurd hpq hne
        · -- `r` sends: impossible at `extC`.
          have hContra : False := by
            have hmemP := heqp ▸ hmem
            have hstq : stqp = (SessionType.externalChoice p branches,
                Qcur ++ E) := network_mem_unique hWF' hmem_p hmemP
            subst hstq
            cases h_send with
            | send hST => cases hST
          exact Or.inr hContra
      · by_cases heqq : r = q1
        · -- `r` receives: append-form + append-persist.
          have hmemQ := heqq ▸ hmem
          have hstq : stqq = (SessionType.externalChoice p branches,
              Qcur ++ E) := network_mem_unique hWF' hmem_q hmemQ
          subst hstq
          cases h_recv with
          | recv =>
            have hEeq : (Qcur ++ E) ++ [QueueMessage.msg p1 lab1 S1] =
                Qcur ++ (E ++ [QueueMessage.msg p1 lab1 S1]) :=
              List.append_assoc _ _ _
            have hC' : CannotAlwaysDrainInternalDeep
                (SessionType.externalChoice p branches)
                (Qcur ++ (E ++ [QueueMessage.msg p1 lab1 S1])) := by
              have hCa := cannot_append_persist_norec
                (sizeOf (SessionType.externalChoice p branches)) _ _
                [QueueMessage.msg p1 lab1 S1] hTNR' hTWF'
                (Nat.le_refl _) hC
              rw [hEeq] at hCa
              exact hCa
            have hmem2 : (r, (SessionType.externalChoice p branches,
                Qcur ++ (E ++ [QueueMessage.msg p1 lab1 S1]))) ∈
                ((M1.replace p1 stqp').replace q1
                  (SessionType.externalChoice p branches,
                    (Qcur ++ E) ++ [QueueMessage.msg p1 lab1 S1])) := by
              rw [← hEeq, ← heqq]
              exact List.mem_cons.mpr (Or.inl rfl)
            exact ih _ hNR2 hWF2 hNS2 hRP2 hStarAcc2 hmem2 hC'
        · -- `r` uninvolved: entry untouched.
          exact ih _ hNR2 hWF2 hNS2 hRP2 hStarAcc2
            (mem_replace_other (mem_replace_other hmem heqp) heqq) hC
end SpecOnlyTransport
section SteerInt

/-- Steer along adversarial `intC` choices: from `Cannot` failure,
    repeatedly fire the per-site chosen branch (`τ_comm`,
    queue-preserving) until no nonempty `intC` remains — or stop stuck
    at a blocked `intC` (some branch role has messages, so no step
    fires). Terminates by `sizeOf` on branch targets; needs no drain
    reasoning. -/
theorem steer_cannotDeep_int_norec (n : Nat) (N N0 : Network) (r : Role)
    (T : SessionType) (Q : Queue)
    (hNR : N.NoRec) (hWF : N.WellFormed) (hNS : N.NoSelf)
    (hRP : Network.RolesPresent N)
    (hsize : sizeOf T ≤ n)
    (hStar : net_trans_star N0 N) (hmem : (r, (T, Q)) ∈ N)
    (hbad : CannotAlwaysDrainInternalDeep T Q) :
    ∃ N' T', net_trans_star N0 N' ∧ N'.NoRec ∧ N'.WellFormed ∧ N'.NoSelf ∧
      Network.RolesPresent N' ∧ (r, (T', Q)) ∈ N' ∧ sizeOf T' ≤ sizeOf T ∧
      (((∀ branches : List (Role × Lab × DataSort × SessionType),
        T' = SessionType.internalChoice branches → branches = []) ∧
      CannotAlwaysDrainInternalDeep T' Q) ∨
      ((∀ (α : st_label) (stq' : SessionTypeWithQueue),
        ¬ over_trans (T', Q) α stq') ∧ Q ≠ [] ∧
      CannotAlwaysDrainInternalDeep T' Q)) := by
  revert hbad hmem hStar hsize hRP hNS hWF hNR Q T r N0 N
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N N0 r T Q hNR hWF hNS hRP hsize hStar hmem hbad
    by_cases hC : ∃ branches : List (Role × Lab × DataSort × SessionType),
      T = SessionType.internalChoice branches ∧ branches ≠ []
    · obtain ⟨branches, hEq, hneB⟩ := hC
      rcases Classical.em (int_choice_fireable T Q branches) with hfire | hfire
      · obtain ⟨Tn, Qn, ρ, hTr, _, _, hall⟩ := hbad
        obtain ⟨hIntCl, -⟩ :=
          hall T Q [] ρ (over_trans_trace.refl _) hTr (by simp)
        obtain ⟨br, hmemB, hCore⟩ := hIntCl branches hEq hneB hfire
        obtain ⟨s, lab, S, T0⟩ := br
        have hT0 : (s, lab, S, T0).2.2.2 = T0 := rfl
        rw [hT0] at hCore
        have hCoreD := CannotAlwaysDrainInternalDeepCore.toDef hCore
        have hOcc : T.Occurs s := by
          rw [hEq]
          exact SessionType.Occurs.intSender hmemB rfl
        have hne : s ≠ r := by
          intro heq
          subst heq
          exact hNS _ _ _ hmem hOcc
        obtain ⟨stqs, hmemS⟩ := hRP _ _ _ _ hmem hOcc
        obtain ⟨N1, hStep, hmemR1, _⟩ :=
          intC_fire_as_tau_comm hmem hEq hmemB hne hmemS
        have hStar1 : net_trans_star N0 N1 :=
          net_trans_star.trans hStar
            (net_trans_star.step (δ := net_label.τ_comm r s lab S) (by trivial) hStep
              (net_trans_star.refl _))
        have hlt : sizeOf T0 < n := by
          have hlt' := sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
          rw [← hEq] at hlt'
          omega
        obtain ⟨N', T', hStar', hNR', hWF', hNS', hRP', hmem', hsize',
            hRes⟩ :=
          ih _ hlt N1 N0 r T0 Q (net_trans_preserves_norec hStep hNR)
            (Network.wellFormedPreserved _ _ _ hWF hStep (by trivial))
            (net_trans_preserves_no_self hStep hNS)
            (net_trans_preserves_roles_present hStep hRP) (Nat.le_refl _)
            hStar1 hmemR1 hCoreD
        have hltT : sizeOf T0 < sizeOf T := by
          have hlt' := sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
          rw [← hEq] at hlt'
          exact hlt'
        exact ⟨N', T', hStar', hNR', hWF', hNS', hRP', hmem',
          le_trans hsize' (le_of_lt hltT), hRes⟩
      · have hNB : ¬ int_choice_fireable T Q branches := hfire
        unfold int_choice_fireable at hfire
        push_neg at hfire
        obtain ⟨br, hmemB, m, hmemM, heqM⟩ := hfire
        obtain ⟨r, lab, S, T0⟩ := br
        have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
            ¬ over_trans (T, Q) α stq' := by
          intro α stq' hS
          cases hS with
          | dequeue hEqD hmem hQ =>
            subst hEq
            cases hEqD
          | specInp hEqD hmem hAbs =>
            subst hEq
            cases hEqD
          | sendFresh hEqS hST hFresh =>
            subst hEq
            cases hEqS
            exact (hFresh _ _ _ _ hmemB _ hmemM) heqM
          | tauUnfold hU =>
            cases hU with
            | tRec => cases hEq
        have hQne : Q ≠ [] := List.ne_nil_of_mem hmemM
        have hEnd : (T = SessionType.tEnd ∨
            (∃ (branches : List (Role × Lab × DataSort × SessionType))
              (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
              (m : QueueMessage),
              T = SessionType.internalChoice branches ∧
              (p, lab, S, T') ∈ branches ∧ m ∈ Q ∧ m.1 = p) ∨
            ((∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
              (lab : Lab) (S : DataSort) (m : QueueMessage),
              T = SessionType.externalChoice p branches ∧ oldest_from p Q m ∧
              m = QueueMessage.msg p lab S ∧
              ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
            (∃ (X : String) (B U : SessionType),
              T = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
              (U = SessionType.tEnd ∨
                (∃ (branches : List (Role × Lab × DataSort × SessionType))
                  (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
                  (m : QueueMessage),
                  U = SessionType.internalChoice branches ∧
                  (p, lab, S, T') ∈ branches ∧ m ∈ Q ∧ m.1 = p) ∨
                (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
                  (lab : Lab) (S : DataSort) (m : QueueMessage),
                  U = SessionType.externalChoice p branches ∧ oldest_from p Q m ∧
                  m = QueueMessage.msg p lab S ∧
                  ∀ (T' : SessionType), (lab, S, T') ∉ branches))))) :=
          Or.inr (Or.inl ⟨branches, r, lab, S, T0, m, hEq, hmemB, hmemM, heqM⟩)
        have hClos : ∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
            over_trans_trace (T, Q) ρ1 (Ti, Qi) →
            over_trans_trace (Ti, Qi) ρ2 (T, Q) →
            [] = ρ1 ++ ρ2 →
            ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
              Ti = SessionType.internalChoice branches → branches ≠ [] →
                int_choice_fireable Ti Qi branches →
                ∃ br ∈ branches, CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
            ∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
              Ti = SessionType.externalChoice p branches →
              branches ≠ [] → (∀ m ∈ Qi, m.1 ≠ p) →
              ∀ br ∈ branches, CannotAlwaysDrainInternalDeepCore br.2.2 Qi) := by
          intro Ti Qi ρ1 ρ2 h1 h2 heq2
          cases ρ1 with
          | nil =>
            have hST := overTrTrace_nil_eq h1
            cases hST
            refine ⟨?_, ?_⟩
            · intro branches2 hEq2 hneB2 hfire2
              have hBeq2 : branches2 = branches := by
                rw [hEq] at hEq2
                cases hEq2
                rfl
              rw [hBeq2] at hfire2
              exact absurd hfire2 hNB
            · intro p branches2 hEq2 _ _
              have hCon : SessionType.internalChoice branches =
                  SessionType.externalChoice p branches2 := by
                rw [hEq] at hEq2
                cases hEq2
              cases hCon
          | cons α ρ1' =>
            cases h1 with
            | step hS _ => exact (hNo _ _ hS).elim
        have hCannot : CannotAlwaysDrainInternalDeep T Q :=
          ⟨T, Q, [], over_trans_trace.refl _, hQne, hEnd, hClos⟩
        exact ⟨N, T, hStar, hNR, hWF, hNS, hRP, hmem, Nat.le_refl _,
          Or.inr ⟨hNo, hQne, hCannot⟩⟩
    · push_neg at hC
      exact ⟨N, T, hStar, hNR, hWF, hNS, hRP, hmem, Nat.le_refl _,
        Or.inl ⟨hC, hbad⟩⟩
end SteerInt
section LoopLive

/-- A role whose session admits no `st_trans` steps can never drain a nonempty
    queue, yet in a live terminating network every maximal path ends empty:
    contradiction. Concretely: such an entry keeps its session forever, its
    queue only grows (head fixed, always dequeueable), so every reachable
    stuck configuration carries an orphan. Covers `tEnd`, `intC []`,
    `tVar` (callers discharge `hST` by `cases`) — the liveness route of the
    universal-drain program. -/
theorem nost_trans_live_false_norec {r : Role} {T : SessionType} {Q : Queue} {N : Network}
    (hST : ∀ (α : st_label) (T' : SessionType), ¬ st_trans T α T')
    (hQ : Q ≠ [])
    (hmemN : (r, (T, Q)) ∈ N)
    (hLive : IsOutputLiveNetwork N)
    (hNR : N.NoRec) (hWF : N.WellFormed) :
    False := by
  obtain ⟨N', hStar, hStuck⟩ := exists_stuck_reachable_of_NoRec hNR hWF
  have hmono : ∀ (M M' : Network), net_trans_star M M' → M.WellFormed →
      ∀ (Qcur : Queue), (r, (T, Qcur)) ∈ M → (∀ m ∈ Q, m ∈ Qcur) →
      ∃ Q'', (r, (T, Q'')) ∈ M' ∧ ∀ m ∈ Q, m ∈ Q'' := by
    intro M M' hS
    induction hS with
    | refl => intro hWFM Qcur hmem hsub; exact ⟨Qcur, hmem, hsub⟩
    | @step N1 N2 N3 δ hInt hTr hStar' ih =>
      intro hWFM Qcur hmem hsub
      obtain ⟨Q1, hmem1, hsub1⟩ :=
        nost_trans_entry_step hST hTr hInt hWFM hmem hsub
      have hWF2 := Network.wellFormedPreserved N1 δ N2 hWFM hTr hInt
      obtain ⟨Q'', hmem'', hsub''⟩ := ih hWF2 Q1 hmem1 hsub1
      exact ⟨Q'', hmem'', hsub''⟩
  obtain ⟨Q', hmem', hsub'⟩ := hmono N N' hStar hWF Q hmemN (fun _ h => h)
  have hQne : Q' ≠ [] := by
    obtain ⟨hd, tl, hQeq⟩ := List.exists_cons_of_ne_nil hQ
    have hmemQ : hd ∈ Q' := hsub' _ (hQeq ▸ List.mem_cons.mpr (Or.inl rfl))
    exact List.ne_nil_of_mem hmemQ
  obtain ⟨hd', tl', hQ'eq⟩ := List.exists_cons_of_ne_nil hQne
  subst hQ'eq
  rcases hd' with ⟨p', lab', S'⟩
  have hscan : Queue.dequeue (QueueMessage.msg p' lab' S' :: tl')
      (QueueMessage.msg p' lab' S') = some tl' :=
    Queue.dequeue_head_hit
  exact hLive.2 N' hStar hStuck r T _ p' lab' S' tl' hmem' hscan

/-- Main loop: from a `Cannot` entry in a live+HD `NoRec` network,
    derive `False`. Queue fuel: intC-steering preserves the queue
    length, dequeue replay drops it by one; the outer size hypothesis
    (`hIH`, threaded with a `sizeOf` bound) closes first moves out of
    spec-only heads (via `specOnly_transport_norec`). -/
theorem loop_noDeep_live_hd_false_norec : ∀ (fuel n : Nat) (N0 Ncur : Network)
    (r : Role) (Tcur : SessionType) (Qcur : Queue),
    (∀ (m : Nat), m < n → ∀ (N0 : Network) (r : Role)
      (T : SessionType) (Q : Queue),
      N0.NoRec → N0.WellFormed → IsOutputLiveNetwork N0 → IsHalfDuplex N0 →
      N0.NoSelf → N0.RolesPresent → sizeOf T ≤ m → (r, (T, Q)) ∈ N0 →
      CannotAlwaysDrainInternalDeep T Q → False) →
    N0.NoRec → N0.WellFormed →
    IsOutputLiveNetwork N0 → IsHalfDuplex N0 →
    N0.NoSelf → N0.RolesPresent →
    net_trans_star N0 Ncur →
    Ncur.NoRec → Ncur.WellFormed → Ncur.NoSelf → Ncur.RolesPresent →
    (r, Tcur, Qcur) ∈ Ncur →
    CannotAlwaysDrainInternalDeep Tcur Qcur →
    sizeOf Tcur ≤ n → Qcur.length ≤ fuel → False := by
  intro fuel n
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro N0 Ncur r Tcur Qcur hIH hNR0 hWF0 hLive0 hHD0 hNS0 hRP0
      hStarAcc hNRc hWFc hNSc hRPc hmem hCannot hsizeCur hfuel
    -- Steer intCs to a fixpoint (queue preserved).
    obtain ⟨N1, T1, hStar1, hNR1, hWF1, hNS1, hRP1, hmem1, hsizeT,
        hRes⟩ :=
      steer_cannotDeep_int_norec (sizeOf Tcur) Ncur N0 r Tcur Qcur hNRc hWFc
        hNSc hRPc (Nat.le_refl _) hStarAcc hmem hCannot
    have hsize1base : sizeOf T1 ≤ n := le_trans hsizeT hsizeCur
    have hLive1 : IsOutputLiveNetwork N1 :=
      IsOutputLiveNetwork_stable_of_NoRec hLive0 hStar1 hNR0 hWF0
    have hHD1 : IsHalfDuplex N1 := hHD0.star hStar1
    have hTWF1 : T1.WellFormed := hWF1.2.1 _ hmem1
    have hTNR1 : T1.NoRec := hNR1 _ hmem1
    rcases hRes with ⟨hFree, hC1⟩ | ⟨hNo, hQne, hC1⟩
    · -- intC-free head: case on the session.
      cases T1 with
      | tEnd =>
        exact ((tEnd_nonempty_not_live_norec hNR0 hWF0 hStar1 hmem1
          (cannot_head_nonempty hC1)) hLive0)
      | internalChoice branches =>
        have hNil : branches = [] := hFree _ rfl
        subst hNil
        exact (nost_trans_live_false_norec nost_trans_int_c_nil
          (cannot_head_nonempty hC1) hmem1 hLive1 hNR1 hWF1)
      | externalChoice p branches =>
        cases branches with
        | nil =>
          exact (nost_trans_live_false_norec (nost_trans_ext_c_nil p)
            (cannot_head_nonempty hC1) hmem1 hLive1 hNR1 hWF1)
        | cons br bs =>
          have hmemB : br ∈ br :: bs := List.mem_cons.mpr (Or.inl rfl)
          by_cases habs : ∀ m ∈ Qcur, m.1 ≠ p
          · -- Spec-only head: transport to stuck-or-first-move.
            -- Static branch badness from the head closure (absence holds).
            -- NB: `obtain` consumes `hC1`, so bank these first.
            have hQne0 : Qcur ≠ [] := cannot_head_nonempty hC1
            have hC0 : CannotAlwaysDrainInternalDeep
                (SessionType.externalChoice p (br :: bs))
                (Qcur ++ []) := by
              simpa using hC1
            obtain ⟨Tn0, Qn0, ρ0, hTr0, hne0, hend0, hclos0⟩ := hC1
            have hHeadClos := hclos0 (SessionType.externalChoice p (br :: bs))
              Qcur [] _ (over_trans_trace.refl _) hTr0 rfl
            obtain ⟨-, hExtC⟩ := hHeadClos
            have hAllBad0 : ∀ b ∈ (br :: bs),
                CannotAlwaysDrainInternalDeepCore b.2.2 Qcur := by
              intro b hm
              exact hExtC p (br :: bs) rfl (by simp) habs b hm
            have hsizeH : sizeOf (SessionType.externalChoice p
                (br :: bs)) ≤ n :=
              hsize1base
            obtain ⟨Nstuck, hStarStuck, hStuck⟩ :=
              exists_stuck_reachable_of_NoRec hNR1 hWF1
            have hmemE0 : (r, (SessionType.externalChoice p (br :: bs),
                Qcur ++ [])) ∈ N1 := by
              simpa using hmem1
            rcases specOnly_transport_norec hIH hLive1 hHD1 hNR1 hWF1 habs
                hAllBad0 hsizeH N1 Nstuck [] hNR1 hWF1 hNS1 hRP1
                (net_trans_star.refl _) hStarStuck hmemE0 hC0 with
              hStill | hF
            · obtain ⟨E', hmem'', hC''⟩ := hStill
              have hne'' : Qcur ++ E' ≠ [] :=
                append_nonempty_left hQne0
              have hLiveS : IsOutputLiveNetwork Nstuck :=
                IsOutputLiveNetwork_stable_of_NoRec hLive1 hStarStuck
                  hNR1 hWF1
              have hNo := hLiveS.2 Nstuck (net_trans_star.refl _) hStuck
              exact noOrphanMessages_nonempty_false hNo hmem'' hne''
            · exact hF
          · push Not at habs
            obtain ⟨m, hmemQ, hm1⟩ := habs
            by_cases hStep : ∃ (α : st_label) (stq' : SessionTypeWithQueue),
                over_trans (SessionType.externalChoice p (br :: bs), Qcur)
                  α stq'
            · -- A step exists (hence a dequeue): replay the witness's
              -- forced first step (no coincide needed).
              obtain ⟨Tn, Qn, ρ, hTr, hne, hend, hclos⟩ := hC1
              cases ρ with
              | nil =>
                have heq := overTrTrace_nil_eq hTr
                -- Head equals the stuck end; rule out each end shape.
                rcases hend with hT | hI | hA | hR
                · -- `tEnd` end vs `extC` head: clash.
                  have hCon : SessionType.tEnd =
                      SessionType.externalChoice p (br :: bs) :=
                    hT.symm.trans (congrArg Prod.fst heq)
                  cases hCon
                · obtain ⟨branches', p', lab', S', T'', msg,
                    hTnEq, hmemB', hmemM, hsender⟩ := hI
                  have hCon : SessionType.internalChoice branches' =
                      SessionType.externalChoice p (br :: bs) :=
                    hTnEq.symm.trans (congrArg Prod.fst heq)
                  cases hCon
                · obtain ⟨p', branches', lab0, S0, m0,
                    hTnEq, hOld, hmeq, habsK⟩ := hA
                  -- Same-constructor equation: unify owner/branches.
                  have heqFst : Tn = SessionType.externalChoice p
                      (br :: bs) :=
                    congrArg Prod.fst heq
                  have hCon : SessionType.externalChoice p' branches' =
                      SessionType.externalChoice p (br :: bs) :=
                    hTnEq.symm.trans heqFst
                  cases hCon with
                  | refl =>
                    -- Absent-key oldest vs our available dequeue: corner.
                    obtain ⟨α0, stq0, hS0⟩ := hStep
                    obtain ⟨T2, Q2, lab, S, rfl, rfl, hST, hQd⟩ :=
                      extC_step_is_dequeue hmemQ hm1 hS0
                    obtain ⟨seen, left, hQeq, hseen⟩ :=
                      dequeue_oldest_of_some hQd
                    have hOldQ : oldest_from p Qcur
                        (QueueMessage.msg p lab S) :=
                      ⟨seen, left, hQeq, rfl, hseen⟩
                    have hQeqn : Qn = Qcur := congrArg Prod.snd heq
                    rw [hQeqn, hmeq] at hOld
                    have hEq : QueueMessage.msg p lab S =
                        QueueMessage.msg p lab0 S0 :=
                      oldest_from_unique hOldQ hOld
                    rw [QueueMessage.msg.injEq] at hEq
                    obtain ⟨-, rfl, rfl⟩ := hEq
                    cases hST with
                    | extC hmem => exact (habsK _ hmem)
                · -- `tRec` end vs `extC` head: clash.
                  obtain ⟨X, B, _, hTnEq, -, -⟩ := hR
                  have hCon : SessionType.tRec X B =
                      SessionType.externalChoice p (br :: bs) :=
                    hTnEq.symm.trans (congrArg Prod.fst heq)
                  cases hCon
              | cons α ρ' =>
                obtain ⟨stqPre, stqPost, hPre, hStepW, hTail⟩ :=
                  over_trans_trace_suffix (pre := []) (l := α) (suf := ρ') hTr
                have hPreEq := overTrTrace_nil_eq hPre
                subst hPreEq
                obtain ⟨T3, Q3, lab2, S2, hαW, hstqW, hSTW, hQdW⟩ :=
                  extC_step_is_dequeue hmemQ hm1 hStepW
                -- Network replay of the forced dequeue.
                have hSQ : sq_trans (SessionType.externalChoice p (br :: bs),
                    Qcur) (sq_action.dequeue p lab2 S2) (T3, Q3) :=
                  sq_trans.dequeue hSTW hQdW
                have hTrN : net_trans N1 (net_label.τ_dequeue r p lab2 S2)
                    (N1.replace r (T3, Q3)) :=
                  net_trans.dequeue hSQ hmem1
                have hInt : is_internal_net_label
                    (net_label.τ_dequeue r p lab2 S2) := by trivial
                have hStar2 : net_trans_star N0 (N1.replace r (T3, Q3)) :=
                  net_trans_star.trans hStar1
                    (net_trans_star.step hInt hTrN (net_trans_star.refl _))
                have hNR2 : (N1.replace r (T3, Q3)).NoRec :=
                  net_trans_preserves_norec hTrN hNR1
                have hWF2 : (N1.replace r (T3, Q3)).WellFormed :=
                  Network.wellFormedPreserved _ _ _ hWF1 hTrN hInt
                have hNS2 : (N1.replace r (T3, Q3)).NoSelf :=
                  net_trans_preserves_no_self hTrN hNS1
                have hRP2 : (N1.replace r (T3, Q3)).RolesPresent :=
                  net_trans_preserves_roles_present hTrN hRP1
                have hmem2 : (r, T3, Q3) ∈ N1.replace r (T3, Q3) := by
                  unfold Network.replace
                  simp
                have hStepW' : over_trans (SessionType.externalChoice p
                    (br :: bs), Qcur) α (T3, Q3) := hstqW ▸ hStepW
                have h1 : over_trans_trace (SessionType.externalChoice p
                    (br :: bs), Qcur) [α] (T3, Q3) :=
                  over_trans_trace.step hStepW' (over_trans_trace.refl _)
                have hTail' : over_trans_trace (T3, Q3) ρ' (Tn, Qn) :=
                  hstqW ▸ hTail
                have hC3 : CannotAlwaysDrainInternalDeep T3 Q3 :=
                  CannotAlwaysDrainInternalDeep.suffix hne hend hclos
                    h1 hTail' rfl
                have hlen : Q3.length + 1 = Qcur.length :=
                  Queue.dequeue_length_drop hQdW
                have hlt : fuel - 1 < fuel := by omega
                have hfuel3 : Q3.length ≤ fuel - 1 := by omega
                have hsize3 : sizeOf T3 ≤ n :=
                  le_trans
                    (le_of_lt (over_trans_session_shrink_norec hStepW' (hNR1 _ hmem1)))
                    hsize1base
                exact ih (fuel - 1) hlt N0 _ r T3 Q3 hIH hNR0 hWF0
                  hLive0 hHD0 hNS0 hRP0 hStar2 hNR2 hWF2 hNS2 hRP2
                  hmem2 hC3 hsize3 hfuel3
            · -- No step at all: stuck `extC` kills liveness.
              have hNo' : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
                  ¬ over_trans (SessionType.externalChoice p (br :: bs), Qcur)
                    α stq' :=
                fun α stq' h => hStep ⟨α, stq', h⟩
              exact (overTrStuck_extC_live_false_norec rfl hNo' hmemB hmem1
                hLive1 hNR1 hWF1)
      | tVar X =>
        have hCl : SessionType.IsClosed (SessionType.tVar X) := hTWF1.2.1
        simp [SessionType.IsClosed, SessionType.fv] at hCl
      | tRec X B =>
        cases hTNR1
    · -- Stuck head (blocked `intC` from steering): case on the session.
      cases T1 with
      | tEnd =>
        exact ((tEnd_nonempty_not_live_norec hNR0 hWF0 hStar1 hmem1 hQne)
          hLive0)
      | internalChoice branches =>
        cases branches with
        | nil =>
          exact (nost_trans_live_false_norec nost_trans_int_c_nil hQne hmem1 hLive1
            hNR1 hWF1)
        | cons br bs =>
          have hmemB : br ∈ br :: bs := List.mem_cons.mpr (Or.inl rfl)
          exact ((overTrStuck_intC_hd_false rfl hNo hmemB hmem1
            hNS1 hRP1) hHD1)
      | externalChoice p branches =>
        cases branches with
        | nil =>
          exact (nost_trans_live_false_norec (nost_trans_ext_c_nil p) hQne hmem1 hLive1
            hNR1 hWF1)
        | cons br bs =>
          have hmemB : br ∈ br :: bs := List.mem_cons.mpr (Or.inl rfl)
          exact (overTrStuck_extC_live_false_norec rfl hNo hmemB hmem1 hLive1
            hNR1 hWF1)
      | tVar X =>
        have hCl : SessionType.IsClosed (SessionType.tVar X) := hTWF1.2.1
        simp [SessionType.IsClosed, SessionType.fv] at hCl
      | tRec X B =>
        cases hTNR1

/-- Outer size induction for no-deep-drain: a `Cannot`
    entry in a live+HD `NoRec` network is impossible. The queue-fuel
    loop handles intC-steering and forced dequeues; first moves out
    of spec-only heads go to smaller sessions (outer IH via the
    loop's hypothesis). -/
theorem noDeep_false_size_norec : ∀ (n : Nat) (N0 : Network) (r : Role)
    (T : SessionType) (Q : Queue),
    N0.NoRec → N0.WellFormed → IsOutputLiveNetwork N0 → IsHalfDuplex N0 →
    N0.NoSelf → N0.RolesPresent → sizeOf T ≤ n → (r, (T, Q)) ∈ N0 →
    CannotAlwaysDrainInternalDeep T Q → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihOuter =>
    intro N0 r T Q hNR hWF hLive hHD hNS hRP hsize hmem hC
    exact loop_noDeep_live_hd_false_norec Q.length n N0 N0 r T Q ihOuter hNR
      hWF hLive hHD hNS hRP (net_trans_star.refl _) hNR hWF hNS hRP hmem hC
      hsize (Nat.le_refl _)
end LoopLive
section NoDeepLive

/-- A `¬Deep` entry in a `NoRec` well-formed network with
    no self-sends and full role presence forces `¬Live` or `¬HD`.
    Via `deep_iff_not_cannot_norec` (needs `T.NoRec`/`T.WellFormed` from
    network membership) plus `noDeep_false_size_norec`. -/
theorem no_deep_drain_no_output_liveness_hd_norec {N : Network} {r : Role}
    {T : SessionType} {Q : Queue}
    (hNR : N.NoRec) (hWF : N.WellFormed) (hHD : IsHalfDuplex N)
    (hNS : N.NoSelf) (hRP : N.RolesPresent)
    (hmem : (r, T, Q) ∈ N)
    (hnd : ¬ CanAlwaysDrainInternalDeep T Q) :
    ¬ IsOutputLiveNetwork N ∨ ¬ IsHalfDuplex N := by
  by_cases hLive : IsOutputLiveNetwork N
  · by_cases hHD' : IsHalfDuplex N
    · exfalso
      have hTNR : T.NoRec := hNR _ hmem
      have hTWF : T.WellFormed := hWF.2.1 _ hmem
      have hCannot : CannotAlwaysDrainInternalDeep T Q := by
        by_cases hC : CannotAlwaysDrainInternalDeep T Q
        · exact hC
        · exact absurd ((deep_iff_not_cannot_norec hTNR hTWF).mpr hC) hnd
      exact noDeep_false_size_norec (sizeOf T) N r T Q hNR hWF hLive hHD hNS
        hRP (Nat.le_refl _) hmem hCannot
    · exact Or.inr hHD'
  · exact Or.inl hLive
end NoDeepLive
