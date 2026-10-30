import Nest.SessionUtils
import Nest.StuckWitness
import Nest.MonitorToolkit
import Nest.NoRec.DeepComplement
import Nest.NoRec.SteerLoop
import Nest.NoRec.NoRecEncoder

/-!
# NoRec.CommCorrespondence: NoRec monitor-communication correspondence.

A communication step of a NoRec, well-formed, output-live, half-duplex network (no self-sends,
all roles present) is matched by its consistent instrumentation, and vice versa.
The dequeue directions (`type_mon_dequeuing_norec`, `mon_type_dequeuing_norec`)
transfer absorption across `τ_dequeue` steps and feed the two dequeue cases.
-/

section DequeueCorrespondence

/-- Forward dequeuing, NoRec: a network `τ_dequeue` is matched by the
    instrumented network, with consistency preserved. The step itself is
    `mon_net_trans.dequeue` (monitor unchanged); consistency of the target is the
    general transfer (`monitor_fold_absorb_dequeue_transfer_norec`) fed by the
    scan shape (`queue_dequeue_some_iff`, which supplies freshness). -/
lemma type_mon_dequeuing_norec {N N' : Network} {MN : MonitoredNetwork}
    {r p : Role} {lab : Lab} {S : DataSort}
    (h : net_trans N (net_label.τ_dequeue r p lab S) N')
    (hNR : N.NoRec) (hwf : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN) :
    ∃ (MN' : MonitoredNetwork), consistentInstrumentation N' = some MN' ∧
      mon_net_trans MN (mon_net_label.τ_dequeue r p lab S) MN' := by
  cases h with
  | dequeue hSQ hmem =>
    cases hSQ with
    | @dequeue T T' Q Q' _ _ _ hST hQ =>
      obtain ⟨M, hM, hmemMN⟩ := mem_consistentInstrumentation hmem hCons
      have hTNR : T.NoRec := hNR _ hmem
      have hTWF : T.WellFormed := hwf.2.1 _ hmem
      have hTND : T.NoDupl := hTWF.1
      obtain ⟨seen, left, hQeq, hQ'eq, hseen⟩ := queue_dequeue_some_iff hQ
      subst hQeq
      subst hQ'eq
      have hEnc : monitor_fold (T, seen ++ [QueueMessage.msg p lab S] ++ left) M :=
        monitor_fold_val_partial_eq_of_some hM
      have hTrans : monitor_fold (T', seen ++ left) M :=
        monitor_fold_absorb_dequeue_transfer_norec hTNR hTND hTWF hseen hST hEnc
      have hTWF' : T'.WellFormed := SessionType.wellFormedPreserved T _ T' hTWF hST
      have hM' : monitor_fold_val_partial (T', seen ++ left) = some M :=
        monitor_fold_val_partial_eq_of_monitor_fold hTWF' hTrans
      have hCons' : consistentInstrumentation (Network.replace N r (T', seen ++ left)) =
          some (MN.replace r ((T', seen ++ left), M)) :=
        consistentInstrumentation_replace hCons hM'
      exact ⟨_, hCons',
        mon_net_trans.dequeue (sq_trans.dequeue hST hQ) hmemMN⟩

/-- Backward dequeuing, NoRec: a monitored `τ_dequeue` comes from a network
    `τ_dequeue` with consistent instrumentation preserved. Inverting the
    monitored step (via generalize-then-`cases`, since `ofmon_label` cannot
    unify with `τ_dequeue` directly) leaves only `mon_trans.dequeue`, which
    carries the session step; the network replays it, and consistency of the
    target is the general transfer fed by the scan shape. -/
lemma mon_type_dequeuing_norec {MN : MonitoredNetwork} {N : Network}
    {r p : Role} {lab : Lab} {S : DataSort} {MN' : MonitoredNetwork}
    (hNR : N.NoRec) (hwf : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN)
    (h : mon_net_trans MN (mon_net_label.τ_dequeue r p lab S) MN') :
    ∃ (N' : Network), net_trans N (net_label.τ_dequeue r p lab S) N' ∧
      (consistentInstrumentation N' = some MN') := by
  have hgen := h
  generalize heta : mon_net_label.τ_dequeue r p lab S = eta at hgen
  cases hgen with
  | @comm _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp at heta
  | @lift r0 mt mt' ell hM hmem =>
    cases ell with
    | yes_send _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | yes_recv _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | no_out _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | no_inp _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | silent p0 lab0 S0 =>
      simp only [mon_net_label.ofmon_label] at heta
      injection heta with hr hp hlab hS
      subst hr
      subst hp
      subst hlab
      subst hS
      cases hM with
      | @dequeue stq stq' M _ _ _ hSQ =>
        obtain ⟨hmemN, hM⟩ := consistentInstrumentation_inv_mem hmem hCons
        cases hSQ with
        | @dequeue T T' Q Q' _ _ _ hST hQ =>
          have hTNR : T.NoRec := hNR _ hmemN
          have hTWF : T.WellFormed := hwf.2.1 _ hmemN
          have hTND : T.NoDupl := hTWF.1
          obtain ⟨seen, left, hQeq, hQ'eq, hseen⟩ := queue_dequeue_some_iff hQ
          subst hQeq
          subst hQ'eq
          have hEnc : monitor_fold (T, seen ++ [QueueMessage.msg p lab S] ++ left) M :=
            monitor_fold_val_partial_eq_of_some hM
          have hTrans : monitor_fold (T', seen ++ left) M :=
            monitor_fold_absorb_dequeue_transfer_norec hTNR hTND hTWF hseen hST hEnc
          have hTWF' : T'.WellFormed := SessionType.wellFormedPreserved T _ T' hTWF hST
          have hM' : monitor_fold_val_partial (T', seen ++ left) = some M :=
            monitor_fold_val_partial_eq_of_monitor_fold hTWF' hTrans
          have hCons' : consistentInstrumentation (Network.replace N r (T', seen ++ left)) =
              some (MN.replace r ((T', seen ++ left), M)) :=
            consistentInstrumentation_replace hCons hM'
          exact ⟨_, net_trans.dequeue (sq_trans.dequeue hST hQ) hmemN, hCons'⟩

end DequeueCorrespondence

section NetworkToMonitor
/-- A communication step of a NoRec, well-formed, output-live, half-duplex
    network (no self-sends, all roles present) is matched by its consistent
    instrumentation, and the target instrumentation is consistent for the
    post-state. -/
theorem network_comm_mon_comm_norec {N N' : Network} {MN : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort}
    (hNR : N.NoRec) (hWF : N.WellFormed)
    (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : net_trans N (net_label.τ_comm p q lab S) N') :
    ∃ MN', mon_net_trans MN (mon_net_label.τ_comm p q lab S) MN' ∧
      consistentInstrumentation N' = some MN' := by
  have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
    simp [is_internal_net_label]
  have hStar : net_trans_star N N' := net_trans_star.step hInt hTr (net_trans_star.refl _)
  have hNR' : N'.NoRec := net_trans_preserves_norec hTr hNR
  have hWF' : N'.WellFormed := Network.wellFormedPreserved _ _ _ hWF hTr hInt
  have hNS' : N'.NoSelf := net_trans_preserves_no_self hTr hNS
  have hRP' : N'.RolesPresent := net_trans_star_preserves_roles_present hStar hRP
  have hLive' : IsOutputLiveNetwork N' := output_live_persistent hWF hLive hStar
  have hHD' : IsHalfDuplex N' := hHD.star hStar
  cases hTr with
  | comm hne h_send h_recv hmem_p hmem_q =>
    cases h_send with
    | @send Tp Tp' Qp _ _ _ hST_send =>
      cases h_recv with
      | @recv Tq Qq _ _ _ =>
        obtain ⟨Mp, hVal_p, hMN_p⟩ := mem_consistentInstrumentation hmem_p hCons
        obtain ⟨Mq, hVal_q, hMN_q⟩ := mem_consistentInstrumentation hmem_q hCons
        have hEnc_p : monitor_fold (Tp, Qp) Mp := monitor_fold_val_partial_eq_of_some hVal_p
        have hEnc_q : monitor_fold (Tq, Qq) Mq := monitor_fold_val_partial_eq_of_some hVal_q
        have hmem_p' : (p, (Tp', Qp)) ∈
            Network.replace (Network.replace N p (Tp', Qp)) q
              (Tq, Qq ++ [QueueMessage.msg p lab S]) :=
          mem_replace_other (by simp [Network.replace]) hne
        have hmem_q' : (q, (Tq, Qq ++ [QueueMessage.msg p lab S])) ∈
            Network.replace (Network.replace N p (Tp', Qp)) q
              (Tq, Qq ++ [QueueMessage.msg p lab S]) := by
          simp [Network.replace]
        have hTpNR : Tp'.NoRec := hNR' _ hmem_p'
        have hTpWF : Tp'.WellFormed := hWF'.2.1 _ hmem_p'
        have hTqNR : Tq.NoRec := hNR' _ hmem_q'
        have hTqWF : Tq.WellFormed := hWF'.2.1 _ hmem_q'
        have hTqND : Tq.NoDupl := hTqWF.1
        -- Sender absorption: the continuation absorbs the unchanged queue,
        -- else the post-state carries a `Cannot` entry and is non-live.
        have hAcc_p : ∃ M', monitor_fold (Tp', Qp) M' := by
          by_contra hNo
          have hCannot : CannotAlwaysDrainInternalDeep Tp' Qp :=
            mon_reject_implies_nodrain_norec Tp' Qp hTpNR hTpWF hNo
          have hnd : ¬ CanAlwaysDrainInternalDeep Tp' Qp :=
            fun hD => (deep_iff_not_cannot_norec hTpNR hTpWF).mp hD hCannot
          rcases no_deep_drain_no_output_liveness_hd_norec hNR' hWF' hHD' hNS' hRP'
            hmem_p' hnd with hNL | hNH
          · exact hNL hLive'
          · exact hNH hHD'
        have hTpSrcNR : Tp.NoRec := hNR _ hmem_p
        have hTpSrcWF : Tp.WellFormed := hWF.2.1 _ hmem_p
        have hTpSrcND : Tp.NoDupl := hTpSrcWF.1
        obtain ⟨Mp', hEnc_p', hYes_p⟩ :=
          monitor_fold_aux_out_aux_norec hTpSrcNR hTpSrcND hST_send hEnc_p hAcc_p
        -- Receiver acceptance: if the monitor rejects the incoming message,
        -- the extended queue has no absorption, so the post-state is non-live.
        have hAccept : ∃ M', mon_tr_yes Mq (ext_tag.recv p lab S) M' := by
          by_contra hNo
          push Not at hNo
          have hNoEnc : ¬ ∃ M', monitor_fold (Tq, Qq ++ [QueueMessage.msg p lab S]) M' := by
            rintro ⟨M', hM'⟩
            have hM'' : monitor_fold_aux (Qq ++ [QueueMessage.msg p lab S]) Tq M' := hM'
            obtain ⟨U, hU, hRest⟩ := monitor_fold_aux_append_iff.mp hM''
            have hUq : U = Mq :=
              monitor_fold_aux_value_unique Qq Tq U Mq hTqWF hU hEnc_q
            subst hUq
            obtain ⟨T_mid, hYes, hTail⟩ := hRest
            have hEq : M' = T_mid := hTail
            subst hEq
            exact hNo _ hYes
          have hCannot : CannotAlwaysDrainInternalDeep Tq (Qq ++ [QueueMessage.msg p lab S]) :=
            mon_reject_implies_nodrain_norec Tq _ hTqNR hTqWF hNoEnc
          have hnd : ¬ CanAlwaysDrainInternalDeep Tq (Qq ++ [QueueMessage.msg p lab S]) :=
            fun hD => (deep_iff_not_cannot_norec hTqNR hTqWF).mp hD hCannot
          rcases no_deep_drain_no_output_liveness_hd_norec hNR' hWF' hHD' hNS' hRP'
            hmem_q' hnd with hNL | hNH
          · exact hNL hLive'
          · exact hNH hHD'
        obtain ⟨Mq', hYes_q⟩ := hAccept
        have hSQ_send : sq_trans (Tp, Qp) (sq_action.send q lab S) (Tp', Qp) :=
          sq_trans.send hST_send
        have hSQ_recv : sq_trans (Tq, Qq) (sq_action.recv p lab S)
            (Tq, Qq ++ [QueueMessage.msg p lab S]) := sq_trans.recv
        have hMonSend : mon_trans ((Tp, Qp), Mp) (mon_label.yes_send q lab S)
            ((Tp', Qp), Mp') := mon_trans.good_send hSQ_send hYes_p
        have hMonRecv : mon_trans ((Tq, Qq), Mq) (mon_label.yes_recv p lab S)
            ((Tq, Qq ++ [QueueMessage.msg p lab S]), Mq') :=
          mon_trans.good_recv hSQ_recv hYes_q
        have hComm : mon_net_trans MN (mon_net_label.τ_comm p q lab S)
            ((MN.replace p ((Tp', Qp), Mp')).replace q
              ((Tq, Qq ++ [QueueMessage.msg p lab S]), Mq')) :=
          mon_net_trans.comm hMonSend hMonRecv hMN_p hMN_q
        have hEnc_q' : monitor_fold (Tq, Qq ++ [QueueMessage.msg p lab S]) Mq' :=
          monitor_fold_aux_append_iff.mpr ⟨Mq, hEnc_q, Mq', hYes_q, rfl⟩
        have hVal_p' : monitor_fold_val_partial (Tp', Qp) = some Mp' :=
          monitor_fold_val_partial_eq_of_monitor_fold hTpWF hEnc_p'
        have hVal_q' : monitor_fold_val_partial (Tq, Qq ++ [QueueMessage.msg p lab S]) = some Mq' :=
          monitor_fold_val_partial_eq_of_monitor_fold hTqWF hEnc_q'
        have hCons1 : consistentInstrumentation (Network.replace N p (Tp', Qp)) =
            some (MonitoredNetwork.replace MN p ((Tp', Qp), Mp')) :=
          consistentInstrumentation_replace hCons hVal_p'
        have hCons2 : consistentInstrumentation
            (Network.replace (Network.replace N p (Tp', Qp)) q
              (Tq, Qq ++ [QueueMessage.msg p lab S])) =
            some ((MN.replace p ((Tp', Qp), Mp')).replace q
              ((Tq, Qq ++ [QueueMessage.msg p lab S]), Mq')) :=
          consistentInstrumentation_replace hCons1 hVal_q'
        exact ⟨_, hComm, hCons2⟩
/-- A dequeue step of a NoRec, well-formed network is matched by its
    consistent instrumentation, and the target instrumentation is consistent
    for the post-state. The monitor is unchanged
    (`mon_trans.dequeue`); absorption transfer is `type_mon_dequeuing_norec`. -/
theorem network_dequeue_mon_dequeue_norec {N N' : Network} {MN : MonitoredNetwork}
    {q p : Role} {lab : Lab} {S : DataSort}
    (hNR : N.NoRec) (hWF : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : net_trans N (net_label.τ_dequeue q p lab S) N') :
    ∃ MN', mon_net_trans MN (mon_net_label.τ_dequeue q p lab S) MN' ∧
      consistentInstrumentation N' = some MN' := by
  obtain ⟨MN', hCons', hStep⟩ := type_mon_dequeuing_norec hTr hNR hWF hCons
  exact ⟨MN', hStep, hCons'⟩
end NetworkToMonitor


section MonitorToNetwork
/-- A monitored dequeue step reflects to a network dequeue step: if the
    consistent instrumentation takes `τ_dequeue q p lab S` to `MN'`, the
    network takes the same step to some `N'` consistent with `MN'`
    (`mon_type_dequeuing_norec`). -/
theorem mon_dequeue_network_dequeue_norec {N : Network} {MN MN' : MonitoredNetwork}
    {q p : Role} {lab : Lab} {S : DataSort}
    (hNR : N.NoRec) (hWF : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : mon_net_trans MN (mon_net_label.τ_dequeue q p lab S) MN') :
    ∃ N', net_trans N (net_label.τ_dequeue q p lab S) N' ∧
      consistentInstrumentation N' = some MN' := by
  obtain ⟨N', hStep, hCons'⟩ := mon_type_dequeuing_norec hNR hWF hCons hTr
  exact ⟨N', hStep, hCons'⟩
/-- A monitored communication step reflects to a network communication step:
    if the consistent instrumentation takes `τ_comm p q lab S` to `MN'`, the
    network takes the same step to some `N'` consistent with `MN'`. The `lift`
    case is impossible (`ofmon_label` never yields `τ_comm`); `p ≠ q` comes
    from `NoSelf` via the send step; sender absorption goes through
    `mon_reject_implies_nodrain_norec` + `no_deep_drain_no_output_liveness_hd_norec` as in
    `network_comm_mon_comm_norec`, pinned to the given monitor target by
    `mon_tr_yes_target_unique`. -/
theorem mon_comm_network_comm_norec {N : Network} {MN MN' : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort}
    (hNR : N.NoRec) (hWF : N.WellFormed)
    (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : mon_net_trans MN (mon_net_label.τ_comm p q lab S) MN') :
    ∃ N', net_trans N (net_label.τ_comm p q lab S) N' ∧
      consistentInstrumentation N' = some MN' := by
  have hgen := hTr
  generalize heta : mon_net_label.τ_comm p q lab S = eta at hgen
  cases hgen with
  | @comm pp qq llab SS mtp mtp' mtq mtq' h_send h_recv hmem_p hmem_q =>
    injection heta with hp hq hlab hS
    subst hp
    subst hq
    subst hlab
    subst hS
    cases h_send with
    | @good_send stqp stqp' Mp Mp' _ _ _ hSQ_send hYes_send =>
      cases h_recv with
      | @good_recv stqq stqq' Mq Mq' _ _ _ hSQ_recv hYes_recv =>
        cases hSQ_send with
        | @send Tp Tp' Qp _ _ _ hST_send =>
          cases hSQ_recv with
          | @recv Tq Qq _ _ _ =>
            obtain ⟨hmem_p_N, hVal_p⟩ :=
              consistentInstrumentation_inv_mem hmem_p hCons
            obtain ⟨hmem_q_N, hVal_q⟩ :=
              consistentInstrumentation_inv_mem hmem_q hCons
            have hEnc_p : monitor_fold (Tp, Qp) Mp :=
              monitor_fold_val_partial_eq_of_some hVal_p
            have hEnc_q : monitor_fold (Tq, Qq) Mq :=
              monitor_fold_val_partial_eq_of_some hVal_q
            have hTpSrcNR : Tp.NoRec := hNR _ hmem_p_N
            have hTpSrcWF : Tp.WellFormed := hWF.2.1 _ hmem_p_N
            have hTpSrcND : Tp.NoDupl := hTpSrcWF.1
            have hne : p ≠ q :=
              out_ne_self_of_noSelf (hNS p Tp Qp hmem_p_N) hST_send
            have hSQ_send : sq_trans (Tp, Qp) (sq_action.send q lab S) (Tp', Qp) :=
              sq_trans.send hST_send
            have hSQ_recv : sq_trans (Tq, Qq) (sq_action.recv p lab S)
                (Tq, Qq ++ [QueueMessage.msg p lab S]) := sq_trans.recv
            have hStep : net_trans N (net_label.τ_comm p q lab S)
                ((N.replace p (Tp', Qp)).replace q (Tq, Qq ++ [QueueMessage.msg p lab S])) :=
              net_trans.comm hne hSQ_send hSQ_recv hmem_p_N hmem_q_N
            have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
              simp [is_internal_net_label]
            have hStar : net_trans_star N
                ((N.replace p (Tp', Qp)).replace q (Tq, Qq ++ [QueueMessage.msg p lab S])) :=
              net_trans_star.step hInt hStep (net_trans_star.refl _)
            have hNR'' := net_trans_preserves_norec hStep hNR
            have hWF'' := Network.wellFormedPreserved _ _ _ hWF hStep hInt
            have hNS'' := net_trans_preserves_no_self hStep hNS
            have hRP'' := net_trans_star_preserves_roles_present hStar hRP
            have hLive'' := output_live_persistent hWF hLive hStar
            have hHD'' := hHD.star hStar
            have hmem_p'' : (p, (Tp', Qp)) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) :=
              mem_replace_other (by simp [Network.replace]) hne
            have hmem_q'' : (q, (Tq, Qq ++ [QueueMessage.msg p lab S])) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) := by
              simp [Network.replace]
            have hTp'NR : Tp'.NoRec := hNR'' _ hmem_p''
            have hTp'WF : Tp'.WellFormed := hWF''.2.1 _ hmem_p''
            have hTqNR : Tq.NoRec := hNR'' _ hmem_q''
            have hTqWF : Tq.WellFormed := hWF''.2.1 _ hmem_q''
            have hTqND : Tq.NoDupl := hTqWF.1
            have hAcc_p : ∃ M', monitor_fold (Tp', Qp) M' := by
              by_contra hNo
              have hCannot : CannotAlwaysDrainInternalDeep Tp' Qp :=
                mon_reject_implies_nodrain_norec Tp' Qp hTp'NR hTp'WF hNo
              have hnd : ¬ CanAlwaysDrainInternalDeep Tp' Qp :=
                fun hD => (deep_iff_not_cannot_norec hTp'NR hTp'WF).mp hD hCannot
              rcases no_deep_drain_no_output_liveness_hd_norec hNR'' hWF'' hHD'' hNS'' hRP''
                hmem_p'' hnd with hNL | hNH
              · exact hNL hLive''
              · exact hNH hHD''
            obtain ⟨M1, hEnc1, hYes1⟩ :=
              monitor_fold_aux_out_aux_norec hTpSrcNR hTpSrcND hST_send hEnc_p hAcc_p
            have hMpWF : Mp.WellFormed := monitor_fold_aux_wf Qp Tp Mp hTpSrcWF hEnc_p
            have hMpEq : M1 = Mp' :=
              mon_tr_yes_target_unique hMpWF hYes1 hYes_send
            rw [hMpEq] at hEnc1
            have hEnc_q' : monitor_fold (Tq, Qq ++ [QueueMessage.msg p lab S]) Mq' :=
              monitor_fold_aux_append_iff.mpr ⟨Mq, hEnc_q, Mq', hYes_recv, rfl⟩
            have hVal_p' : monitor_fold_val_partial (Tp', Qp) = some Mp' :=
              monitor_fold_val_partial_eq_of_monitor_fold hTp'WF hEnc1
            have hVal_q' : monitor_fold_val_partial (Tq, Qq ++ [QueueMessage.msg p lab S]) = some Mq' :=
              monitor_fold_val_partial_eq_of_monitor_fold hTqWF hEnc_q'
            have hCons1 : consistentInstrumentation (Network.replace N p (Tp', Qp)) =
                some (MonitoredNetwork.replace MN p ((Tp', Qp), Mp')) :=
              consistentInstrumentation_replace hCons hVal_p'
            have hCons2 : consistentInstrumentation
                (Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S])) =
                some ((MN.replace p ((Tp', Qp), Mp')).replace q
                  ((Tq, Qq ++ [QueueMessage.msg p lab S]), Mq')) :=
              consistentInstrumentation_replace hCons1 hVal_q'
            exact ⟨_, hStep, hCons2⟩
  | @lift r0 mt mt' ell hM hmem =>
    cases ell with
    | yes_send _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | yes_recv _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | no_out _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | no_inp _ _ _ => simp [mon_net_label.ofmon_label] at heta
    | silent _ _ _ => simp [mon_net_label.ofmon_label] at heta
end MonitorToNetwork
