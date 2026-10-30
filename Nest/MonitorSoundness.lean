import Nest.DrainNonLiveness
import Nest.DequeueCorrespondence
import Nest.CoverDeep

/-!
# MonitorSoundness: the monitor soundness theorem.

The culminating result: a well-formed, roles-present, no-self-send,
half-duplex, output-live and deeply prunable network is
internally bisimilar to its consistent instrumentation
(`monitor_soundness`). Network-level preservation of monitorability and
deep adequacy along `net_trans`/`net_trans_star`, the no-monitor-fold ⇒
drain-failure bridge, and the communication correspondence in both
directions (`network_comm_mon_comm`, `mon_comm_network_comm`);
the dequeue directions come from `Nest.DequeueCorrespondence`.
-/

section MonitorSoundness

/-- A network is monitorable when every entry session type has finite prune closure. -/
def Network.Monitorable (N : Network) : Prop :=
  ∀ x ∈ N, Drainability.Monitorable x.2.1

/-- A network is deeply prunable when every entry session type is `Prunable` with empty seen set. -/
def Network.Prunable (N : Network) : Prop :=
  ∀ x ∈ N, _root_.Prunable [] x.2.1

/-- A session type is deeply adequate when it is `Prunable` under some evidenced seen set. -/
def SessionType.DeepAdequate (T : SessionType) : Prop :=
  ∃ seen, SeenEvidence seen ∧ _root_.Prunable seen T

/-- A network is deeply adequate when every entry session type is. -/
def Network.DeepAdequate (N : Network) : Prop :=
  ∀ x ∈ N, x.2.1.DeepAdequate

/-- Every session step embeds into prune-steps reachability (single session step as a prune-RTC). -/
theorem st_trans_to_prune_rtc {T T' : SessionType} {α : st_label}
    (h : st_trans T α T') :
    Relation.ReflTransGen Drainability.PruneStep T T' := by
  induction h with
  | intC hmem =>
    exact Relation.ReflTransGen.single (Drainability.PruneStep.intC hmem)
  | extC hmem =>
    exact Relation.ReflTransGen.single (Drainability.PruneStep.extC hmem)
  | tRec _ ih =>
    exact (Relation.ReflTransGen.single Drainability.PruneStep.trec).trans ih

/-- Session steps preserve monitorability (prune-closure finiteness is monotone along `PruneStep`). -/
theorem st_trans_preserves_monitorable {T T' : SessionType} {α : st_label}
    (h : st_trans T α T') (hMon : Drainability.Monitorable T) :
    Drainability.Monitorable T' :=
  hMon.mono (st_trans_to_prune_rtc h)

/-- Session steps preserve deep adequacy (adequacy derivations transport along the step). -/
theorem st_trans_preserves_deep_adequate {T T' : SessionType} {α : st_label}
    (h : st_trans T α T') (hAd : T.DeepAdequate) : T'.DeepAdequate := by
  induction h with
  | intC hmem =>
    obtain ⟨seen, hev, hPrunable⟩ := hAd
    cases hPrunable with
    | intC _ _ hall _ => exact ⟨seen, hev, hall _ hmem⟩
  | extC hmem =>
    obtain ⟨seen, hev, hPrunable⟩ := hAd
    cases hPrunable with
    | extC _ _ _ hall _ => exact ⟨seen, hev, hall _ hmem⟩
  | @tRec X B Tsub α hsub ih =>
    obtain ⟨seen, hev, hPrunable⟩ := hAd
    have hev1 : SeenEvidence (SessionType.tRec X B :: seen) :=
      seen_ev_extend hev hPrunable
    have hAdSub : (substSessionType B X (SessionType.tRec X B)).DeepAdequate := by
      cases hPrunable with
      | trec_new _ _ _ _ hsubD _ => exact ⟨_, hev1, hsubD⟩
      | trec_seen _ _ _ hmem _ =>
        obtain ⟨X0, B0, hEq, hEv⟩ := hev _ hmem
        simp only [SessionType.tRec.injEq] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        exact ⟨_, hev1, hEv⟩
    exact ih hAdSub

/-- Monitorability is preserved by pointwise network updates with monitorable replacements. -/
theorem Network.Monitorable.replace {N : Network} {r : Role}
    {stq : SessionTypeWithQueue}
    (hMon : N.Monitorable) (hNew : Drainability.Monitorable stq.1) :
    (Network.replace N r stq).Monitorable := by
  intro x hx
  unfold Network.replace at hx
  simp only [List.mem_cons, List.mem_filter] at hx
  rcases hx with rfl | ⟨hxN, -⟩
  · exact hNew
  · exact hMon x hxN

/-- Deep adequacy is preserved by pointwise network updates with deeply adequate replacements. -/
theorem Network.DeepAdequate.replace {N : Network} {r : Role}
    {stq : SessionTypeWithQueue}
    (hAd : N.DeepAdequate) (hNew : stq.1.DeepAdequate) :
    (Network.replace N r stq).DeepAdequate := by
  intro x hx
  unfold Network.replace at hx
  simp only [List.mem_cons, List.mem_filter] at hx
  rcases hx with rfl | ⟨hxN, -⟩
  · exact hNew
  · exact hAd x hxN

/-- Network transitions preserve monitorability (each entry either steps or stays). -/
theorem net_trans_preserves_monitorable {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hMon : N.Monitorable) : N'.Monitorable := by
  cases hTr with
  | @io_send r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @send T T' Q q lab' S' hST =>
      have hMonT : Drainability.Monitorable T := hMon _ hmem
      have hMonT' : Drainability.Monitorable T' := st_trans_preserves_monitorable hST hMonT
      exact Network.Monitorable.replace hMon hMonT'
  | @io_recv r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @recv T Q q lab' S' =>
      have hMonT : Drainability.Monitorable T := hMon _ hmem
      exact Network.Monitorable.replace hMon hMonT
  | @dequeue r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @dequeue T T' Q Q' q lab' S' hST hQ =>
      have hMonT : Drainability.Monitorable T := hMon _ hmem
      have hMonT' : Drainability.Monitorable T' := st_trans_preserves_monitorable hST hMonT
      exact Network.Monitorable.replace hMon hMonT'
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    cases h_send with
    | @send Tp Tp' Qp q' lab' S' hST_send =>
      cases h_recv with
      | @recv Tq Qq p' lab'' S'' =>
        have hMonP : Drainability.Monitorable Tp := hMon _ hmem_p
        have hMonP' : Drainability.Monitorable Tp' :=
          st_trans_preserves_monitorable hST_send hMonP
        have hMid : (Network.replace N p (Tp', Qp)).Monitorable :=
          Network.Monitorable.replace hMon hMonP'
        have hMonQ : Drainability.Monitorable Tq := hMid _ (mem_replace_other hmem_q (Ne.symm hne))
        exact Network.Monitorable.replace hMid hMonQ

/-- Network transitions preserve deep adequacy (each entry either steps or stays). -/
theorem net_trans_preserves_deep_adequate {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hAd : N.DeepAdequate) : N'.DeepAdequate := by
  cases hTr with
  | @io_send r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @send T T' Q q lab' S' hST =>
      have hAdT : T.DeepAdequate := hAd _ hmem
      have hAdT' : T'.DeepAdequate := st_trans_preserves_deep_adequate hST hAdT
      exact Network.DeepAdequate.replace hAd hAdT'
  | @io_recv r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @recv T Q q lab' S' =>
      have hAdT : T.DeepAdequate := hAd _ hmem
      exact Network.DeepAdequate.replace hAd hAdT
  | @dequeue r p stq stq' lab S hSQ hmem =>
    cases hSQ with
    | @dequeue T T' Q Q' q lab' S' hST hQ =>
      have hAdT : T.DeepAdequate := hAd _ hmem
      have hAdT' : T'.DeepAdequate := st_trans_preserves_deep_adequate hST hAdT
      exact Network.DeepAdequate.replace hAd hAdT'
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    cases h_send with
    | @send Tp Tp' Qp q' lab' S' hST_send =>
      cases h_recv with
      | @recv Tq Qq p' lab'' S'' =>
        have hAdP : Tp.DeepAdequate := hAd _ hmem_p
        have hAdP' : Tp'.DeepAdequate := st_trans_preserves_deep_adequate hST_send hAdP
        have hMid : (Network.replace N p (Tp', Qp)).DeepAdequate :=
          Network.DeepAdequate.replace hAd hAdP'
        have hAdQ : Tq.DeepAdequate := hMid _ (mem_replace_other hmem_q (Ne.symm hne))
        exact Network.DeepAdequate.replace hMid hAdQ

/-- Monitorability persists along reflexive-transitive network runs. -/
theorem net_trans_star_preserves_monitorable {N N' : Network}
    (hStar : net_trans_star N N') (hMon : N.Monitorable) : N'.Monitorable := by
  induction hStar with
  | refl => exact hMon
  | step _ hTr _ ih => exact ih (net_trans_preserves_monitorable hTr hMon)

/-- Deep adequacy persists along reflexive-transitive network runs. -/
theorem net_trans_star_preserves_deep_adequate {N N' : Network}
    (hStar : net_trans_star N N') (hAd : N.DeepAdequate) : N'.DeepAdequate := by
  induction hStar with
  | refl => exact hAd
  | step _ hTr _ ih => exact ih (net_trans_preserves_deep_adequate hTr hAd)

/-- Empty-seen prunability at every entry yields network deep adequacy (witnessed by the empty
   evidence). -/
theorem Network.DeepAdequate.of_Prunable {N : Network}
    (hPrunable : N.Prunable) : N.DeepAdequate := by
  intro x hx
  exact ⟨[], seen_ev_empty, hPrunable x hx⟩

/-- Empty-seen prunability at every entry of a well-formed network yields network
    monitorability (per-entry `prunable_implies_monitorable`). -/
theorem Network.Monitorable.of_Prunable {N : Network}
    (hWF : N.WellFormed) (hPrunable : N.Prunable) : N.Monitorable := by
  intro x hx
  obtain ⟨r, T, Q⟩ := x
  exact prunable_implies_monitorable (hWF.2.1 _ hx) (hPrunable _ hx)

/-- No monitor fold plus well-formedness, monitorability and deep adequacy yields drain failure
   (`Cannot`). -/
theorem monitor_no_implies_cannotdrain_of_adequate {T : SessionType} {Q : Queue}
    (hWF : T.WellFormed) (hMon : Drainability.Monitorable T)
    (hAd : T.DeepAdequate) (hNo : ¬ ∃ M, monitor_fold (T, Q) M) :
    Drainability.CannotAlwaysDrainInternalDeepRec T Q := by
  obtain ⟨seen, hev, hPrunable⟩ := hAd
  by_contra hCon
  have hCan : Drainability.CanAlwaysDrainInternalDeepRec T Q :=
    Drainability.drainrec_can_of_not_cannot hWF hMon hCon
  have hCov := deep_cover Q T hWF hMon seen hev hPrunable hCan
  obtain ⟨M, hEnc⟩ := can_enc_of_cover Q T hWF hCan hCov
  exact hNo ⟨M, hEnc⟩

/-- Forward communication correspondence: a network `τ_comm` is matched by the instrumented network,
   preserving consistent instrumentation. -/
theorem network_comm_mon_comm {N N' : Network} {MN : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort}
    (hMon : N.Monitorable) (hDeepAd : N.DeepAdequate)
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : net_trans N (net_label.τ_comm p q lab S) N') :
    ∃ MN', mon_net_trans MN (mon_net_label.τ_comm p q lab S) MN' ∧
      consistentInstrumentation N' = some MN' := by
  have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
    simp [is_internal_net_label]
  have hStar : net_trans_star N N' := net_trans_star.step hInt hTr (net_trans_star.refl _)
  have hWF' : N'.WellFormed := Network.wellFormedPreserved _ _ _ hWF hTr hInt
  have hNS' : N'.NoSelf := net_trans_preserves_no_self hTr hNS
  have hRP' : N'.RolesPresent := net_trans_star_preserves_roles_present hStar hRP
  have hLive' : IsOutputLiveNetwork N' := output_live_persistent hWF hLive hStar
  have hHD' : IsHalfDuplex N' := hHD.star hStar
  have hMon' : N'.Monitorable := net_trans_star_preserves_monitorable hStar hMon
  have hDeepAd' : N'.DeepAdequate := net_trans_star_preserves_deep_adequate hStar hDeepAd
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
        have hTpWF : Tp'.WellFormed := hWF'.2.1 _ hmem_p'
        have hTpMon : Drainability.Monitorable Tp' := hMon' _ hmem_p'
        have hTpAd : Tp'.DeepAdequate := hDeepAd' _ hmem_p'
        have hTqWF : Tq.WellFormed := hWF'.2.1 _ hmem_q'
        have hTqMon : Drainability.Monitorable Tq := hMon' _ hmem_q'
        have hTqAd : Tq.DeepAdequate := hDeepAd' _ hmem_q'
        have hAcc_p : ∃ M', monitor_fold (Tp', Qp) M' := by
          by_contra hNo
          have hCannot : Drainability.CannotAlwaysDrainInternalDeepRec Tp' Qp :=
            monitor_no_implies_cannotdrain_of_adequate hTpWF hTpMon hTpAd hNo
          exact cannotdrain_implies_not_output_live hWF' hRP' hNS' hHD'
            hmem_p' hTpWF hTpMon hCannot hLive'
        have hTpSrcWF : Tp.WellFormed := hWF.2.1 _ hmem_p
        obtain ⟨Mp', hEnc_p', hYes_p⟩ :=
          monitor_fold_aux_out_aux_general hTpSrcWF hST_send hEnc_p hAcc_p
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
          have hCannot : Drainability.CannotAlwaysDrainInternalDeepRec Tq
              (Qq ++ [QueueMessage.msg p lab S]) :=
            monitor_no_implies_cannotdrain_of_adequate hTqWF hTqMon hTqAd hNoEnc
          exact cannotdrain_implies_not_output_live hWF' hRP' hNS' hHD'
            hmem_q' hTqWF hTqMon hCannot hLive'
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

/-- Backward communication correspondence: a monitored `τ_comm` comes from a network `τ_comm` with
   consistent instrumentation preserved. -/
theorem mon_comm_network_comm {N : Network} {MN MN' : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort}
    (hMon : N.Monitorable) (hDeepAd : N.DeepAdequate)
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
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
            have hTpSrcWF : Tp.WellFormed := hWF.2.1 _ hmem_p_N
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
            have hWF'' := Network.wellFormedPreserved _ _ _ hWF hStep hInt
            have hNS'' := net_trans_preserves_no_self hStep hNS
            have hRP'' := net_trans_star_preserves_roles_present hStar hRP
            have hLive'' := output_live_persistent hWF hLive hStar
            have hHD'' := hHD.star hStar
            have hMon'' := net_trans_star_preserves_monitorable hStar hMon
            have hDeepAd'' := net_trans_star_preserves_deep_adequate hStar hDeepAd
            have hmem_p'' : (p, (Tp', Qp)) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) :=
              mem_replace_other (by simp [Network.replace]) hne
            have hmem_q'' : (q, (Tq, Qq ++ [QueueMessage.msg p lab S])) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) := by
              simp [Network.replace]
            have hTp'WF : Tp'.WellFormed := hWF''.2.1 _ hmem_p''
            have hTp'Mon : Drainability.Monitorable Tp' := hMon'' _ hmem_p''
            have hTp'Ad : Tp'.DeepAdequate := hDeepAd'' _ hmem_p''
            have hTqWF : Tq.WellFormed := hWF''.2.1 _ hmem_q''
            have hAcc_p : ∃ M', monitor_fold (Tp', Qp) M' := by
              by_contra hNo
              have hCannot : Drainability.CannotAlwaysDrainInternalDeepRec Tp' Qp :=
                monitor_no_implies_cannotdrain_of_adequate hTp'WF hTp'Mon hTp'Ad hNo
              exact cannotdrain_implies_not_output_live hWF'' hRP'' hNS'' hHD''
                hmem_p'' hTp'WF hTp'Mon hCannot hLive''
            obtain ⟨M1, hEnc1, hYes1⟩ :=
              monitor_fold_aux_out_aux_general hTpSrcWF hST_send hEnc_p hAcc_p
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

/-- Monitor soundness: a well-formed, live, half-duplex and deeply prunable network is
   internally bisimilar to its consistent instrumentation (monitorability follows
   from prunability via `Network.Monitorable.of_Prunable`). -/
theorem monitor_soundness {N : Network} {MN : MonitoredNetwork}
    (hwf : N.WellFormed)
    (hNS : N.NoSelf)
    (hRP : N.RolesPresent)
    (hPrunable : N.Prunable)
    (h_output_live : IsOutputLiveNetwork N)
    (h_half_duplex : IsHalfDuplex N)
    (hCons : consistentInstrumentation N = some MN) :
    InternallyBisimilar N MN := by
  have hMon : N.Monitorable := Network.Monitorable.of_Prunable hwf hPrunable
  have hDeepAd0 : N.DeepAdequate := Network.DeepAdequate.of_Prunable hPrunable
  let R : Network → MonitoredNetwork → Prop :=
    fun N' MN' => consistentInstrumentation N' = some MN' ∧ net_trans_star N N'
  have hR0 : R N MN := ⟨hCons, net_trans_star.refl _⟩
  refine ⟨R, hR0, ?_⟩
  rintro N' MN' ⟨hCons', h_star⟩ μ₁ hIntLbl₁
  have hWF' : N'.WellFormed := net_trans_preserves_well_formed hwf h_star
  have hRP' : N'.RolesPresent := net_trans_star_preserves_roles_present h_star hRP
  have hNS' : N'.NoSelf := net_trans_star_preserves_no_self h_star hNS
  have hHD' : IsHalfDuplex N' := h_half_duplex.star h_star
  have hLive' : IsOutputLiveNetwork N' := output_live_persistent hwf h_output_live h_star
  have hMon' : N'.Monitorable := net_trans_star_preserves_monitorable h_star hMon
  have hDeepAd' : N'.DeepAdequate :=
    net_trans_star_preserves_deep_adequate h_star hDeepAd0
  constructor
  · intro N'' hN'_tr
    cases μ₁ with
    | io_send _ _ _ _ => exfalso; exact hIntLbl₁
    | io_recv _ _ _ _ => exfalso; exact hIntLbl₁
    | τ_dequeue r p lab S =>
      obtain ⟨MN'', hStep, hCons''⟩ :=
        network_dequeue_mon_dequeue hWF' hCons' hN'_tr
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hN'_tr (net_trans_star.refl _))
      exact ⟨MN'', mon_net_label.τ_dequeue r p lab S, by simp [is_internal_mon_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨MN'', hStep, hCons''⟩ :=
        network_comm_mon_comm hMon' hDeepAd' hWF' hRP' hNS' hHD' hLive' hCons' hN'_tr
      have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hN'_tr (net_trans_star.refl _))
      exact ⟨MN'', mon_net_label.τ_comm p q lab S, by simp [is_internal_mon_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
  · intro M μ₂ hIntLbl₂ hMN'_tr
    cases μ₂ with
    | io_yes_send _ _ _ _ => exfalso; exact hIntLbl₂
    | io_yes_recv _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_out _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_inp _ _ _ _ => exfalso; exact hIntLbl₂
    | τ_dequeue r p lab S =>
      obtain ⟨N'', hStep, hCons''⟩ :=
        mon_dequeue_network_dequeue hWF' hCons' hMN'_tr
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hStep (net_trans_star.refl _))
      exact ⟨N'', net_label.τ_dequeue r p lab S, by simp [is_internal_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨N'', hStep, hCons''⟩ :=
        mon_comm_network_comm hMon' hDeepAd' hWF' hRP' hNS' hHD' hLive' hCons' hMN'_tr
      have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hStep (net_trans_star.refl _))
      exact ⟨N'', net_label.τ_comm p q lab S, by simp [is_internal_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩

end MonitorSoundness
