import Nest.MonitorLTSCo
import Nest.MonitorToolkitCo
import Nest.SemFoldCo
import Nest.FoldExistsCo
import Nest.LiveCanDrainCo

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorSoundnessCo: coinductive monitor soundness, relationally.

Relational instrumentation (`consistentInstrumentation_co`) and the
two-field `mon_trans_co` (`hSQ` + coinductive `hYes`, no computed
equation), with `InternallyBisimilarCo` (`netLTS`/`mnetLTS_co`).

Follows the architecture of finite `MonitorSoundness`
(`Nest/MonitorSoundness.lean`) — invariant, alignment, forward/backward
correspondence; the relational reformulation (`AlignedCo`,
`InternallyBisimilarCo`/`R`, `MNhostCo`, Eqv-route correspondence)
is new. The ported building blocks used here are credited to
Jules Jacobs <jules.jacobs@inf.ethz.ch>, Nate Foster
<nate.foster@epfl.ch>, and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>
in their home files (`Nest.SemFoldCo`,
`Nest.FoldExistsCo`, `Nest.LiveCanDrainCo`).

Note: `InternallyBisimilar` (`Nest/MonitorLTS.lean`) hardcodes the finite
`mnetLTS`, so the `Co` statement uses `InternallyBisimilarCo` below
(`netLTS`/`mnetLTS_co`).
-/

-- ================================================================
-- Invariant.
-- ================================================================

/-- Network invariant: well-formedness, roles-present, no-self,
    half-duplex, output-live. -/
def InvCo (N : Network) : Prop :=
  N.WellFormed ∧ N.RolesPresent ∧ N.NoSelf ∧ IsHalfDuplex N ∧ IsOutputLiveNetwork N

/-- The invariant persists along single internal steps. -/
theorem InvCo_step {N N' : Network} {label : net_label} (inv : InvCo N)
    (internal : is_internal_net_label label) (step : net_trans N label N') : InvCo N' := by
  have hStar : net_trans_star N N' := net_trans_star.step internal step (net_trans_star.refl _)
  exact ⟨net_trans_preserves_well_formed inv.1 hStar,
    net_trans_star_preserves_roles_present hStar inv.2.1,
    net_trans_preserves_no_self step inv.2.2.1,
    inv.2.2.2.1.star hStar,
    output_live_persistent inv.1 inv.2.2.2.2 hStar⟩

-- ================================================================
-- Monitored-network host projection.
-- ================================================================

/-- Host projection: forget monitor states. -/
def MNhostCo (MN : MonitoredNetwork) : Network :=
  MN.map fun x => (x.1, x.2.1)

/-- Host projection commutes with replacement. -/
theorem MNhostCo_replace (MN : MonitoredNetwork) (r : Role) (stm : MonitoredSessionType) :
    MNhostCo (MN.replace r stm) = (MNhostCo MN).replace r stm.1 := by
  have key : ∀ (L : MonitoredNetwork),
      (L.filter (fun x : Role × MonitoredSessionType => x.1 != r)).map
        (fun x => (x.1, x.2.1)) =
      ((L.map (fun x : Role × MonitoredSessionType => (x.1, x.2.1))).filter
        (fun y : Role × SessionTypeWithQueue => y.1 != r)) := by
    intro L
    induction L with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨r0, stm0⟩
      by_cases heq : r0 = r <;> simp [heq, ih]
  simp [MNhostCo, MonitoredNetwork.replace, Network.replace, key]

/-- Host membership lifts to monitored membership. -/
theorem MNhostCo_mem {MN : MonitoredNetwork} {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (hHost : MNhostCo MN = N) (hmem : (r, stq) ∈ N) :
    ∃ M, (r, (stq, M)) ∈ MN := by
  have hmem' : (r, stq) ∈ MNhostCo MN := hHost ▸ hmem
  unfold MNhostCo at hmem'
  obtain ⟨x, hmemx, hfx⟩ := List.mem_map.mp hmem'
  rcases x with ⟨r', stm⟩
  rcases stm with ⟨stq', M⟩
  simp only at hfx
  obtain ⟨rfl, rfl⟩ := hfx
  exact ⟨M, hmemx⟩

/-- Host projection of a consistent instrumentation is the network. -/
theorem MNhostCo_of_consistent {N : Network} {MN : MonitoredNetwork}
    (hCons : consistentInstrumentation_co N = some MN) : MNhostCo MN = N := by
  induction N generalizing MN with
  | nil =>
    simp only [consistentInstrumentation_co] at hCons
    have hMN : MN = [] := Option.some_inj.mp hCons.symm
    subst hMN
    rfl
  | cons hd tl ih =>
    rcases hd with ⟨r0, stq0⟩
    rw [consistentInstrumentation_co] at hCons
    cases h_e : monitor_fold_val_partial_co stq0 with
    | none => simp [h_e] at hCons
    | some M0 =>
      cases h_c : consistentInstrumentation_co tl with
      | none => simp [h_e, h_c] at hCons
      | some MNtl =>
        rw [h_e, h_c] at hCons
        injection hCons with hMN_eq
        rw [← hMN_eq]
        show (r0, stq0) :: MNhostCo MNtl = (r0, stq0) :: tl
        rw [ih h_c]

/-- Replacement members are new or old-and-apart. -/
theorem MN_mem_replace_inv {MN : MonitoredNetwork} {r : Role} {stm : MonitoredSessionType}
    {r' : Role} {stm' : MonitoredSessionType}
    (h : (r', stm') ∈ MN.replace r stm) :
    (r' = r ∧ stm' = stm) ∨ ((r', stm') ∈ MN ∧ r' ≠ r) := by
  unfold MonitoredNetwork.replace at h
  simp only [List.mem_cons, List.mem_filter, bne_iff_ne] at h
  rcases h with h | ⟨hmem, hne⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨hmem, hne⟩

-- ================================================================
-- Liveness yields semantic folds.
-- ================================================================

/-- Liveness yields a semantic fold for any member. -/
theorem SemFoldCo_exists_InvCo {N : Network} {r : Role} {T : SessionType} {Q : Queue}
    (inv : InvCo N) (member : (r, (T, Q)) ∈ N) : ∃ M, SemFoldCo T Q M := by
  obtain ⟨M, run⟩ := SemFoldCo_exists_of_Can (inv.1.2.1 _ member)
    (LiveCanDrainCo.live_can_drain inv.1 inv.2.1 inv.2.2.1 inv.2.2.2.1 inv.2.2.2.2 member)
  exact ⟨M, run⟩

-- ================================================================
-- Alignment + relation.
-- ================================================================

/-- Alignment: every monitored entry folds its queue semantically. -/
def AlignedCo (MN : MonitoredNetwork) : Prop :=
  ∀ r stq M, (r, (stq, M)) ∈ MN → SemFoldCo stq.1 stq.2 M

/-- Internally bisimilar, coinductive-monitor version (`netLTS`/`mnetLTS_co`). -/
def InternallyBisimilarCo (N : Network) (MN : MonitoredNetwork) : Prop :=
  ∃ r : Network → MonitoredNetwork → Prop, r N MN ∧
    IsInternalBisimulation is_internal_net_label is_internal_mon_net_label netLabelToMonNetLabel
      netLTS mnetLTS_co r

/-- The bisimulation relation: invariant + host equality + alignment. -/
def R (N : Network) (MN : MonitoredNetwork) : Prop :=
  InvCo N ∧ MNhostCo MN = N ∧ AlignedCo MN

-- ================================================================
-- Forward correspondence.
-- ================================================================

/-- Forward: a network `τ_dequeue` is matched by the monitored network. -/
theorem network_dequeue_mon_dequeue_co {N N' : Network} {MN : MonitoredNetwork}
    {r p : Role} {lab : Lab} {S : DataSort}
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (host : MNhostCo MN = N) (aligned : AlignedCo MN)
    (hTr : net_trans N (net_label.τ_dequeue r p lab S) N') :
    ∃ MN', mon_net_trans_co MN (mon_net_label.τ_dequeue r p lab S) MN' ∧
      MNhostCo MN' = N' ∧ AlignedCo MN' := by
  cases hTr with
  | @dequeue _ _ stq stq' _ _ hSQ hmem =>
    cases hSQ with
    | @dequeue T T' Q Q' _ _ _ hST hQ =>
      obtain ⟨M, hmemMN⟩ := MNhostCo_mem host hmem
      have hFold := aligned _ _ _ hmemMN
      refine ⟨MN.replace r ((T', Q'), M),
        mon_net_trans_co.lift (mon_trans_co.dequeue (sq_trans.dequeue hST hQ)) hmemMN, ?_, ?_⟩
      · rw [MNhostCo_replace, host]
      · intro r' stq' M' hmem'
        rcases MN_mem_replace_inv hmem' with hNew | ⟨hmemOld, _⟩
        · obtain ⟨rfl, hEq⟩ := hNew
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          exact SemFoldCo_dequeue (hWF.2.1 _ hmem) hFold (sq_trans.dequeue hST hQ)
        · exact aligned _ _ _ hmemOld

/-- Forward: a network `τ_comm` is matched by the monitored network. -/
theorem network_comm_mon_comm_co {N N' : Network} {MN : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort}
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (host : MNhostCo MN = N) (aligned : AlignedCo MN)
    (hTr : net_trans N (net_label.τ_comm p q lab S) N') :
    ∃ MN', mon_net_trans_co MN (mon_net_label.τ_comm p q lab S) MN' ∧
      MNhostCo MN' = N' ∧ AlignedCo MN' := by
  have inv : InvCo N := ⟨hWF, hRP, hNS, hHD, hLive⟩
  have hTr0 := hTr
  cases hTr with
  | @comm _ _ _ _ stqp stqp' stqq stqq' apart hs hr mp mq =>
    cases hs with
    | @send Tp Tp' Qp _ _ _ hST =>
      cases hr with
      | @recv Tq Qq =>
        have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by trivial
        have inv' := InvCo_step inv hInt hTr0
        have hmem_p' : (p, (Tp', Qp)) ∈
            Network.replace (Network.replace N p (Tp', Qp)) q
              (Tq, Qq ++ [QueueMessage.msg p lab S]) :=
          mem_replace_other (by simp [Network.replace]) apart
        have hmem_q' : (q, (Tq, Qq ++ [QueueMessage.msg p lab S])) ∈
            Network.replace (Network.replace N p (Tp', Qp)) q
              (Tq, Qq ++ [QueueMessage.msg p lab S]) := by
          simp [Network.replace]
        obtain ⟨Mp, hmemMp⟩ := MNhostCo_mem host mp
        obtain ⟨Mq, hmemMq⟩ := MNhostCo_mem host mq
        have hFoldp := aligned _ _ _ hmemMp
        have hFoldq := aligned _ _ _ hmemMq
        obtain ⟨Mp', hBasep, hFoldp'⟩ := SemFoldCo_send (inv.1.2.1 _ mp) hFoldp hST
          (SemFoldCo_exists_InvCo inv' hmem_p')
        have hYesSend : mon_tr_co Mp (mon_verdict.yes (ext_tag.send q lab S)) Mp' := by
          simp only [mon_tr_co]
          exact ⟨SemFoldCo_wf hFoldp, SemFoldCo_wf hFoldp',
            mon_tr_yes_max_deriv_co.base (SemFoldCo_wf hFoldp) hBasep⟩
        obtain ⟨M1q, hCompq⟩ := SemFoldCo_exists_InvCo inv' hmem_q'
        obtain ⟨Mq', hFmonq, hFoldq'⟩ := SemFoldCo_recv_accept (inv.1.2.1 _ mq) hFoldq hCompq
        have hYesRecv : mon_tr_co Mq (mon_verdict.yes (ext_tag.recv p lab S)) Mq' := by
          simp only [mon_tr_co]
          exact ⟨SemFoldCo_wf hFoldq, SemFoldCo_wf hFoldq',
            fmon_implies_mon_tr_yes_co (SemFoldCo_wf hFoldq) (SemFoldCo_wf hFoldq') hFmonq⟩
        have hSend : mon_trans_co ((Tp, Qp), Mp) (mon_label.yes_send q lab S) ((Tp', Qp), Mp') :=
          mon_trans_co.good_send (sq_trans.send hST) hYesSend
        have hRecv : mon_trans_co ((Tq, Qq), Mq) (mon_label.yes_recv p lab S)
            ((Tq, Qq ++ [.msg p lab S]), Mq') :=
          mon_trans_co.good_recv sq_trans.recv hYesRecv
        refine ⟨((MN.replace p ((Tp', Qp), Mp')).replace q ((Tq, Qq ++ [.msg p lab S]), Mq')),
          mon_net_trans_co.comm hSend hRecv hmemMp hmemMq, ?_, ?_⟩
        · rw [MNhostCo_replace, MNhostCo_replace, host]
        · intro r' stq' M' hmem'
          rcases MN_mem_replace_inv hmem' with hNew | ⟨hmemOld, hne⟩
          · obtain ⟨rfl, hEq⟩ := hNew
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
            exact hFoldq'
          · rcases MN_mem_replace_inv hmemOld with hNew' | ⟨hmemOld', hne'⟩
            · obtain ⟨rfl, hEq'⟩ := hNew'
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq'
              exact hFoldp'
            · exact aligned _ _ _ hmemOld'

-- ================================================================
-- Backward correspondence.
-- ================================================================

/-- Backward: a monitored `τ_dequeue` is matched by the network. -/
theorem mon_dequeue_network_dequeue_co {N : Network} {MN MN' : MonitoredNetwork}
    {r p : Role} {lab : Lab} {S : DataSort} {lbl : mon_net_label}
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (host : MNhostCo MN = N) (aligned : AlignedCo MN)
    (hTr : mon_net_trans_co MN lbl MN') (hEq : lbl = mon_net_label.τ_dequeue r p lab S) :
    ∃ N', net_trans N (net_label.τ_dequeue r p lab S) N' ∧
      MNhostCo MN' = N' ∧ AlignedCo MN' := by
  match hTr with
  | @mon_net_trans_co.lift _ _ mt _ _ h_der hmem =>
    cases h_der with
    | good_send _ _ => simp [mon_net_label.ofmon_label] at hEq
    | good_recv _ _ => simp [mon_net_label.ofmon_label] at hEq
    | badOut _ _ => simp [mon_net_label.ofmon_label] at hEq
    | badIn _ => simp [mon_net_label.ofmon_label] at hEq
    | @dequeue _ _ M _ _ _ hSQ =>
      simp only [mon_net_label.ofmon_label] at hEq
      rcases hEq with ⟨rfl, rfl, rfl, rfl⟩
      cases hSQ with
      | @dequeue T T' Q Q' _ _ _ hST hQ =>
        have hmemH : (r, (T, Q)) ∈ MNhostCo MN := List.mem_map.mpr ⟨_, hmem, rfl⟩
        have hmemN : (r, (T, Q)) ∈ N := host ▸ hmemH
        have hFold := aligned _ _ _ hmem
        refine ⟨N.replace r (T', Q'), net_trans.dequeue (sq_trans.dequeue hST hQ) hmemN, ?_, ?_⟩
        · rw [MNhostCo_replace, host]
        · intro r' stq' M' hmem'
          rcases MN_mem_replace_inv hmem' with hNew | ⟨hmemOld, _⟩
          · obtain ⟨rfl, hEqM⟩ := hNew
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqM
            exact SemFoldCo_dequeue (hWF.2.1 _ hmemN) hFold (sq_trans.dequeue hST hQ)
          · exact aligned _ _ _ hmemOld
  | mon_net_trans_co.comm _ _ _ _ =>
    cases hEq

/-- Backward: a monitored `τ_comm` is matched by the network. -/
theorem mon_comm_network_comm_co {N : Network} {MN MN' : MonitoredNetwork}
    {p q : Role} {lab : Lab} {S : DataSort} {lbl : mon_net_label}
    (hWF : N.WellFormed) (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (hHD : IsHalfDuplex N) (hLive : IsOutputLiveNetwork N)
    (host : MNhostCo MN = N) (aligned : AlignedCo MN)
    (hTr : mon_net_trans_co MN lbl MN') (hEq : lbl = mon_net_label.τ_comm p q lab S) :
    ∃ N', net_trans N (net_label.τ_comm p q lab S) N' ∧
      MNhostCo MN' = N' ∧ AlignedCo MN' := by
  have inv : InvCo N := ⟨hWF, hRP, hNS, hHD, hLive⟩
  match hTr with
  | mon_net_trans_co.comm h_send h_recv hmem_p hmem_q =>
    cases h_send with
    | @good_send _ _ Mp Mp' _ _ _ hSQ_send hYes_send =>
      cases h_recv with
      | @good_recv _ _ Mq Mq' _ _ _ hSQ_recv hYes_recv =>
        cases hSQ_send with
        | @send Tp Tp' Qp _ _ _ hST_send =>
          cases hSQ_recv with
          | @recv Tq Qq =>
            cases hEq
            have hmemH_p : (p, (Tp, Qp)) ∈ MNhostCo MN := List.mem_map.mpr ⟨_, hmem_p, rfl⟩
            have hmemH_q : (q, (Tq, Qq)) ∈ MNhostCo MN := List.mem_map.mpr ⟨_, hmem_q, rfl⟩
            have hmem_p_N : (p, (Tp, Qp)) ∈ N := host ▸ hmemH_p
            have hmem_q_N : (q, (Tq, Qq)) ∈ N := host ▸ hmemH_q
            have hFoldp := aligned _ _ _ hmem_p
            have hFoldq := aligned _ _ _ hmem_q
            have hne : p ≠ q :=
              out_ne_self_of_noSelf (inv.2.2.1 _ _ _ hmem_p_N) hST_send
            have hStep : net_trans N (net_label.τ_comm p q lab S)
                ((N.replace p (Tp', Qp)).replace q (Tq, Qq ++ [.msg p lab S])) :=
              net_trans.comm hne (sq_trans.send hST_send) sq_trans.recv hmem_p_N hmem_q_N
            have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by trivial
            have inv' := InvCo_step inv hInt hStep
            have hmem_p'' : (p, (Tp', Qp)) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) :=
              mem_replace_other (by simp [Network.replace]) hne
            have hmem_q'' : (q, (Tq, Qq ++ [QueueMessage.msg p lab S])) ∈
                Network.replace (Network.replace N p (Tp', Qp)) q
                  (Tq, Qq ++ [QueueMessage.msg p lab S]) := by
              simp [Network.replace]
            -- The observed co-steps furnish `Prune` derivations; `fmon_exists`
            -- turns the induced `Ex` into `fmon` derivations for *some*
            -- residuals, and `Prune_unique` + `SemFoldCo_eqv_tgt` identify
            -- them (up to `Eqv`) with the observed targets — no computation.
            have hCop : ∃ hT hV, mon_tr_yes_co Mp (ext_tag.send q lab S) Mp' hT hV := by
              simpa [mon_tr_co] using hYes_send
            obtain ⟨hTp, hVp, hcop⟩ := hCop
            have hPrunep : Prune (ext_tag.send q lab S) Mp Mp' := co_implies_Prune hTp hVp hcop
            obtain ⟨Vp, hFmonp⟩ := fmon_exists hTp (Ex_of_Prune hTp hPrunep)
            have hFoldVp : SemFoldCo Tp' Qp Vp :=
              SemFoldCo_send_any (inv.1.2.1 _ hmem_p_N) hFoldp hST_send
                (SemFoldCo_exists_InvCo inv' hmem_p'') hFmonp
            have hFoldp'' : SemFoldCo Tp' Qp Mp' :=
              SemFoldCo_eqv_tgt hFoldVp (Prune_unique hTp (fmon_spec hTp hFmonp) hPrunep) hVp
            have hCoq : ∃ hT hV, mon_tr_yes_co Mq (ext_tag.recv p lab S) Mq' hT hV := by
              simpa [mon_tr_co] using hYes_recv
            obtain ⟨hTq, hVq, hcoq⟩ := hCoq
            have hPruneq : Prune (ext_tag.recv p lab S) Mq Mq' := co_implies_Prune hTq hVq hcoq
            obtain ⟨Vq, hFmonq⟩ := fmon_exists hTq (Ex_of_Prune hTq hPruneq)
            have hFoldVq : SemFoldCo Tq (Qq ++ [.msg p lab S]) Vq :=
              SemFoldCo_recv_any (inv.1.2.1 _ hmem_q_N) hFoldq hFmonq
            have hFoldq'' : SemFoldCo Tq (Qq ++ [.msg p lab S]) Mq' :=
              SemFoldCo_eqv_tgt hFoldVq (Prune_unique hTq (fmon_spec hTq hFmonq) hPruneq) hVq
            refine ⟨_, hStep, ?_, ?_⟩
            · rw [MNhostCo_replace, MNhostCo_replace, host]
            · intro r' stq' M' hmem'
              rcases MN_mem_replace_inv hmem' with hNew | ⟨hmemOld, hne'⟩
              · obtain ⟨rfl, hEqM⟩ := hNew
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqM
                exact hFoldq''
              · rcases MN_mem_replace_inv hmemOld with hNew' | ⟨hmemOld', hne''⟩
                · obtain ⟨rfl, hEqM'⟩ := hNew'
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqM'
                  exact hFoldp''
                · exact aligned _ _ _ hmemOld'
  | mon_net_trans_co.lift h_der hmem =>
    cases h_der with
    | good_send _ _ => simp [mon_net_label.ofmon_label] at hEq
    | good_recv _ _ => simp [mon_net_label.ofmon_label] at hEq
    | badOut _ _ => simp [mon_net_label.ofmon_label] at hEq
    | badIn _ => simp [mon_net_label.ofmon_label] at hEq
    | dequeue _ => simp [mon_net_label.ofmon_label] at hEq

-- ================================================================
-- Main theorem.
-- ================================================================

/-- Coinductive monitor soundness: a well-formed, roles-present, no-self,
    half-duplex, output-live network is internally bisimilar (coinductively)
    to its consistent instrumentation. -/
theorem monitor_soundness_co {N : Network} {MN : MonitoredNetwork}
    (hwf : N.WellFormed)
    (hNS : N.NoSelf)
    (hRP : N.RolesPresent)
    (h_output_live : IsOutputLiveNetwork N)
    (h_half_duplex : IsHalfDuplex N)
    (hCons : consistentInstrumentation_co N = some MN) :
    InternallyBisimilarCo N MN := by
  have inv0 : InvCo N := ⟨hwf, hRP, hNS, h_half_duplex, h_output_live⟩
  have host0 : MNhostCo MN = N := MNhostCo_of_consistent hCons
  have align0 : AlignedCo MN := by
    intro r stq M hmem
    obtain ⟨hmemN, hFold⟩ := consistentInstrumentation_inv_mem_co hmem hCons
    exact fold_co_to_SemFoldCo (hwf.2.1 _ hmemN) (monitor_fold_val_partial_co_sound hFold)
  refine ⟨R, ⟨inv0, host0, align0⟩, ?_⟩
  rintro N' MN' ⟨inv', host', aligned'⟩ μ₁ hIntLbl₁
  obtain ⟨hWF', hRP', hNS', hHD', hLive'⟩ := inv'
  have inv' : InvCo N' := ⟨hWF', hRP', hNS', hHD', hLive'⟩
  constructor
  · intro N'' hTr
    cases μ₁ with
    | io_send _ _ _ _ => exfalso; exact hIntLbl₁
    | io_recv _ _ _ _ => exfalso; exact hIntLbl₁
    | τ_dequeue r p lab S =>
      obtain ⟨MN'', hStep, hHost'', hAlign''⟩ :=
        network_dequeue_mon_dequeue_co hWF' hRP' hNS' hHD' hLive' host' aligned' hTr
      exact ⟨MN'', mon_net_label.τ_dequeue r p lab S,
        by simp [is_internal_mon_net_label], rfl, hStep,
        ⟨InvCo_step inv' hIntLbl₁ hTr, hHost'', hAlign''⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨MN'', hStep, hHost'', hAlign''⟩ :=
        network_comm_mon_comm_co hWF' hRP' hNS' hHD' hLive' host' aligned' hTr
      exact ⟨MN'', mon_net_label.τ_comm p q lab S,
        by simp [is_internal_mon_net_label], rfl, hStep,
        ⟨InvCo_step inv' hIntLbl₁ hTr, hHost'', hAlign''⟩⟩
  · intro MN'' μ₂ hIntLbl₂ hTr
    cases μ₂ with
    | io_yes_send _ _ _ _ => exfalso; exact hIntLbl₂
    | io_yes_recv _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_out _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_inp _ _ _ _ => exfalso; exact hIntLbl₂
    | τ_dequeue r p lab S =>
      obtain ⟨N'', hStep, hHost'', hAlign''⟩ :=
        mon_dequeue_network_dequeue_co hWF' hRP' hNS' hHD' hLive' host' aligned' hTr rfl
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by
        simp [is_internal_net_label]
      exact ⟨N'', net_label.τ_dequeue r p lab S, hInt, rfl, hStep,
        ⟨InvCo_step inv' hInt hStep, hHost'', hAlign''⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨N'', hStep, hHost'', hAlign''⟩ :=
        mon_comm_network_comm_co hWF' hRP' hNS' hHD' hLive' host' aligned' hTr rfl
      have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
        simp [is_internal_net_label]
      exact ⟨N'', net_label.τ_comm p q lab S, hInt, rfl, hStep,
        ⟨InvCo_step inv' hInt hStep, hHost'', hAlign''⟩⟩
