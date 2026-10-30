import Nest.MonitorCo
import Nest.MonitorLTS
import Nest.NetworkLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorLTSCo: coinductive monitored stack (relational).

Coinductive twin of the monitored session-type / network LTS
(`Nest/MonitorLTS.lean`, monitored stack): `mon_tr_co` uses `mon_tr_yes_co` on the
yes-branch and keeps finite `mon_tr_no` on the no-branch. The `good` rules
carry only the session step and the coinductive yes-step — no computed
equation: the correspondence proceeds relationally.
-/

/-- Combined yes/no LTS for coinductive monitor states. The yes-branch uses
    `mon_tr_yes_co` (which already carries source and target well-formedness);
    the no-branch keeps the finite `mon_tr_no`. -/
def mon_tr_co (T : SessionType) (ℓ : mon_verdict) (T' : SessionType) : Prop :=
  match ℓ with
  | mon_verdict.yes γ => ∃ hT hV, mon_tr_yes_co T γ T' hT hV
  | mon_verdict.no γ => mon_tr_no T γ T'

/-- LTS for coinductive monitored session types. The `good` rules carry only
    the session step and the coinductive yes-step (no computed equation). -/
inductive mon_trans_co : MonitoredSessionType → mon_label → MonitoredSessionType → Prop where
  | good_send {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.send p lab S) stq')
      (hYes : mon_tr_co M (mon_verdict.yes (ext_tag.send p lab S)) M') :
    mon_trans_co (stq, M) (mon_label.yes_send p lab S) (stq', M')
  | good_recv {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.recv p lab S) stq')
      (hYes : mon_tr_co M (mon_verdict.yes (ext_tag.recv p lab S)) M') :
    mon_trans_co (stq, M) (mon_label.yes_recv p lab S) (stq', M')
  | badOut {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.send p lab S) stq')
      (hMon : mon_tr_co M (mon_verdict.no (ext_tag.send p lab S)) M') :
    mon_trans_co (stq, M) (mon_label.no_out p lab S) (stq', M')
  | badIn {stq : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hMon : mon_tr_co M (mon_verdict.no (ext_tag.recv p lab S)) M') :
    mon_trans_co (stq, M) (mon_label.no_inp p lab S) (stq, M')
  | dequeue {stq stq' : SessionTypeWithQueue} {M : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.dequeue p lab S) stq') :
    mon_trans_co (stq, M) (mon_label.silent p lab S) (stq', M)

/-- LTS for coinductive monitored networks (flat-list representation).
    The par-left/par-right rules are eliminated, as in `mon_net_trans`. -/
inductive mon_net_trans_co : MonitoredNetwork → mon_net_label → MonitoredNetwork → Prop where
  | lift {r : Role} {mt mt' : MonitoredSessionType} {ℓ : mon_label}
      (h : mon_trans_co mt ℓ mt')
      (hmem : (r, mt) ∈ MN) :
    mon_net_trans_co MN (mon_net_label.ofmon_label r ℓ) (MonitoredNetwork.replace MN r mt')
  | comm {p q : Role} {lab : Lab} {S : DataSort}
      {mtp mtp' : MonitoredSessionType} {mtq mtq' : MonitoredSessionType}
      (h_send : mon_trans_co mtp (mon_label.yes_send q lab S) mtp')
      (h_recv : mon_trans_co mtq (mon_label.yes_recv p lab S) mtq')
      (hmem_p : (p, mtp) ∈ MN)
      (hmem_q : (q, mtq) ∈ MN) :
    mon_net_trans_co MN (mon_net_label.τ_comm p q lab S)
      ((MN.replace p mtp').replace q mtq')

/-- The coinductive monitored-network LTS. -/
def mnetLTS_co : LTS MonitoredNetwork mon_net_label := LTS.mk mon_net_trans_co

/-- Monitor state for a coinductive session type with queue: folding the queue
    into the session type with `mon_tr_yes_co` steps. -/
def monitor_fold_aux_co : Queue → SessionType → SessionType → Prop
  | .nil, T, T' => T' = T
  | .cons (QueueMessage.msg p lab S) rest, T, T' =>
    ∃ (T_mid : SessionType) (hT : T.WellFormed) (hM : T_mid.WellFormed),
      mon_tr_yes_co T (ext_tag.recv p lab S) T_mid hT hM ∧
      monitor_fold_aux_co rest T_mid T'

/-- Monitor acceptance for a queued session type under the coinductive relation. -/
def monitor_fold_co (stq : SessionTypeWithQueue) (T' : SessionType) : Prop :=
  monitor_fold_aux_co stq.2 stq.1 T'

/-- `Option` version of the coinductive queue fold. -/
noncomputable def monitor_fold_val_partial_co (stq : SessionTypeWithQueue) : Option SessionType := by
  classical
  if h : ∃ T', monitor_fold_co stq T' then
    exact some h.choose
  else
    exact none

/-- Consistent instrumentation, relational (`Co` twin).
    Each entry folds its queue with the relational coinductive fold
    (`monitor_fold_val_partial_co`); no computed function is involved. -/
noncomputable def consistentInstrumentation_co : Network → Option MonitoredNetwork
  | [] => some []
  | (r, stq) :: rest =>
    match monitor_fold_val_partial_co stq, consistentInstrumentation_co rest with
    | some M, some MN => some ((r, (stq, M)) :: MN)
    | _, _ => none

/-- A network is co-monitorable when it has a defined consistent
    instrumentation whose every monitor is co-monitorable (finite-state).
    This is the network-level counterpart of `MonitorableCo`
    (`Nest/MonitorCo.lean`), mirroring `Network.Monitorable`
    (`Nest/MonitorSoundness.lean`). -/
def Network.MonitorableCo (N : Network) : Prop :=
  ∃ MN : MonitoredNetwork, consistentInstrumentation_co N = some MN ∧
    ∀ x ∈ MN, _root_.MonitorableCo x.2.2
