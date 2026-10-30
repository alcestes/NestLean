import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.NoRec.DrainSurvival
import Nest.NoRec.NoRecEncoder

/-!
# DrainAccept: NoRec draining implies monitor acceptance.

Draining implies monitor acceptance, first for vacuous recursion
(`drain_implies_mon_exists_accepts_vacuous`: per-step fuel is `tRecCount`
with adequacy from `of_vacuous_everywhere`; the head prunes via vacuous
drain survival to a yes-transition, successors preserve `VacuousRec` and
`WellFormed`, the tail folds by the IH), then for `NoRec` via the
`VacuousRec.of_NoRec` bridge (`drain_implies_mon_exists_accepts_norec`).
Feeds `DeepComplement`'s reject-implies-nodrain direction.
-/

section DrainAccept

/-- Draining implies monitor acceptance (vacuous recursion): a well-formed,
    vacuous drain of `Q` folds to a monitor accepting `Q`. By queue
    induction: per-step fuel is `tRecCount` with adequacy from
    `of_vacuous_everywhere` (no separate `Has`-existence hypothesis is
    needed — vacuous `tRec`s unfold unconditionally); the head prunes
    (vacuous drain survival) to a yes-transition (via
    `mon_yes_prune_deep_mp`); successors preserve `VacuousRec` and
    `WellFormed`; the tail folds by the IH. -/
theorem drain_implies_mon_exists_accepts_vacuous (T : SessionType) (Q : Queue)
    (hVac : T.VacuousRec) (hWF : T.WellFormed)
    (hDeep : CanAlwaysDrainInternalDeep T Q) :
    ∃ M : SessionType, monitor_fold (T, Q) M := by
  induction Q generalizing T with
  | nil =>
    exact ⟨T, rfl⟩
  | cons msg Q' ih =>
    obtain ⟨p, lab, S⟩ := msg
    have hAd : PruneAdequate p lab S (SessionType.tRecCount T) T :=
      PruneAdequate.of_vacuous_everywhere p lab S hWF hVac
    obtain ⟨hHas, hDeep'⟩ := drain_survives_deep_pruning_aux_vacuous p lab S
      (SessionType.tRecCount T) (sizeOf T) T Q' (Nat.le_refl _) hVac
      hWF hAd hDeep
    have hPr : pruneFirstInputDeep T (QueueMessage.msg p lab S)
        (SessionType.tRecCount T) =
        some (pruneFirstInputDeepGo p lab S (SessionType.tRecCount T) T) := by
      simp [pruneFirstInputDeep, hHas]
    have hMP : mon_tr_yes T (ext_tag.recv p lab S)
        (pruneFirstInputDeepGo p lab S (SessionType.tRecCount T) T) :=
      mon_yes_prune_deep_mp p lab S (SessionType.tRecCount T) (sizeOf T) T _
        hVac (Nat.le_refl _) hAd hWF hPr
    have hVac' : (pruneFirstInputDeepGo p lab S
        (SessionType.tRecCount T) T).VacuousRec :=
      prune_first_input_deep_go_preserves_vacuous_rec p lab S
        (SessionType.tRecCount T) (sizeOf T) T (Nat.le_refl _) hAd hVac
    have hWF' : (pruneFirstInputDeepGo p lab S
        (SessionType.tRecCount T) T).WellFormed :=
      mon_tr_yes_preserves_wf hMP hWF
    obtain ⟨M, hM⟩ := ih (pruneFirstInputDeepGo p lab S
      (SessionType.tRecCount T) T) hVac' hWF' hDeep'
    refine ⟨M, ?_⟩
    show monitor_fold_aux (QueueMessage.msg p lab S :: Q') T M
    exact ⟨_, hMP, hM⟩

/-- Draining implies monitor acceptance: a well-formed `NoRec` drain of `Q`
    folds to a monitor accepting `Q`. Delegates to the vacuous assembly
    via the `NoRec` bridge. -/
theorem drain_implies_mon_exists_accepts_norec (T : SessionType) (Q : Queue)
    (hNR : T.NoRec) (hWF : T.WellFormed)
    (hDeep : CanAlwaysDrainInternalDeep T Q) :
    ∃ M : SessionType, monitor_fold (T, Q) M :=
  drain_implies_mon_exists_accepts_vacuous T Q
    (SessionType.VacuousRec.of_NoRec hNR) hWF hDeep

end DrainAccept
