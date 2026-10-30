import Nest.NoRec.NoRecToolkit

/-!
# VacuousRec: Vacuous-recursion toolkit: the NoRec-tolerant recursion discipline.

VacuousRec inductive, its preservation/termination mirrors, and the `of_NoRec`
bridge feeding the vacuous drain-acceptance assembly.
-/

/-!
# Vacuous-recursion toolkit.

Inductive + preservation/termination chain, used only inside `Nest.NoRec`.
-/

/-- Vacuous recursion everywhere: every `tRec X B` binds a variable not free
    in its body (unfolding deletes the binder, grafting no copies). -/
inductive SessionType.VacuousRec : SessionType → Prop where
  | end : VacuousRec SessionType.tEnd
  | tvar (X : String) : VacuousRec (SessionType.tVar X)
  | internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Role × Lab × DataSort × SessionType),
        x ∈ branches → VacuousRec x.2.2.2) :
    VacuousRec (SessionType.internalChoice branches)
  | externalChoice {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Lab × DataSort × SessionType),
        x ∈ branches → VacuousRec x.2.2) :
    VacuousRec (SessionType.externalChoice r branches)
  | trec {X : String} {B : SessionType} (hfree : X ∉ B.fv)
      (hbody : VacuousRec B) :
    VacuousRec (SessionType.tRec X B)

/-- A network is vacuous when every entry's session type is vacuous
    (`VacuousRec`): binders unused everywhere. Threading hypothesis for
    the vacuous soundness chain (replaces `Network.NoRec`; unfolding is
    a no-op on bodies, so `tRec` arms recurse via `of_tRecBody` instead
    of absurdity). -/
def Network.VacuousRec (N : Network) : Prop :=
  ∀ (x : Role × SessionTypeWithQueue), x ∈ N → x.2.1.VacuousRec

/-- Vacuousness of an internal-choice branch target. -/
lemma SessionType.VacuousRec.of_internalChoice
    {branches : List (Role × Lab × DataSort × SessionType)}
    (h : VacuousRec (SessionType.internalChoice branches))
    {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    VacuousRec x.2.2.2 := by
  cases h with
  | internalChoice h_branches => exact h_branches x hmem

/-- Vacuousness of an external-choice branch target. -/
lemma SessionType.VacuousRec.of_externalChoice
    {r : Role} {branches : List (Lab × DataSort × SessionType)}
    (h : VacuousRec (SessionType.externalChoice r branches))
    {x : Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    VacuousRec x.2.2 := by
  cases h with
  | externalChoice h_branches => exact h_branches x hmem

/-- Recursion-free types are vacuously recursive (no binders at all). -/
lemma SessionType.VacuousRec.of_NoRec {T : SessionType} (h : T.NoRec) :
    T.VacuousRec := by
  induction h
  · exact SessionType.VacuousRec.end
  · rename_i X
    exact SessionType.VacuousRec.tvar X
  · rename_i h_branches ih
    exact SessionType.VacuousRec.internalChoice (fun x hx => ih x hx)
  · rename_i h_branches ih
    exact SessionType.VacuousRec.externalChoice (fun x hx => ih x hx)

/-- `st_trans` steps preserve `VacuousRec` (induction: branch targets via
    member inversions; `tRec` recurses into the body, unfolding being a
    no-op by freeness). -/
lemma st_trans_preserves_vac {T T' : SessionType} {α : st_label}
    (hST : st_trans T α T') (hVac : T.VacuousRec) : T'.VacuousRec := by
  revert hVac
  induction hST with
  | intC hmem => intro hVac; exact SessionType.VacuousRec.of_internalChoice hVac hmem
  | extC hmem => intro hVac; exact SessionType.VacuousRec.of_externalChoice hVac hmem
  | @tRec X T T' α h ih =>
    intro hVac
    cases hVac with
    | trec hfree hVacB =>
      have hSn : substSessionType T X (SessionType.tRec X T) = T :=
        subst_noop T X (SessionType.tRec X T) hfree
      have hVacS : (substSessionType T X (SessionType.tRec X T)).VacuousRec := by
        rw [hSn]
        exact hVacB
      exact ih hVacS

/-- `sq_trans` steps preserve vacuousness of the session component
    (`recv` keeps the session). -/
lemma sq_trans_preserves_vac {stq stq' : SessionTypeWithQueue} {a : sq_action}
    (h : sq_trans stq a stq') (hVac : stq.1.VacuousRec) : stq'.1.VacuousRec := by
  cases h with
  | send hST => exact st_trans_preserves_vac hST hVac
  | dequeue hST hQ => exact st_trans_preserves_vac hST hVac
  | recv => exact hVac

/-- Membership transport for vacuous entries (mirror `no_rec_replace` in
    `Nest.NoRec.NoRecToolkit`). -/
private lemma vacuous_rec_replace {N : Network} {r : Role}
    {stq : SessionTypeWithQueue}
    (hVac : N.VacuousRec) (hNew : stq.1.VacuousRec) :
    (Network.replace N r stq).VacuousRec := by
  intro x hx
  unfold Network.replace at hx
  simp only [List.mem_cons, List.mem_filter] at hx
  rcases hx with rfl | ⟨hxN, -⟩
  · exact hNew
  · exact hVac x hxN

/-- `net_trans` steps preserve vacuous networks (per-arm session preservation +
    replace transport; receiver sessions are unchanged). -/
lemma net_trans_preserves_vac {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hVac : N.VacuousRec) : N'.VacuousRec := by
  cases hTr with
  | io_send hSQ hmem =>
    exact vacuous_rec_replace hVac (sq_trans_preserves_vac hSQ (hVac _ hmem))
  | io_recv hSQ hmem =>
    exact vacuous_rec_replace hVac (sq_trans_preserves_vac hSQ (hVac _ hmem))
  | dequeue hSQ hmem =>
    exact vacuous_rec_replace hVac (sq_trans_preserves_vac hSQ (hVac _ hmem))
  | comm _hne h_send h_recv hmem_p hmem_q =>
    cases h_recv with
    | recv =>
      exact vacuous_rec_replace (vacuous_rec_replace hVac
        (sq_trans_preserves_vac h_send (hVac _ hmem_p))) (hVac _ hmem_q)

/-- Vacuous networks persist along τ-stars. -/
lemma net_trans_star_preserves_vac {N N' : Network}
    (hStar : net_trans_star N N') (hVac : N.VacuousRec) : N'.VacuousRec := by
  revert hVac
  induction hStar with
  | refl =>
    intro hVac
    exact hVac
  | step hInt hTr _ ih =>
    intro hVac
    exact ih (net_trans_preserves_vac hTr hVac)

/-- `st_trans` steps shrink vacuous sessions (induction: branch targets are
    strict subterms; `tRec` descends through the no-op unfold, which is
    strictly smaller). Fails for used binders (`subst` can grow). -/
lemma st_trans_size_lt_of_vac {T T' : SessionType} {α : st_label}
    (hST : st_trans T α T') (hVac : T.VacuousRec) : sizeOf T' < sizeOf T := by
  revert hVac
  induction hST with
  | intC hmem => intro _; exact sizeOf_SessionType_lt_sizeOf_internalChoice hmem
  | extC hmem => intro _; exact sizeOf_SessionType_lt_sizeOf_externalChoice hmem
  | @tRec X T T' α h ih =>
    intro hVac
    cases hVac with
    | trec hfree hVacB =>
      have hSn : substSessionType T X (SessionType.tRec X T) = T :=
        subst_noop T X (SessionType.tRec X T) hfree
      have hVacS : (substSessionType T X (SessionType.tRec X T)).VacuousRec := by
        rw [hSn]
        exact hVacB
      have h1 : sizeOf T' < sizeOf (substSessionType T X (SessionType.tRec X T)) :=
        ih hVacS
      have h2 : sizeOf (substSessionType T X (SessionType.tRec X T)) <
          sizeOf (SessionType.tRec X T) := by
        rw [hSn]
        simp
      omega

/-- Budget strictly decreases along internal steps of vacuous
    well-formed networks (mirror `budget_step_norec`; unfoldings shrink
    by no-op; queues are uncounted so `recv` extension is free). Fails
    for used binders (subst-grown targets can exceed the budget). -/
lemma budget_step_vac {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ)
    (hVac : N.VacuousRec) (hWF : N.WellFormed) :
    networkBudget N' < networkBudget N := by
  cases hTr with
  | io_send _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ => simp [is_internal_net_label] at hInt
  | @dequeue r p stq stq' lab S hSQ hmem =>
    obtain ⟨T, Q⟩ := stq
    obtain ⟨T', Q'⟩ := stq'
    cases hSQ with
    | dequeue hST hQ =>
      have hTVac := hVac _ hmem
      have hlt : sizeOf T' < sizeOf T := st_trans_size_lt_of_vac hST hTVac
      have heq : networkBudget (Network.replace N r (T', Q')) + sizeOf T =
          networkBudget N + sizeOf T' :=
        budget_replace_eq N r (T, Q) (T', Q') hmem hWF.1
      unfold networkBudget at heq ⊢
      omega
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    obtain ⟨Tp, Qp⟩ := stqp
    obtain ⟨Tp', Qp'⟩ := stqp'
    obtain ⟨Tq, Qq⟩ := stqq
    cases h_send with
    | send hST =>
      cases h_recv with
      | recv =>
        have hTVac := hVac _ hmem_p
        have hltS : sizeOf Tp' < sizeOf Tp := st_trans_size_lt_of_vac hST hTVac
        have heq1 : networkBudget (Network.replace N p (Tp', Qp)) + sizeOf Tp =
            networkBudget N + sizeOf Tp' :=
          budget_replace_eq N p (Tp, Qp) (Tp', Qp) hmem_p hWF.1
        have hmem_q' : (q, (Tq, Qq)) ∈ Network.replace N p (Tp', Qp) :=
          mem_replace_other hmem_q (Ne.symm hne)
        have heq2 : networkBudget (Network.replace (Network.replace N p (Tp', Qp))
              q (Tq, Qq ++ [QueueMessage.msg p lab S])) + sizeOf Tq =
            networkBudget (Network.replace N p (Tp', Qp)) + sizeOf Tq :=
          budget_replace_eq _ q (Tq, Qq) (Tq, Qq ++ [QueueMessage.msg p lab S])
            hmem_q' (nodup_replace_roles hWF.1)
        unfold networkBudget at heq1 heq2 ⊢
        omega

/-- Every vacuous well-formed network reaches a stuck configuration
    (same budget induction; unfold-loops terminate by no-op shrink).
    False for used binders in general (observable cycles can persist
    forever — no stuck state need be reachable). -/
lemma exists_stuck_reachable_vac {Ni : Network}
    (hVac : Ni.VacuousRec) (hWF : Ni.WellFormed) :
    ∃ N', net_trans_star Ni N' ∧ IsStuckNetwork N' := by
  suffices key : ∀ (n : ℕ) (N : Network), N.VacuousRec → N.WellFormed →
      networkBudget N ≤ n → ∃ N', net_trans_star N N' ∧ IsStuckNetwork N' from
    key _ _ hVac hWF (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro N hVac hWF hle
    by_cases hst : IsStuckNetwork N
    · exact ⟨N, net_trans_star.refl N, hst⟩
    · exfalso
      obtain ⟨δ, N2, hInt, hTr⟩ := stuckStep_of_notStuck hst
      have hlt := budget_step_vac hTr hInt hVac hWF
      omega
  | succ n ih =>
    intro N hVac hWF hle
    by_cases hst : IsStuckNetwork N
    · exact ⟨N, net_trans_star.refl N, hst⟩
    · obtain ⟨δ, N2, hInt, hTr⟩ := stuckStep_of_notStuck hst
      have hlt := budget_step_vac hTr hInt hVac hWF
      obtain ⟨N', hStar', hStuck'⟩ := ih N2 (net_trans_preserves_vac hTr hVac)
        (Network.wellFormedPreserved _ _ _ hWF hTr hInt) (by omega)
      exact ⟨N', net_trans_star.step hInt hTr hStar', hStuck'⟩

/-- No infinite internal paths from vacuous well-formed networks
    (budget strictly decreases each step; counting contradiction). -/
lemma noInfiniteInternalPath_of_Vac {Ni : Network}
    (hVac : Ni.VacuousRec) (hWF : Ni.WellFormed) :
    ¬ ∃ path : InfiniteNetworkPath, path.seq 0 = Ni := by
  rintro ⟨path, h0⟩
  have hdec : ∀ i, networkBudget (path.seq (i + 1)) < networkBudget (path.seq i) := by
    intro i
    have hTr := path.δ_tr i
    obtain ⟨r, p, lab, S, h | h⟩ := path.δ_form i
    · rw [h] at hTr
      have hstar := path_star_reachable_of path Ni h0 i
      exact budget_step_vac hTr (by trivial)
        (net_trans_star_preserves_vac hstar hVac)
        (net_trans_preserves_well_formed hWF hstar)
    · rw [h] at hTr
      have hstar := path_star_reachable_of path Ni h0 i
      exact budget_step_vac hTr (by trivial)
        (net_trans_star_preserves_vac hstar hVac)
        (net_trans_preserves_well_formed hWF hstar)
  have hbound : ∀ n, networkBudget (path.seq n) + n ≤ networkBudget Ni := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have h := hdec k
      omega
  have hcon := hbound (networkBudget Ni + 1)
  omega

/-- Persistent queue membership refutes liveness over vacuous networks
    (verbatim mirror; only the two preservation calls change). -/
theorem msg_always_present_imples_not_output_live_vac {N N' : Network} {q : Role}
    {m : QueueMessage} {T' : SessionType} {Q' : Queue}
    (hVac : N.VacuousRec) (hWF : N.WellFormed)
    (hStar : net_trans_star N N')
    (hMem : (q, (T', Q')) ∈ N')
    (hPersist : ∀ N'' T'' Q'', net_trans_star N' N'' → (q, (T'', Q'')) ∈ N'' → QueueMem m Q'') :
    ¬ IsOutputLiveNetwork N := by
  intro hLive
  have hVac' : N'.VacuousRec := net_trans_star_preserves_vac hStar hVac
  have hWF' : N'.WellFormed := net_trans_preserves_well_formed hWF hStar
  obtain ⟨N'', hStar', hStuck''⟩ := exists_stuck_reachable_vac hVac' hWF'
  obtain ⟨⟨T'', Q''⟩, hmem''⟩ := net_trans_role_preserved hStar' q (T', Q') hMem
  have hMemQ : QueueMem m Q'' := hPersist N'' T'' Q'' hStar' hmem''
  revert hmem'' hMemQ
  cases Q'' with
  | nil =>
    intro hmem'' hMemQ
    cases hMemQ
  | cons hd tl =>
    intro hmem'' _
    obtain ⟨p0, lab0, S0⟩ := hd
    have hDeq : Queue.dequeue (QueueMessage.msg p0 lab0 S0 :: tl)
        (QueueMessage.msg p0 lab0 S0) = some tl := by
      simp [Queue.dequeue, Queue.dequeue.go]
    have hNoOrph : ¬ NoOrphanMessages N'' := by
      intro hNo
      exact hNo q T'' _ p0 lab0 S0 tl hmem'' hDeq
    exact hNoOrph (hLive.2 N'' (net_trans_star.trans hStar hStar') hStuck'')


/-- Adequate types are vacuous: size induction — head vacuousness by
    regress (contrapositive), which unblocks body derivations via a
    `subst_noop` rewrite for structural descent (branch targets via
    `hall`; `WellFormed` pieces via inversions). With
    `of_vacuous_everywhere`, vacuousness is necessary and sufficient
    for adequacy (modulo `WellFormed`/`IsBalancedW` on the sufficiency side). -/
theorem PruneAdequate.vacuousRec_of_adequate (p : Role) (lab : Lab)
    (S : DataSort) {T : SessionType} {f : Nat} (hWF : T.WellFormed)
    (hAd : PruneAdequate p lab S f T) : T.VacuousRec := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun U => U.WellFormed →
    ∀ (f : Nat) (hAd : PruneAdequate p lab S f U), U.VacuousRec
  have hC : ∀ U, C U := by
    intro U
    refine hwf.induction (α := SessionType) (C := C) (a := U) ?step
    intro U ih hWF f hAd
    cases U with
    | tEnd => exact SessionType.VacuousRec.end
    | tVar X => exact SessionType.VacuousRec.tvar X
    | internalChoice branches =>
      apply SessionType.VacuousRec.internalChoice
      intro x hx
      rcases x with ⟨q0, l0, s0, T0⟩
      have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hx
      obtain ⟨hND, hCl, hCo⟩ := hWF
      have hWFT0 : T0.WellFormed :=
        ⟨noDupl_of_mem_intBranches hND hx,
          isClosed_of_mem_intBranches hCl hx,
          isContractive_of_mem_intBranches hCo hx⟩
      have hAdT0 : PruneAdequate p lab S f T0 := by
        cases hAd with
        | intC hall => exact hall _ hx
      exact ih T0 hlt hWFT0 f hAdT0
    | externalChoice q branches =>
      apply SessionType.VacuousRec.externalChoice
      intro x hx
      rcases x with ⟨l0, s0, T0⟩
      have hlt : sizeOf T0 < sizeOf (SessionType.externalChoice q branches) :=
        sizeOf_SessionType_lt_sizeOf_externalChoice (p := q) hx
      obtain ⟨hND, hCl, hCo⟩ := hWF
      have hWFT0 : T0.WellFormed :=
        ⟨noDupl_of_mem_extBranches hND hx,
          isClosed_of_mem_extBranches hCl hx,
          isContractive_of_mem_extBranches hCo hx⟩
      have hAdT0 : PruneAdequate p lab S f T0 := by
        cases hAd with
        | extC hall => exact hall _ hx
      exact ih T0 hlt hWFT0 f hAdT0
    | tRec X B =>
      have hfree : X ∉ B.fv := by
        intro hmem
        exact trec_head_no_adequate p lab S B X hmem hWF.2.1 f hAd
      have hNDB : B.NoDupl := by cases hWF.1 with | tRec h => exact h
      have hCoB : B.Contractive := by
        cases hWF.2.2 with | tRec hCo0 hG0 => exact hCo0
      have hClB : B.IsClosed :=
        closed_of_trec_closed_vacuous hfree hWF.2.1
      cases hAd with
      | trec_yes _ hsub =>
        have hAdB := by
          rw [subst_noop B X _ hfree] at hsub
          exact hsub
        have hltB : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
        exact SessionType.VacuousRec.trec hfree
          (ih B hltB ⟨hNDB, hClB, hCoB⟩ _ hAdB)
      | trec_vac _ hsub =>
        have hltB : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
        exact SessionType.VacuousRec.trec hfree
          (ih B hltB ⟨hNDB, hClB, hCoB⟩ _ hsub)
  exact hC T hWF f hAd


