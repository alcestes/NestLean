import Nest.Tests.MonitorCo
import Nest.SessionAdequacy
import Nest.MonitorSoundness
import Nest.Examples.ProofUtils

/-! # Counterexample: `monitor_soundness` needs the `Prunable` hypothesis.

The finite monitor-soundness theorem (`monitor_soundness`,
`Nest/MonitorSoundness.lean`) assumes `N.Prunable` on top of well-formedness,
no self-sends, roles present, output-liveness and half-duplexity. This file
shows the hypothesis is load-bearing: with role `p` running the recursive
type `T07 = μX. r?{a : q?x.end, b : X}` (from `Nest/Tests/MonitorCo.lean`),
the inductive monitor semantics admits no `q?x`-acceptance transition to the
coinductive target `T07U` — even though coinductively the transition exists
(`t07_sound_qx : mon_tr_yes_co T07 gQx T07U`). Hence the network below, where
`q` sends `x` to `p`, satisfies the structural hypotheses (well-formedness,
no self-sends, roles present, defined instrumentation) but not `Prunable`,
and the inductive `x`-acceptance step the finite soundness proof would need
for the `q → p` communication has no inductive counterpart.
-/

/-- `q` sends `x` to `p`, then ends. -/
def cxTq : SessionType :=
  SessionType.internalChoice [("p", "x", "S", SessionType.tEnd)]

/-- `r` sends `a` to `p`, then ends. -/
def cxTr : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tEnd)]

-- ================================================================
-- Half-duplex + output-liveness extension.
-- The same `cxN` already satisfies both; we prove it minimally.
-- ================================================================

section CxLiveness

/-- `cxTq` only sends `p!x` to `tEnd`. -/
theorem cxTq_out {T' : SessionType} {α : st_label}
    (h : st_trans cxTq α T') : α = st_label.out "p" "x" "S" ∧ T' = SessionType.tEnd := by
  unfold cxTq at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl⟩

/-- `cxTr` only sends `p!a` to `tEnd`. -/
theorem cxTr_out {T' : SessionType} {α : st_label}
    (h : st_trans cxTr α T') : α = st_label.out "p" "a" "S" ∧ T' = SessionType.tEnd := by
  unfold cxTr at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl⟩

/-- `CoT_branch` only receives `q?x` to `tEnd`. -/
theorem coT_inp {T' : SessionType} {α : st_label}
    (h : st_trans CoT_branch α T') : α = st_label.inp "q" "x" "S" ∧ T' = SessionType.tEnd := by
  unfold CoT_branch at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl⟩

/-- `T07` only receives `r?a → CoT` or `r?b → T07`. -/
theorem t07_inp {T' : SessionType} {α : st_label}
    (h : st_trans T07 α T') :
      (α = st_label.inp "r" "a" "S" ∧ T' = CoT_branch) ∨
      (α = st_label.inp "r" "b" "S" ∧ T' = T07) := by
  unfold T07 at h
  cases h with
  | tRec hsub =>
    have heq : substSessionType T07body "X" (SessionType.tRec "X" T07body) = T07unfold := rfl
    rw [heq] at hsub
    unfold T07unfold at hsub
    cases hsub with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩

/-- `T07` never sends. -/
theorem t07_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ st_trans T07 (st_label.out p lab S) T' := by
  intro h
  have h' := t07_inp h
  rcases h' with ⟨hα, _⟩ | ⟨hα, _⟩ <;> simp at hα

/-- `CoT_branch` never sends. -/
theorem coT_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ st_trans CoT_branch (st_label.out p lab S) T' := by
  intro h
  have h' := coT_inp h
  obtain ⟨hα, _⟩ := h'
  simp at hα

/-- `cxTq` never receives. -/
theorem cxTq_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ st_trans cxTq (st_label.inp p lab S) T' := by
  intro h
  have h' := cxTq_out h
  obtain ⟨hα, _⟩ := h'
  simp at hα

/-- `cxTr` never receives. -/
theorem cxTr_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ st_trans cxTr (st_label.inp p lab S) T' := by
  intro h
  have h' := cxTr_out h
  obtain ⟨hα, _⟩ := h'
  simp at hα

end CxLiveness

/-- Counterexample network: `p` runs `T07`, `q`/`r` feed it one message each. -/
def cxN : Network :=
  [("p", (T07, [])), ("q", (cxTq, [])), ("r", (cxTr, []))]

/-- Instrumented network: empty queues fold to the source types themselves. -/
def cxMN : MonitoredNetwork :=
  [(("p", ((T07, []), T07))), (("q", ((cxTq, []), cxTq))), (("r", ((cxTr, []), cxTr)))]

/-- Well-formedness facts for the hand-written roles. -/
theorem cxTq_wf : cxTq.WellFormed := SessionType.wfCheck_sound (by decide)

theorem cxTr_wf : cxTr.WellFormed := SessionType.wfCheck_sound (by decide)

theorem T07_wf' : T07.WellFormed := SessionType.wfCheck_sound (by decide)

/-- Role occurrences are computable. -/
theorem T07_roles : rolesOf T07 = ["r", "q"] := by decide

theorem cxTq_roles : rolesOf cxTq = ["p"] := by decide

theorem cxTr_roles : rolesOf cxTr = ["p"] := by decide

/-- Coinductively, `p`'s monitor does accept `q?x` (proved in the test corpus). -/
theorem T07_co_accept : ∃ hT hV, mon_tr_yes_co T07 gQx T07U hT hV :=
  ⟨_, _, t07_sound_qx⟩

/-- Substitution unfolds `T07` to the one-step-unfolded choice. -/
theorem T07_subst_unfold :
    substSessionType T07body "X" (SessionType.tRec "X" T07body) = T07unfold := rfl

/-- No inductive base acceptance of `q?x` from the unfolded `T07`: the owner
    (`r`) and the sender (`q`) disagree. -/
theorem no_base_qx_unfold {V : SessionType}
    (hb : mon_tr_yes_base T07unfold (ext_tag.recv "q" "x" "S") V) : False := by
  generalize hγ : (ext_tag.recv "q" "x" "S") = γ at hb
  unfold T07unfold at hb
  cases hb with
  | extC _ _ =>
    simp only [ext_tag.recv.injEq] at hγ
    exact absurd hγ.1 (by decide)

/-- The inductive monitor of `p` has no `q?x`-transition to the coinductive target:
    `T07U` is a `tRec`, so the maximal-prefix rule's kept-target equation fails. -/
theorem T07_no_inductive_x_T07U : ¬ mon_tr_yes T07 gQx T07U := by
  rintro ⟨h, m⟩
  simp only [T07, gQx, T07U] at h
  cases h with
  | base hb =>
    cases hb with
    | tRec hsub =>
      rw [T07_subst_unfold] at hsub
      exact no_base_qx_unfold hsub
  | unfold hsub =>
    rw [T07_subst_unfold] at hsub
    unfold T07unfold at hsub
    cases hsub with
    | base hb => exact no_base_qx_unfold hb
    | pfxExt _ _ hkept _ _ _ => cases hkept

/-- `CoT_branch` existentially accepts `q?x` to `end`. -/
theorem CoT_exist_qx : ∃ V, mon_tr_yes_exist CoT_branch gQx V :=
  ⟨SessionType.tEnd,
    mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))⟩

/-- `T07` existentially accepts `q?x` (non-maximal kept list `[(a, end)]`). -/
theorem T07_exist_qx : ∃ V, mon_tr_yes_exist T07 gQx V := by
  refine ⟨SessionType.externalChoice "r" [("a", "S", SessionType.tEnd)], ?_⟩
  apply mon_tr_yes_exist.unfold
  show mon_tr_yes_exist T07unfold gQx _
  unfold T07unfold
  refine mon_tr_yes_exist.pfxExt ⟨by decide, by decide⟩ (by decide) rfl ?_ ?_ ?_
  · intro T0 T1 l s hB hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact mon_tr_yes_exist.base
        (mon_tr_yes_base.extC (by decide) (by simp))
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      simp at hK
  · exact List.nodup_singleton _
  · intro l s T1 hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
    obtain ⟨rfl, rfl, rfl⟩ := hK
    exact ⟨CoT_branch, by simp⟩

/-- No maximal `q?x` acceptance from `T07` (hence none from its unfold):
    any maximal derivation forces the `b`-branch to be kept (both branches
    are existentially acceptable), and its sub-derivation is a smaller
    maximal derivation for the same goal. -/
theorem T07_no_maximal_any : ∀ {T : SessionType} {γ : ext_tag} {V : SessionType}
    {hE : mon_tr_yes_exist T γ V} (_hM : mon_tr_yes_max_deriv hE),
    (T = T07 ∨ T = T07unfold) → γ = gQx → False := by
  refine mon_tr_yes_max_deriv.rec (motive := fun {T γ V} hE _hM =>
    (T = T07 ∨ T = T07unfold) → γ = gQx → False) ?_ ?_ ?_ ?_
  · intro T γ V hb hDisj hγ
    cases hb with
    | @intC branches huniq p lab S T' hmem =>
      rcases hDisj with h | h
      · unfold T07 at h; cases h
      · unfold T07unfold at h; cases h
    | @extC branches huniq p lab S T' hmem =>
      rcases hDisj with h | h
      · unfold T07 at h; cases h
      · unfold T07unfold at h; cases h
        simp only [gQx, ext_tag.recv.injEq] at hγ
        exact absurd hγ.1 (by decide)
    | @tRec X B T' γ' hsub =>
      rcases hDisj with h | h
      · unfold T07 at h; cases h
        subst hγ
        rw [T07_subst_unfold] at hsub
        exact no_base_qx_unfold hsub
      · unfold T07unfold at h; cases h
  · intro branches kept q lab S T' hne hno hkept hall hNK hkey
      hallMax hcover horder _ihMax hDisj hγ
    rcases hDisj with h | h
    · unfold T07 at h; cases h
    · unfold T07unfold at h; cases h
  · intro p branches kept q lab S T' hne hneq hkept hall hNK hkey
      hallMax hcover horder ihMax hDisj hγ
    rcases hDisj with h | h
    · unfold T07 at h; cases h
    · unfold T07unfold at h; cases h
      simp only [gQx, ext_tag.recv.injEq] at hγ
      obtain ⟨rfl, rfl, rfl⟩ := hγ
      have hmemB_b : (("b", "S", T07) ∈
          [("a", "S", CoT_branch), ("b", "S", T07)]) := by simp
      obtain ⟨T1b, hmemK_b⟩ :=
        hcover "b" "S" T07 hmemB_b T07_exist_qx
      have hsub_b := hall T07 T1b "b" "S" hmemB_b hmemK_b
      exact ihMax T07 T1b "b" "S" hmemB_b hmemK_b hsub_b
        (Or.inl rfl) rfl
  · intro X B γ V h hmax ih hDisj hγ
    rcases hDisj with h | h
    · unfold T07 at h; cases h
      exact ih (Or.inr T07_subst_unfold) hγ
    · unfold T07unfold at h; cases h

/-- No inductive `q?x` acceptance from `T07` to any target. -/
theorem T07_no_inductive_x_any : ¬ ∃ V, mon_tr_yes T07 gQx V := by
  rintro ⟨V, hE, hM⟩
  exact T07_no_maximal_any hM (Or.inl rfl) rfl

/-- `q?x` is exposed from `T07` (via the `a`-branch). -/
theorem T07_exposed_qx : ExposedFrom T07 "q" "x" "S" := by
  unfold T07
  apply ExposedFrom.trec
  unfold T07body
  have hmem_a : (("a", "S", CoT_branch) : Lab × DataSort × SessionType) ∈
      [("a", "S", CoT_branch), ("b", "S", SessionType.tVar "X")] := by simp
  have hsub : ExposedFrom CoT_branch "q" "x" "S" :=
    ExposedFrom.extC_here (p := "q") (branches := [("x", "S", SessionType.tEnd)])
      (lab := "x") (S := "S") (T' := SessionType.tEnd) (by simp)
  exact ExposedFrom.extC_step (by decide) hmem_a hsub

/-- One-message prunability fails for `q?x` at `T07`: the forced steps cycle
    `T07 → unfold → T07`, so the reachability is not acyclic. -/
theorem T07_not_prunableonemsg : ¬ PrunableOneMsg "q" "x" "S" T07 := by
  intro hPrune
  have hHas : pruneFirstInputDeepHas "q" "x" "S" T07 = true := by decide
  have hRTC1 : Relation.ReflTransGen (forced_step "q" "x" "S") T07
      (substSessionType T07body "X" T07) :=
    Relation.ReflTransGen.single forced_step.trec
  have hforced : forced_step "q" "x" "S"
      (substSessionType T07body "X" T07) T07 :=
    forced_step.extCQ (q := "r")
      (branches := [("a", "S", CoT_branch), ("b", "S", T07)])
      (x := ("b", "S", T07)) (by decide) (by simp) hHas
  exact (hPrune _ _ hRTC1 hforced) hRTC1

/-- `T07` is not prunable: `trec_new` demands one-message prunability for the
    exposed `(q, x, S)` triple, which fails by the forced-step cycle above. -/
theorem T07_not_prunable : ¬ Prunable [] T07 := by
  intro h
  unfold T07 at h
  cases h with
  | trec_new _ _ _ _ _ hOne =>
    exact T07_not_prunableonemsg (hOne "q" "x" "S" T07_exposed_qx)
  | trec_seen _ _ _ hmem _ =>
    simp at hmem

/-- The network satisfies well-formedness. -/
theorem cxN_wellformed : cxN.WellFormed := by
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    have hx3 : x = ("p", (T07, [])) ∨ x = ("q", (cxTq, [])) ∨
        x = ("r", (cxTr, [])) := by simpa [cxN] using hx
    rcases hx3 with rfl | rfl | rfl
    · show SessionType.WellFormed T07
      exact T07_wf'
    · show SessionType.WellFormed cxTq
      exact cxTq_wf
    · show SessionType.WellFormed cxTr
      exact cxTr_wf
  · exact Network.SenderClosed_of_all_nil (by
      intro x hx
      have hx3 : x = ("p", (T07, [])) ∨ x = ("q", (cxTq, [])) ∨
          x = ("r", (cxTr, [])) := by simpa [cxN] using hx
      rcases hx3 with rfl | rfl | rfl <;> rfl)

/-- The network has no self-sends. -/
theorem cxN_noself : cxN.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  have hx3 : x = ("p", (T07, [])) ∨ x = ("q", (cxTq, [])) ∨
      x = ("r", (cxTr, [])) := by simpa [cxN] using hx
  rcases hx3 with rfl | rfl | rfl
  · show ("p" : Role) ∉ rolesOf T07
    rw [T07_roles]
    decide
  · show ("q" : Role) ∉ rolesOf cxTq
    rw [cxTq_roles]
    decide
  · show ("r" : Role) ∉ rolesOf cxTr
    rw [cxTr_roles]
    decide

/-- Every occurring role is a member. -/
theorem cxN_rolespresent : cxN.RolesPresent := by
  intro q T Q s hmem hocc
  have hmem' := occurs_mem hocc
  have hm3 : (q, (T, Q)) = ("p", (T07, [])) ∨ (q, (T, Q)) = ("q", (cxTq, [])) ∨
      (q, (T, Q)) = ("r", (cxTr, [])) := by simpa [cxN] using hmem
  rcases hm3 with h | h | h
  · cases h
    have hdisj : s = "r" ∨ s = "q" := by simpa [T07_roles] using hmem'
    rcases hdisj with rfl | rfl
    · exact ⟨(cxTr, []), by simp [cxN]⟩
    · exact ⟨(cxTq, []), by simp [cxN]⟩
  · cases h
    have hs : s = "p" := by simpa [cxTq_roles] using hmem'
    subst hs
    exact ⟨(T07, []), by simp [cxN]⟩
  · cases h
    have hs : s = "p" := by simpa [cxTr_roles] using hmem'
    subst hs
    exact ⟨(T07, []), by simp [cxN]⟩

-- ================================================================
-- Per-role invariant for half-duplex / output-liveness.
-- ================================================================

section CxInv

/-- Per-role shape invariant: `p` stays in `{T07, CoT, tEnd}`,
    `q`/`r` stay one-shot with empty queues, no other roles,
    and `p`'s queue never contains a self-message. -/
def CxInv (N' : Network) : Prop :=
  (∀ T Q, ("p", (T, Q)) ∈ N' → (T = T07 ∨ T = CoT_branch ∨ T = SessionType.tEnd)) ∧
  (∀ T Q, ("q", (T, Q)) ∈ N' → (T = cxTq ∨ T = SessionType.tEnd) ∧ Q = []) ∧
  (∀ T Q, ("r", (T, Q)) ∈ N' → (T = cxTr ∨ T = SessionType.tEnd) ∧ Q = []) ∧
  (∀ x ∈ N', x.1 = "p" ∨ x.1 = "q" ∨ x.1 = "r") ∧
  (∀ T Q, ("p", (T, Q)) ∈ N' → ∀ m ∈ Q, m.1 ≠ "p")

theorem cxInv_base : CxInv cxN := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Q h
    have h3 : ("p", (T, Q)) = ("p", (T07, [])) ∨ ("p", (T, Q)) = ("q", (cxTq, [])) ∨
        ("p", (T, Q)) = ("r", (cxTr, [])) := by simpa [cxN] using h
    rcases h3 with h | h | h
    · have hT : T = T07 := congrArg (fun x : Role × SessionTypeWithQueue => x.2.1) h
      exact Or.inl hT
    · have hR : ("p" : Role) = "q" := congrArg Prod.fst h
      exact absurd hR (by decide)
    · have hR : ("p" : Role) = "r" := congrArg Prod.fst h
      exact absurd hR (by decide)
  · intro T Q h
    have h3 : ("q", (T, Q)) = ("p", (T07, [])) ∨ ("q", (T, Q)) = ("q", (cxTq, [])) ∨
        ("q", (T, Q)) = ("r", (cxTr, [])) := by simpa [cxN] using h
    rcases h3 with h | h | h
    · have hR : ("q" : Role) = "p" := congrArg Prod.fst h
      exact absurd hR (by decide)
    · have hT : T = cxTq := congrArg (fun x : Role × SessionTypeWithQueue => x.2.1) h
      have hQ : Q = ([] : Queue) := congrArg (fun x : Role × SessionTypeWithQueue => x.2.2) h
      exact ⟨Or.inl hT, hQ⟩
    · have hR : ("q" : Role) = "r" := congrArg Prod.fst h
      exact absurd hR (by decide)
  · intro T Q h
    have h3 : ("r", (T, Q)) = ("p", (T07, [])) ∨ ("r", (T, Q)) = ("q", (cxTq, [])) ∨
        ("r", (T, Q)) = ("r", (cxTr, [])) := by simpa [cxN] using h
    rcases h3 with h | h | h
    · have hR : ("r" : Role) = "p" := congrArg Prod.fst h
      exact absurd hR (by decide)
    · have hR : ("r" : Role) = "q" := congrArg Prod.fst h
      exact absurd hR (by decide)
    · have hT : T = cxTr := congrArg (fun x : Role × SessionTypeWithQueue => x.2.1) h
      have hQ : Q = ([] : Queue) := congrArg (fun x : Role × SessionTypeWithQueue => x.2.2) h
      exact ⟨Or.inl hT, hQ⟩
  · intro x hx
    simp only [cxN, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro T Q h m hm
    have h3 : ("p", (T, Q)) = ("p", (T07, [])) ∨ ("p", (T, Q)) = ("q", (cxTq, [])) ∨
        ("p", (T, Q)) = ("r", (cxTr, [])) := by simpa [cxN] using h
    rcases h3 with h | h | h
    · have hQ : Q = ([] : Queue) := congrArg (fun x : Role × SessionTypeWithQueue => x.2.2) h
      rw [hQ] at hm
      cases hm
    · have hR : ("p" : Role) = "q" := congrArg Prod.fst h
      exact absurd hR (by decide)
    · have hR : ("p" : Role) = "r" := congrArg Prod.fst h
      exact absurd hR (by decide)

theorem mem_replace_iff {N : Network} {r0 : Role} {stq0 : SessionTypeWithQueue}
    {r : Role} {stq : SessionTypeWithQueue} :
    (r, stq) ∈ Network.replace N r0 stq0 →
      (r = r0 ∧ stq = stq0) ∨ ((r, stq) ∈ N ∧ r ≠ r0) := by
  unfold Network.replace
  simp only [List.mem_cons, List.mem_filter]
  intro h
  rcases h with h | ⟨hmem, hne⟩
  · left
    cases h
    exact ⟨rfl, rfl⟩
  · right
    exact ⟨hmem, bne_iff_ne.mp hne⟩

section CxInvPreserve

/-- Queue subset for dequeue: members of result come from original. -/
theorem cx_dequeue_subset (seen left : Queue) (msg : QueueMessage) (Q' : Queue)
    (h : Queue.dequeue.go seen left msg = some Q') :
    ∀ x ∈ Q', x ∈ seen ++ left := by
  induction left generalizing seen with
  | nil =>
    simp [Queue.dequeue.go] at h
  | cons m left' ih =>
    simp only [Queue.dequeue.go] at h
    by_cases heq : m = msg
    · simp [heq] at h
      subst h
      intro x hx
      have hmem : x ∈ seen ∨ x ∈ left' := by
        simpa [List.mem_append] using hx
      rcases hmem with h1 | h1
      · exact List.mem_append.mpr (Or.inl h1)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1)))
    · simp [heq] at h
      by_cases heq2 : m.1 = msg.1
      · simp [heq2] at h
      · simp [heq2] at h
        have hsub := ih (seen ++ [m]) h
        intro x hx
        have hx' := hsub x hx
        rw [List.mem_append] at hx' ⊢
        rcases hx' with h1 | h1
        · rw [List.mem_append] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · rw [List.mem_singleton] at h1
            subst h1
            exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inr (List.mem_cons.mpr (Or.inr h1))

theorem cx_dequeue_mem_subset {Q : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Q.dequeue msg = some Q') : ∀ x ∈ Q', x ∈ Q := by
  have hsub := cx_dequeue_subset [] Q msg Q' h
  intro x hx
  have := hsub x hx
  simpa using this

theorem cxInv_step_deq {N N' : Network} {r0 snd : Role} {stq stq' : SessionTypeWithQueue}
    {lab : Lab} {S : DataSort} (hInv : CxInv N)
    (hSQ : sq_trans stq (sq_action.dequeue snd lab S) stq')
    (hmem0 : (r0, stq) ∈ N) (hEq : N' = Network.replace N r0 stq') :
    CxInv N' := by
  obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
  obtain ⟨T, Q⟩ := stq
  obtain ⟨T', Q'⟩ := stq'
  cases hSQ with
  | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
    subst hEq
    have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
    rcases hR0 with rfl | rfl | rfl
    · have hPT := hP T Q hmem0
      rcases hPT with rfl | rfl | rfl
      · have hInp := t07_inp hST
        rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
        · subst hT'
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, hstq⟩ | ⟨hmem, _⟩
            · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
              exact Or.inr (Or.inl rfl)
            · exact hP _ _ hmem
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exfalso; exact absurd hr (by decide)
            · exact hQ _ _ hmem
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exfalso; exact absurd hr (by decide)
            · exact hR _ _ hmem
          · intro x hx
            have h' := mem_replace_iff hx
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exact Or.inl hr
            · exact hRoles _ hmem
          · intro T0 Q0 hmem' m hm
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, hstq⟩ | ⟨hmem, _⟩
            · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
              have hSub := cx_dequeue_mem_subset hQdeq
              have hmQ : m ∈ Q := hSub _ hm
              exact hNoP _ _ hmem0 _ hmQ
            · exact hNoP _ _ hmem _ hm
        · subst hT'
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, hstq⟩ | ⟨hmem, _⟩
            · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
              exact Or.inl rfl
            · exact hP _ _ hmem
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exfalso; exact absurd hr (by decide)
            · exact hQ _ _ hmem
          · intro T0 Q0 hmem'
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exfalso; exact absurd hr (by decide)
            · exact hR _ _ hmem
          · intro x hx
            have h' := mem_replace_iff hx
            rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
            · exact Or.inl hr
            · exact hRoles _ hmem
          · intro T0 Q0 hmem' m hm
            have h' := mem_replace_iff hmem'
            rcases h' with ⟨hr, hstq⟩ | ⟨hmem, _⟩
            · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
              have hSub := cx_dequeue_mem_subset hQdeq
              have hmQ : m ∈ Q := hSub _ hm
              exact hNoP _ _ hmem0 _ hmQ
            · exact hNoP _ _ hmem _ hm
      · have hC := coT_inp hST
        obtain ⟨hα, hT'⟩ := hC
        subst hT'
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro T0 Q0 hmem'
          have h' := mem_replace_iff hmem'
          rcases h' with ⟨hr, hstq⟩ | ⟨hmem, _⟩
          · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
            exact Or.inr (Or.inr rfl)
          · exact hP _ _ hmem
        · intro T0 Q0 hmem'
          have h' := mem_replace_iff hmem'
          rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
          · exfalso; exact absurd hr (by decide)
          · exact hQ _ _ hmem
        · intro T0 Q0 hmem'
          have h' := mem_replace_iff hmem'
          rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
          · exfalso; exact absurd hr (by decide)
          · exact hR _ _ hmem
        · intro x hx
          have h' := mem_replace_iff hx
          rcases h' with ⟨hr, _⟩ | ⟨hmem, _⟩
          · exact Or.inl hr
          · exact hRoles _ hmem
        · intro T0 Q0 hmem' m hm
          have h' := mem_replace_iff hmem'
          rcases h' with ⟨hr, hstq⟩ | ⟨hmem2, _⟩
          · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
            have hSub := cx_dequeue_mem_subset hQdeq
            have hmQ : m ∈ Q := hSub _ hm
            exact hNoP _ _ hmem0 _ hmQ
          · exact hNoP _ _ hmem2 _ hm
      · exfalso; exact st_trans_t_end_absurd hST
    · have hQT := hQ T Q hmem0
      rcases hQT.1 with rfl | rfl
      · exfalso; exact cxTq_no_inp hST
      · exfalso; exact st_trans_t_end_absurd hST
    · have hRT := hR T Q hmem0
      rcases hRT.1 with rfl | rfl
      · exfalso; exact cxTr_no_inp hST
      · exfalso; exact st_trans_t_end_absurd hST

theorem cxInv_send {N : Network} {s : Role} {T T' : SessionType} {Q : Queue} {lab : Lab} {S : DataSort}
    (hInv : CxInv N) (hmem : (s, (T, Q)) ∈ N)
    (hST : st_trans T (st_label.out "p" lab S) T')
    (hNew : T' = SessionType.tEnd) :
    CxInv (Network.replace N s (T', Q)) := by
  obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
  have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem
  rcases hRs with rfl | rfl | rfl
  · have hPT := hP T Q hmem
    rcases hPT with rfl | rfl | rfl
    · exfalso; exact t07_no_out hST
    · exfalso; exact coT_no_out hST
    · exfalso; exact st_trans_t_end_absurd hST
  · have hQT := hQ T Q hmem
    rcases hQT.1 with rfl | rfl
    · subst hNew
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hP _ _ hm
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, hstq⟩ | ⟨hm, _⟩
        · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
          exact ⟨Or.inr rfl, hQT.2⟩
        · exact hQ _ _ hm
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hR _ _ hm
      · intro x hx
        have h' := mem_replace_iff hx
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exact Or.inr (Or.inl hr)
        · exact hRoles _ hm
      · intro T0 Q0 hm' m hm2
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hmem2, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hNoP _ _ hmem2 _ hm2
    · exfalso; exact st_trans_t_end_absurd hST
  · have hRT := hR T Q hmem
    rcases hRT.1 with rfl | rfl
    · subst hNew
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hP _ _ hm
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hQ _ _ hm
      · intro T0 Q0 hm'
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, hstq⟩ | ⟨hm, _⟩
        · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
          exact ⟨Or.inr rfl, hRT.2⟩
        · exact hR _ _ hm
      · intro x hx
        have h' := mem_replace_iff hx
        rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
        · exact Or.inr (Or.inr hr)
        · exact hRoles _ hm
      · intro T0 Q0 hm' m hm2
        have h' := mem_replace_iff hm'
        rcases h' with ⟨hr, _⟩ | ⟨hmem2, _⟩
        · exfalso; exact absurd hr (by decide)
        · exact hNoP _ _ hmem2 _ hm2
    · exfalso; exact st_trans_t_end_absurd hST

theorem cxInv_recv_p {N : Network} {T : SessionType} {Q : Queue} {msg : QueueMessage}
    (hInv : CxInv N) (hmem : ("p", (T, Q)) ∈ N) (hMsg : msg.1 ≠ "p") :
    CxInv (Network.replace N "p" (T, Q ++ [msg])) := by
  obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
  have hPT := hP T Q hmem
  have hNoPQ := hNoP T Q hmem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T0 Q0 hm'
    have h' := mem_replace_iff hm'
    rcases h' with ⟨hr, hstq⟩ | ⟨hm, _⟩
    · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
      exact hPT
    · exact hP _ _ hm
  · intro T0 Q0 hm'
    have h' := mem_replace_iff hm'
    rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
    · exfalso; exact absurd hr (by decide)
    · exact hQ _ _ hm
  · intro T0 Q0 hm'
    have h' := mem_replace_iff hm'
    rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
    · exfalso; exact absurd hr (by decide)
    · exact hR _ _ hm
  · intro x hx
    have h' := mem_replace_iff hx
    rcases h' with ⟨hr, _⟩ | ⟨hm, _⟩
    · exact Or.inl hr
    · exact hRoles _ hm
  · intro T0 Q0 hm' m hm2
    have h' := mem_replace_iff hm'
    rcases h' with ⟨hr, hstq⟩ | ⟨hmem2, _⟩
    · simp at hstq; obtain ⟨rfl, rfl⟩ := hstq
      simp only [List.mem_append, List.mem_singleton] at hm2
      rcases hm2 with hmemQ | rfl
      · exact hNoPQ _ hmemQ
      · exact hMsg
    · exact hNoP _ _ hmem2 _ hm2

theorem cxInv_comm {N Nmid N' : Network} {s r0 : Role} {lab : Lab} {S : DataSort}
    {T_s T_s' T_r : SessionType} {Q_s Q_r : Queue}
    (hInv : CxInv N)
    (hmem_s : (s, (T_s, Q_s)) ∈ N) (hmem_r : (r0, (T_r, Q_r)) ∈ N)
    (hST : st_trans T_s (st_label.out r0 lab S) T_s')
    (hne : s ≠ r0)
    (hEqMid : Nmid = Network.replace N s (T_s', Q_s))
    (hEq : N' = Network.replace Nmid r0 (T_r, Q_r ++ [QueueMessage.msg s lab S])) :
    CxInv N' := by
  obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
  have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
  rcases hRs with rfl | rfl | rfl
  · exfalso
    have hPT := hP T_s Q_s hmem_s
    rcases hPT with rfl | rfl | rfl
    · exact t07_no_out hST
    · exact coT_no_out hST
    · exact st_trans_t_end_absurd hST
  · have hQT := hQ T_s Q_s hmem_s
    rcases hQT.1 with rfl | rfl
    · have hOut := cxTq_out hST
      obtain ⟨hα, hT'⟩ := hOut
      simp only [st_label.out.injEq] at hα
      obtain ⟨rfl, rfl, rfl⟩ := hα
      have hMid : CxInv Nmid := by
        subst hEqMid
        have hST' : st_trans cxTq (st_label.out "p" "x" "S") T_s' := hST
        exact cxInv_send ⟨hP, hQ, hR, hRoles, hNoP⟩ hmem_s hST' hT'
      have hmem_r_mid : ("p", (T_r, Q_r)) ∈ Nmid := by
        subst hEqMid
        exact mem_replace_other hmem_r (by decide : ("p" : Role) ≠ "q")
      have hRecv := cxInv_recv_p (msg := QueueMessage.msg "q" "x" "S") hMid hmem_r_mid (by decide)
      subst hEq
      exact hRecv
    · exfalso; exact st_trans_t_end_absurd hST
  · have hRT := hR T_s Q_s hmem_s
    rcases hRT.1 with rfl | rfl
    · have hOut := cxTr_out hST
      obtain ⟨hα, hT'⟩ := hOut
      simp only [st_label.out.injEq] at hα
      obtain ⟨rfl, rfl, rfl⟩ := hα
      have hMid : CxInv Nmid := by
        subst hEqMid
        have hST' : st_trans cxTr (st_label.out "p" "a" "S") T_s' := hST
        exact cxInv_send ⟨hP, hQ, hR, hRoles, hNoP⟩ hmem_s hST' hT'
      have hmem_r_mid : ("p", (T_r, Q_r)) ∈ Nmid := by
        subst hEqMid
        exact mem_replace_other hmem_r (by decide : ("p" : Role) ≠ "r")
      have hRecv := cxInv_recv_p (msg := QueueMessage.msg "r" "a" "S") hMid hmem_r_mid (by decide)
      subst hEq
      exact hRecv
    · exfalso; exact st_trans_t_end_absurd hST

theorem cxInv_step {N N' : Network} {δ : net_label}
    (hInv : CxInv N) (hTr : net_trans N δ N') (hInt : is_internal_net_label δ) :
    CxInv N' := by
  cases hTr with
  | io_send hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | io_recv hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
    exact cxInv_step_deq hInv hSQ hmem0 rfl
  | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
    cases h_send with
    | @send Tp Tp' Qp q lab' S' hST =>
      cases h_recv with
      | @recv Tq Qq p lab'' S'' =>
        exact cxInv_comm hInv hmem_s hmem_r hST hne rfl rfl

theorem cxInv_star {N N' : Network} (hStar : net_trans_star N N') (hInv : CxInv N) :
    CxInv N' := by
  induction hStar with
  | refl => exact hInv
  | step hInt hTr _ ih => exact ih (cxInv_step hInv hTr hInt)

theorem cxInv_reachable {N' : Network} (hStar : net_trans_star cxN N') : CxInv N' :=
  cxInv_star hStar cxInv_base

theorem cxN_halfDuplex : IsHalfDuplex cxN := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hInv := cxInv_reachable hStar
  obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
  -- Show q/r queues empty forces p,q to be "p"
  -- First, characterize Qp, Qq emptiness unless owner is p
  have hQp_empty_or_p : Qp = [] ∨ p = "p" := by
    by_cases hp : p = "p"
    · exact Or.inr hp
    · left
      by_cases hq : p = "q"
      · subst hq
        obtain ⟨T, hT⟩ := hP
        have hQ := (hQinv T Qp hT).2
        exact hQ
      · by_cases hr : p = "r"
        · subst hr
          obtain ⟨T, hT⟩ := hP
          have hQ := (hRinv T Qp hT).2
          exact hQ
        · exfalso
          obtain ⟨T, hT⟩ := hP
          -- hT : (p,(T,Qp)) ∈ N', so p = p/q/r by hRoles
          have hR := hRoles _ hT
          rcases hR with rfl | rfl | rfl <;> contradiction
  have hQq_empty_or_p : Qq = [] ∨ q = "p" := by
    by_cases hq : q = "p"
    · exact Or.inr hq
    · left
      by_cases hqq : q = "q"
      · subst hqq
        obtain ⟨T, hT⟩ := hQ
        have hQe := (hQinv T Qq hT).2
        exact hQe
      · by_cases hr : q = "r"
        · subst hr
          obtain ⟨T, hT⟩ := hQ
          have hQe := (hRinv T Qq hT).2
          exact hQe
        · exfalso
          obtain ⟨T, hT⟩ := hQ
          have hR := hRoles _ hT
          rcases hR with rfl | rfl | rfl <;> contradiction
  rcases hQp_empty_or_p with hQpEmpty | rfl
  · -- Qp empty contradicts contains
    have hNil : ¬ QueueContainsFrom ([] : Queue) q := noContainsNil
    rw [hQpEmpty] at hCp
    exact absurd hCp hNil
  · rcases hQq_empty_or_p with hQqEmpty | rfl
    · have hNil : ¬ QueueContainsFrom ([] : Queue) "p" := noContainsNil
      rw [hQqEmpty] at hCq
      exact absurd hCq hNil
    · -- Both roles are "p": Qp contains a "p"-message, but invariant says none.
      obtain ⟨lab, S, hMem⟩ := hCp
      have hmemList : QueueMessage.msg "p" lab S ∈ Qp := QueueMem.to_mem hMem
      obtain ⟨T, hT⟩ := hP
      have hNo := hNoP T Qp hT _ hmemList
      simp at hNo

end CxInvPreserve

section CxOutputLive

/-- Termination measure: 2 per unsent one-shot + queue length + p-stage. -/
def cxMeasure (N : Network) : ℕ :=
  (if networkLookup N "q" = some (cxTq, ([] : Queue)) then 2 else 0) +
  (if networkLookup N "r" = some (cxTr, ([] : Queue)) then 2 else 0) +
  (match networkLookup N "p" with | some (_, Q) => Q.length | none => 0) +
  (match networkLookup N "p" with
    | some (T, _) => (if T = T07 then 1 else if T = CoT_branch then 1 else 0)
    | none => 0)

theorem cxMeasure_base : cxMeasure cxN = 5 := by
  simp [cxMeasure, cxN, networkLookup]

theorem cxWF_reachable {N' : Network} (hStar : net_trans_star cxN N') : N'.WellFormed :=
  net_trans_preserves_well_formed cxN_wellformed hStar

theorem cxMeasure_deq {N N' : Network} {r0 snd : Role} {stq stq' : SessionTypeWithQueue}
    {lab : Lab} {S : DataSort} (hWF : N.WellFormed) (hInv : CxInv N)
    (hSQ : sq_trans stq (sq_action.dequeue snd lab S) stq')
    (hmem0 : (r0, stq) ∈ N) (hEq : N' = Network.replace N r0 stq') :
    cxMeasure N' < cxMeasure N := by
  obtain ⟨T, Q⟩ := stq
  obtain ⟨T', Q'⟩ := stq'
  cases hSQ with
  | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
    subst hEq
    obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
    have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
    rcases hR0 with rfl | rfl | rfl
    · have hPT := hP T Q hmem0
      rcases hPT with rfl | rfl | rfl
      · have hInp := t07_inp hST
        rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
        · subst hT'
          -- N' = replace N "p" (CoT, Q'), N has (p, T07, Q)
          have hNodup := hWF.1
          have hLookNp : networkLookup N "p" = some (T07, Q) :=
            networkLookup_some_of_mem hNodup hmem0
          have hLookNp' : networkLookup (Network.replace N "p" (CoT_branch, Q')) "p" =
              some (CoT_branch, Q') := networkLookup_replace _
          have hLookNq : networkLookup (Network.replace N "p" (CoT_branch, Q')) "q" =
              networkLookup N "q" := networkLookup_replace_other (by decide)
          have hLookNr : networkLookup (Network.replace N "p" (CoT_branch, Q')) "r" =
              networkLookup N "r" := networkLookup_replace_other (by decide)
          have hLen := Queue.dequeue_length_drop hQdeq
          unfold cxMeasure
          rw [hLookNq, hLookNr, hLookNp, hLookNp']
          simp
          omega
        · subst hT'
          have hNodup := hWF.1
          have hLookNp : networkLookup N "p" = some (T07, Q) :=
            networkLookup_some_of_mem hNodup hmem0
          have hLookNp' : networkLookup (Network.replace N "p" (T07, Q')) "p" =
              some (T07, Q') := networkLookup_replace _
          have hLookNq : networkLookup (Network.replace N "p" (T07, Q')) "q" =
              networkLookup N "q" := networkLookup_replace_other (by decide)
          have hLookNr : networkLookup (Network.replace N "p" (T07, Q')) "r" =
              networkLookup N "r" := networkLookup_replace_other (by decide)
          have hLen := Queue.dequeue_length_drop hQdeq
          unfold cxMeasure
          rw [hLookNq, hLookNr, hLookNp, hLookNp']
          simp
          omega
      · have hC := coT_inp hST
        obtain ⟨hα, hT'⟩ := hC
        subst hT'
        have hNodup := hWF.1
        have hLookNp : networkLookup N "p" = some (CoT_branch, Q) :=
          networkLookup_some_of_mem hNodup hmem0
        have hLookNp' : networkLookup (Network.replace N "p" (SessionType.tEnd, Q')) "p" =
            some (SessionType.tEnd, Q') := networkLookup_replace _
        have hLookNq : networkLookup (Network.replace N "p" (SessionType.tEnd, Q')) "q" =
            networkLookup N "q" := networkLookup_replace_other (by decide)
        have hLookNr : networkLookup (Network.replace N "p" (SessionType.tEnd, Q')) "r" =
            networkLookup N "r" := networkLookup_replace_other (by decide)
        have hLen := Queue.dequeue_length_drop hQdeq
        have hNe1 : (SessionType.tEnd ≠ T07) := by decide
        have hNe2 : (SessionType.tEnd ≠ CoT_branch) := by decide
        have hNe3 : (CoT_branch ≠ T07) := by decide
        unfold cxMeasure
        rw [hLookNq, hLookNr, hLookNp, hLookNp']
        simp [hNe1, hNe2, hNe3]
        omega
      · exfalso; exact st_trans_t_end_absurd hST
    · have hQT := hQ T Q hmem0
      rcases hQT.1 with rfl | rfl
      · exfalso; exact cxTq_no_inp hST
      · exfalso; exact st_trans_t_end_absurd hST
    · have hRT := hR T Q hmem0
      rcases hRT.1 with rfl | rfl
      · exfalso; exact cxTr_no_inp hST
      · exfalso; exact st_trans_t_end_absurd hST

theorem cxMeasure_comm {N Nmid N' : Network} {s r0 : Role} {lab : Lab} {S : DataSort}
    {T_s T_s' T_r : SessionType} {Q_s Q_r : Queue}
    (hWF : N.WellFormed) (hInv : CxInv N)
    (hmem_s : (s, (T_s, Q_s)) ∈ N) (hmem_r : (r0, (T_r, Q_r)) ∈ N)
    (hST : st_trans T_s (st_label.out r0 lab S) T_s')
    (hne : s ≠ r0)
    (hEqMid : Nmid = Network.replace N s (T_s', Q_s))
    (hEq : N' = Network.replace Nmid r0 (T_r, Q_r ++ [QueueMessage.msg s lab S])) :
    cxMeasure N' < cxMeasure N := by
  obtain ⟨hP, hQ, hR, hRoles, hNoP⟩ := hInv
  have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
  rcases hRs with rfl | rfl | rfl
  · exfalso
    have hPT := hP T_s Q_s hmem_s
    rcases hPT with rfl | rfl | rfl
    · exact t07_no_out hST
    · exact coT_no_out hST
    · exact st_trans_t_end_absurd hST
  · have hQT := hQ T_s Q_s hmem_s
    rcases hQT.1 with rfl | rfl
    · have hOut := cxTq_out hST
      obtain ⟨hα, hT'⟩ := hOut
      simp only [st_label.out.injEq] at hα
      obtain ⟨rfl, rfl, rfl⟩ := hα
      subst hEqMid
      subst hEq
      have hNodup := hWF.1
      have hLookNq : networkLookup N "q" = some (cxTq, Q_s) :=
        networkLookup_some_of_mem hNodup hmem_s
      have hQempty : Q_s = [] := hQT.2
      subst hQempty
      have hLookNr : networkLookup N "r" = some (T_r, Q_r) ∨ True := Or.inr trivial
      -- Compute measures via lookups
      have hMidQ : networkLookup (Network.replace N "q" (T_s', ([] : Queue))) "q" =
          some (T_s', ([] : Queue)) := networkLookup_replace _
      have hMidR : networkLookup (Network.replace N "q" (T_s', ([] : Queue))) "r" =
          networkLookup N "r" := networkLookup_replace_other (by decide)
      have hMidP : networkLookup (Network.replace N "q" (T_s', ([] : Queue))) "p" =
          networkLookup N "p" := networkLookup_replace_other (by decide)
      have hNq_eq : networkLookup N "q" = some (cxTq, ([] : Queue)) := hLookNq
      -- T_s' = tEnd by hT'
      subst hT'
      -- Now Nmid = replace N q (tEnd, []), N' = replace Nmid p (T_r, Q_r++[qx])
      have hLookNmidP : networkLookup (Network.replace N "q" (SessionType.tEnd, ([] : Queue))) "p" =
          networkLookup N "p" := networkLookup_replace_other (by decide)
      have hLookNp : networkLookup N "p" = some (T_r, Q_r) := by
        -- hmem_r : ("p", (T_r, Q_r)) ∈ N (since r0="p" after subst)
        exact networkLookup_some_of_mem hNodup hmem_r
      have hLookNpMid : networkLookup (Network.replace N "q" (SessionType.tEnd, ([] : Queue))) "p" =
          some (T_r, Q_r) := by rw [hMidP]; exact hLookNp
      have hLookN'P : networkLookup ((Network.replace N "q" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "q" "x" "S"])) "p" =
          some (T_r, Q_r ++ [QueueMessage.msg "q" "x" "S"]) := networkLookup_replace _
      have hLookN'Q : networkLookup ((Network.replace N "q" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "q" "x" "S"])) "q" =
          some (SessionType.tEnd, ([] : Queue)) := by
        rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
        exact hMidQ
      have hLookN'R : networkLookup ((Network.replace N "q" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "q" "x" "S"])) "r" =
          networkLookup N "r" := by
        rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
        exact hMidR
      unfold cxMeasure
      rw [hLookNq, hLookN'Q]
      -- q part: 2 -> 0
      have hRpart_eq : (if networkLookup N "r" = some (cxTr, ([] : Queue)) then (2 : ℕ) else 0) =
          (if networkLookup ((Network.replace N "q" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "q" "x" "S"])) "r" = some (cxTr, ([] : Queue)) then 2 else 0) := by
        rw [hLookN'R]
      rw [hRpart_eq]
      -- p length + pStage
      have hPLen : networkLookup N "p" = some (T_r, Q_r) := hLookNp
      rw [hPLen, hLookN'P]
      have hNeTq : SessionType.tEnd ≠ cxTq := by decide
      simp [hNeTq]
      omega
    · exfalso; exact st_trans_t_end_absurd hST
  · have hRT := hR T_s Q_s hmem_s
    rcases hRT.1 with rfl | rfl
    · have hOut := cxTr_out hST
      obtain ⟨hα, hT'⟩ := hOut
      simp only [st_label.out.injEq] at hα
      obtain ⟨rfl, rfl, rfl⟩ := hα
      subst hEqMid
      subst hEq
      have hNodup := hWF.1
      have hLookNr0 : networkLookup N "r" = some (cxTr, Q_s) :=
        networkLookup_some_of_mem hNodup hmem_s
      have hQempty : Q_s = [] := hRT.2
      subst hQempty
      subst hT'
      have hMidQ : networkLookup (Network.replace N "r" (SessionType.tEnd, ([] : Queue))) "q" =
          networkLookup N "q" := networkLookup_replace_other (by decide)
      have hMidR : networkLookup (Network.replace N "r" (SessionType.tEnd, ([] : Queue))) "r" =
          some (SessionType.tEnd, ([] : Queue)) := networkLookup_replace _
      have hMidP : networkLookup (Network.replace N "r" (SessionType.tEnd, ([] : Queue))) "p" =
          networkLookup N "p" := networkLookup_replace_other (by decide)
      have hLookNp : networkLookup N "p" = some (T_r, Q_r) :=
        networkLookup_some_of_mem hNodup hmem_r
      have hLookN'P : networkLookup ((Network.replace N "r" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"])) "p" =
          some (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"]) := networkLookup_replace _
      have hLookN'Q : networkLookup ((Network.replace N "r" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"])) "q" =
          networkLookup N "q" := by
        rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
        exact hMidQ
      have hLookN'R : networkLookup ((Network.replace N "r" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"])) "r" =
          some (SessionType.tEnd, ([] : Queue)) := by
        rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
        exact hMidR
      have hLookNq0 : networkLookup N "q" = networkLookup ((Network.replace N "r" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"])) "q" := by
        rw [hLookN'Q]
      unfold cxMeasure
      have hRq : networkLookup N "r" = some (cxTr, ([] : Queue)) := hLookNr0
      rw [hRq, hLookN'R]
      have hQpart_eq : (if networkLookup N "q" = some (cxTq, ([] : Queue)) then (2 : ℕ) else 0) =
          (if networkLookup ((Network.replace N "r" (SessionType.tEnd, ([] : Queue))).replace "p" (T_r, Q_r ++ [QueueMessage.msg "r" "a" "S"])) "q" = some (cxTq, ([] : Queue)) then 2 else 0) := by
        rw [hLookN'Q]
      rw [hQpart_eq]
      rw [hLookNp, hLookN'P]
      have hNeTr : SessionType.tEnd ≠ cxTr := by decide
      simp [hNeTr]
      omega
    · exfalso; exact st_trans_t_end_absurd hST

theorem cxMeasure_step {N N' : Network} {δ : net_label}
    (hWF : N.WellFormed) (hInv : CxInv N)
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ) :
    cxMeasure N' < cxMeasure N := by
  cases hTr with
  | io_send hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | io_recv hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
    exact cxMeasure_deq hWF hInv hSQ hmem0 rfl
  | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
    cases h_send with
    | @send Tp Tp' Qp q lab' S' hST =>
      cases h_recv with
      | @recv Tq Qq p lab'' S'' =>
        exact cxMeasure_comm hWF hInv hmem_s hmem_r hST hne rfl rfl

theorem cxMeasure_star_lt {N N' : Network} {δ : net_label}
    (hWF : N.WellFormed) (hInv : CxInv N)
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ) :
    cxMeasure N' < cxMeasure N :=
  cxMeasure_step hWF hInv hTr hInt

section CxInfinite

theorem cxNoInfinitePath : ¬ ∃ path : InfiniteNetworkPath, path.seq 0 = cxN := by
  rintro ⟨path, h0⟩
  have hStar : ∀ i, net_trans_star cxN (path.seq i) := fun i => path_star_reachable h0 i
  have hWF : ∀ i, (path.seq i).WellFormed := fun i => cxWF_reachable (hStar i)
  have hInv : ∀ i, CxInv (path.seq i) := fun i => cxInv_reachable (hStar i)
  have hDec : ∀ i, cxMeasure (path.seq (i + 1)) < cxMeasure (path.seq i) := by
    intro i
    have hTr := path.δ_tr i
    have hForm := path.δ_form i
    obtain ⟨r, p, lab, S, h | h⟩ := hForm
    · rw [h] at hTr
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by trivial
      exact cxMeasure_step (hWF i) (hInv i) hTr hInt
    · rw [h] at hTr
      have hInt : is_internal_net_label (net_label.τ_comm r p lab S) := by trivial
      exact cxMeasure_step (hWF i) (hInv i) hTr hInt
  have hBound : ∀ n, cxMeasure (path.seq n) + n ≤ cxMeasure cxN := by
    intro n
    induction n with
    | zero =>
      rw [h0]
      omega
    | succ k ih =>
      have hlt := hDec k
      omega
  have h0m := hBound (cxMeasure cxN + 1)
  omega

theorem cxN_outputLiveInf : IsOutputLiveInfinitePathNetwork cxN := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  exfalso
  exact cxNoInfinitePath ⟨path, h0⟩

end CxInfinite

section CxStuck

/-- Queued messages. -/
def cxQx : QueueMessage := QueueMessage.msg "q" "x" "S"
def cxRa : QueueMessage := QueueMessage.msg "r" "a" "S"

/-- 8 reachable shapes (lookup-based, order-independent). -/
def CxShape (N' : Network) : Prop :=
  (networkLookup N' "p" = some (T07, []) ∧
    networkLookup N' "q" = some (cxTq, []) ∧
    networkLookup N' "r" = some (cxTr, [])) ∨
  (networkLookup N' "p" = some (T07, [cxQx]) ∧
    networkLookup N' "q" = some (SessionType.tEnd, []) ∧
    networkLookup N' "r" = some (cxTr, [])) ∨
  (networkLookup N' "p" = some (T07, [cxRa]) ∧
    networkLookup N' "q" = some (cxTq, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, [])) ∨
  (networkLookup N' "p" = some (T07, [cxQx, cxRa]) ∧
    networkLookup N' "q" = some (SessionType.tEnd, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, [])) ∨
  (networkLookup N' "p" = some (CoT_branch, []) ∧
    networkLookup N' "q" = some (cxTq, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, [])) ∨
  (networkLookup N' "p" = some (T07, [cxRa, cxQx]) ∧
    networkLookup N' "q" = some (SessionType.tEnd, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, [])) ∨
  (networkLookup N' "p" = some (CoT_branch, [cxQx]) ∧
    networkLookup N' "q" = some (SessionType.tEnd, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, [])) ∨
  (networkLookup N' "p" = some (SessionType.tEnd, []) ∧
    networkLookup N' "q" = some (SessionType.tEnd, []) ∧
    networkLookup N' "r" = some (SessionType.tEnd, []))

theorem cxShape_base : CxShape cxN := by
  left
  simp [cxN, networkLookup, cxTq, cxTr, cxQx, cxRa]

theorem cxShape_step {N N' : Network} {δ : net_label}
    (hWF : N.WellFormed) (hInv : CxInv N) (hShape : CxShape N)
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ) :
    CxShape N' := by
  rcases hShape with h | h | h | h | h | h | h | h
  · -- S0
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · -- r0 = p: stq = (T07, []) via uniqueness, Q=[] so dequeue impossible
        have hMemP : (("p", (T07, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemR : (("r", (cxTr, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · -- s = p: T07 has no out
        have hMemP : (("p", (T07, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST t07_no_out
      · -- s = q: must be q -> p x, leading to S1
        have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          have hOut := cxTq_out hST
          obtain ⟨hα, hT'⟩ := hOut
          simp only [st_label.out.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          cases h_recv with
          | @recv Tq Qq p lab'' S'' =>
            -- hmem_r : ("p", (Tq,Qq)) ∈ N, must have (Tq,Qq)=(T07,[])
            have hMemP : (("p", (T07, ([] : Queue))) ∈ N) := networkLookup_mem hP
            have hEqR := network_mem_unique hWF hmem_r hMemP
            simp at hEqR
            obtain ⟨rfl, rfl⟩ := hEqR
            -- N' is (N.replace "q" (tEnd,[])).replace "p" (T07, []++[msg])
            -- Show S1
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · -- p = (T07, [qx]): last replace is p, new entry is (T07, []++[qx])
              exact networkLookup_replace _
            · -- q = (tEnd, []): last replace is p (q≠p), then Nmid replace q
              rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact networkLookup_replace _
            · -- r unchanged = (cxTr, []): r≠p, r≠q, use shape hR
              rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p"),
                networkLookup_replace_other (by decide : ("r" : Role) ≠ "q")]
              exact hR
      · -- s = r: must be r -> p a, leading to S2
        have hMemR : (("r", (cxTr, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          have hOut := cxTr_out hST
          obtain ⟨hα, hT'⟩ := hOut
          simp only [st_label.out.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          cases h_recv with
          | @recv Tq Qq p lab'' S'' =>
            have hMemP : (("p", (T07, ([] : Queue))) ∈ N) := networkLookup_mem hP
            have hEqR := network_mem_unique hWF hmem_r hMemP
            simp at hEqR
            obtain ⟨rfl, rfl⟩ := hEqR
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p"),
                networkLookup_replace_other (by decide : ("q" : Role) ≠ "r")]
              exact hQ
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
              exact networkLookup_replace _
  · -- S1: p=(T07,[qx]), q=(tEnd,[]), r=(cxTr,[])
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · -- r0=p: (T07,[qx]), t07_inp forces snd=r, but [qx] has no r-msg
        have hMemP : (("p", (T07, [cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp [cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          have hInp := t07_inp hST
          rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
          · -- r,a: [qx] dequeue (r,a) = none
            simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            simp [cxQx, Queue.dequeue, Queue.dequeue.go] at hQdeq
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            simp [cxQx, Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemR : (("r", (cxTr, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp [cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST t07_no_out
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · -- s=r: r->p a, leading to S3 (p=[qx,ra])
        have hMemR : (("r", (cxTr, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          have hOut := cxTr_out hST
          obtain ⟨hα, hT'⟩ := hOut
          simp only [st_label.out.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          cases h_recv with
          | @recv Tq Qq p lab'' S'' =>
            have hMemP : (("p", (T07, [cxQx])) ∈ N) := networkLookup_mem hP
            have hEqR := network_mem_unique hWF hmem_r hMemP
            simp [cxQx] at hEqR
            obtain ⟨rfl, rfl⟩ := hEqR
            -- S3: p=[qx,ra], q=tEnd, r=tEnd
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p"),
                networkLookup_replace_other (by decide : ("q" : Role) ≠ "r")]
              exact hQ
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
              exact networkLookup_replace _
  · -- S2: p=(T07,[ra]), q=(cxTq,[]), r=(tEnd,[])
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxRa])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp [cxRa] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ Q' _ _ _ hST hQdeq =>
          have hInp := t07_inp hST
          rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            subst hT'
            -- Deq ra from [ra] -> [], T07->CoT, leading to S4
            have hDeq : Queue.dequeue [cxRa] (QueueMessage.msg "r" "a" "S") = some ([] : Queue) := by decide
            have hQeq : Q' = [] := by
              have h1 : Queue.dequeue [cxRa] (QueueMessage.msg "r" "a" "S") = some Q' := hQdeq
              rw [hDeq] at h1
              exact (Option.some_inj.mp h1).symm
            subst hQeq
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact hQ
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
              exact hR
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            -- Deq (r,b) from [ra] = none (same sender, diff lab) -> impossible
            simp [cxRa, Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ p lab' S' hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxRa])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp [cxRa] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST t07_no_out
      · -- s=q: q->p x, [ra]++[qx]=[ra,qx] -> S5
        have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          have hOut := cxTq_out hST
          obtain ⟨hα, hT'⟩ := hOut
          simp only [st_label.out.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          cases h_recv with
          | @recv Tq Qq p lab'' S'' =>
            have hMemP : (("p", (T07, [cxRa])) ∈ N) := networkLookup_mem hP
            have hEqR := network_mem_unique hWF hmem_r hMemP
            simp [cxRa] at hEqR
            obtain ⟨rfl, rfl⟩ := hEqR
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p"),
                networkLookup_replace_other (by decide : ("r" : Role) ≠ "q")]
              exact hR
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
  · -- S3: p=(T07,[qx,ra]), q=tEnd, r=tEnd -> deq ra -> S6
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxQx, cxRa])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp [cxQx, cxRa] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ Q' _ _ _ hST hQdeq =>
          have hInp := t07_inp hST
          rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            subst hT'
            have hDeq : Queue.dequeue [cxQx, cxRa] (QueueMessage.msg "r" "a" "S") = some [cxQx] := by decide
            have hQeq : Q' = [cxQx] := by
              have h1 : Queue.dequeue [cxQx, cxRa] (QueueMessage.msg "r" "a" "S") = some Q' := hQdeq
              rw [hDeq] at h1
              exact (Option.some_inj.mp h1).symm
            subst hQeq
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact hQ
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
              exact hR
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            have hNone : Queue.dequeue [QueueMessage.msg "q" "x" "S", QueueMessage.msg "r" "a" "S"] (QueueMessage.msg "r" "b" "S") = none := by decide
            rw [hNone] at hQdeq
            cases hQdeq
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxQx, cxRa])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp [cxQx, cxRa] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST t07_no_out
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
  · -- S4: p=(CoT,[]), q=cxTq, r=tEnd -> comm q->p -> S6
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (CoT_branch, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (CoT_branch, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST coT_no_out
      · -- s=q -> S6
        have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          have hOut := cxTq_out hST
          obtain ⟨hα, hT'⟩ := hOut
          simp only [st_label.out.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          cases h_recv with
          | @recv Tq Qq p lab'' S'' =>
            have hMemP : (("p", (CoT_branch, ([] : Queue))) ∈ N) := networkLookup_mem hP
            have hEqR := network_mem_unique hWF hmem_r hMemP
            simp at hEqR
            obtain ⟨rfl, rfl⟩ := hEqR
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p"),
                networkLookup_replace_other (by decide : ("r" : Role) ≠ "q")]
              exact hR
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
  · -- S5: p=(T07,[ra,qx]), q=tEnd, r=tEnd -> deq ra -> S6
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxRa, cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp [cxRa, cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ Q' _ _ _ hST hQdeq =>
          have hInp := t07_inp hST
          rcases hInp with ⟨hα, hT'⟩ | ⟨hα, hT'⟩
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            subst hT'
            have hDeq : Queue.dequeue [cxRa, cxQx] (QueueMessage.msg "r" "a" "S") = some [cxQx] := by decide
            have hQeq : Q' = [cxQx] := by
              have h1 : Queue.dequeue [cxRa, cxQx] (QueueMessage.msg "r" "a" "S") = some Q' := hQdeq
              rw [hDeq] at h1
              exact (Option.some_inj.mp h1).symm
            subst hQeq
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inr
            apply Or.inl
            refine ⟨?_, ?_, ?_⟩
            · exact networkLookup_replace _
            · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
              exact hQ
            · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
              exact hR
          · simp only [st_label.inp.injEq] at hα
            obtain ⟨rfl, rfl, rfl⟩ := hα
            have hNone : Queue.dequeue [QueueMessage.msg "r" "a" "S", QueueMessage.msg "q" "x" "S"] (QueueMessage.msg "r" "b" "S") = none := by decide
            rw [hNone] at hQdeq
            cases hQdeq
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (T07, [cxRa, cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp [cxRa, cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST t07_no_out
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
  · -- S6: p=(CoT,[qx]), q=tEnd, r=tEnd -> deq qx -> S7
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (CoT_branch, [cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp [cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ Q' _ _ _ hST hQdeq =>
          have hC := coT_inp hST
          obtain ⟨hα, hT'⟩ := hC
          simp only [st_label.inp.injEq] at hα
          obtain ⟨rfl, rfl, rfl⟩ := hα
          subst hT'
          have hDeq : Queue.dequeue [cxQx] (QueueMessage.msg "q" "x" "S") = some ([] : Queue) := by decide
          have hQeq : Q' = [] := by
            have h1 : Queue.dequeue [cxQx] (QueueMessage.msg "q" "x" "S") = some Q' := hQdeq
            rw [hDeq] at h1
            exact (Option.some_inj.mp h1).symm
          subst hQeq
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          refine ⟨?_, ?_, ?_⟩
          · exact networkLookup_replace _
          · rw [networkLookup_replace_other (by decide : ("q" : Role) ≠ "p")]
            exact hQ
          · rw [networkLookup_replace_other (by decide : ("r" : Role) ≠ "p")]
            exact hR
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (CoT_branch, [cxQx])) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp [cxQx] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST coT_no_out
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
  · -- S7: p=tEnd, q=tEnd, r=tEnd, no steps
    obtain ⟨hP, hQ, hR⟩ := h
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInv
    cases hTr with
    | io_send hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | io_recv hSQ hmem =>
      simp [is_internal_net_label] at hInt
    | @dequeue r0 snd stq stq' lab S hSQ hmem0 =>
      have hR0 : r0 = "p" ∨ r0 = "q" ∨ r0 = "r" := hRoles _ hmem0
      rcases hR0 with rfl | rfl | rfl
      · have hMemP : (("p", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem0 hMemP
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem0 hMemQ
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem0 hMemR
        obtain ⟨T, Q⟩ := stq
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases hSQ with
        | @dequeue _ _ _ _ _ _ _ hST hQdeq =>
          exact absurd hST st_trans_t_end_absurd
    | @comm s r0 lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_s hmem_r =>
      have hRs : s = "p" ∨ s = "q" ∨ s = "r" := hRoles _ hmem_s
      rcases hRs with rfl | rfl | rfl
      · have hMemP : (("p", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hP
        have hEq := network_mem_unique hWF hmem_s hMemP
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hQ
        have hEq := network_mem_unique hWF hmem_s hMemQ
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd
      · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N) := networkLookup_mem hR
        have hEq := network_mem_unique hWF hmem_s hMemR
        obtain ⟨T, Q⟩ := stqp
        simp at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        cases h_send with
        | @send Tp Tp' Qp q lab' S' hST =>
          exact absurd hST st_trans_t_end_absurd

theorem cxShape_star {N N' : Network} (hStar : net_trans_star N N')
    (hWF : N.WellFormed) (hInv : CxInv N) (hShape : CxShape N) : CxShape N' := by
  induction hStar with
  | refl => exact hShape
  | step hInt hTr hStar' ih =>
    have hInv2 := cxInv_step hInv hTr hInt
    have hWF2 := Network.wellFormedPreserved _ _ _ hWF hTr hInt
    have hShape2 := cxShape_step hWF hInv hShape hTr hInt
    exact ih hWF2 hInv2 hShape2

theorem cxShape_reachable {N' : Network} (hStar : net_trans_star cxN N') : CxShape N' :=
  cxShape_star hStar cxN_wellformed cxInv_base cxShape_base

theorem cxN_noOrphan_stuck : ∀ (N' : Network), net_trans_star cxN N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck r T Q p lab S Q' hmem hQdeq
  have hShape := cxShape_reachable hStar
  have hWF := cxWF_reachable hStar
  have hInv := cxInv_reachable hStar
  rcases hShape with h | h | h | h | h | h | h | h
  · -- S0: has comm q->p, so not stuck -> False
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N') := networkLookup_mem hQ
    have hMemP : (("p", (T07, ([] : Queue))) ∈ N') := networkLookup_mem hP
    have hST : st_trans cxTq (st_label.out "p" "x" "S") SessionType.tEnd := by
      apply st_trans.intC
      simp [cxTq]
    have hSend : sq_trans (cxTq, ([] : Queue)) (sq_action.send "p" "x" "S") (SessionType.tEnd, ([] : Queue)) :=
      sq_trans.send hST
    have hRecv : sq_trans (T07, ([] : Queue)) (sq_action.recv "q" "x" "S") (T07, [QueueMessage.msg "q" "x" "S"]) :=
      sq_trans.recv
    have hTr : net_trans N' (net_label.τ_comm "q" "p" "x" "S")
        ((N'.replace "q" (SessionType.tEnd, [])).replace "p" (T07, [QueueMessage.msg "q" "x" "S"])) :=
      net_trans.comm (by decide) hSend hRecv hMemQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S1: has comm r->p
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemR : (("r", (cxTr, ([] : Queue))) ∈ N') := networkLookup_mem hR
    have hMemP : (("p", (T07, [cxQx])) ∈ N') := networkLookup_mem hP
    have hST : st_trans cxTr (st_label.out "p" "a" "S") SessionType.tEnd := by
      apply st_trans.intC
      simp [cxTr]
    have hSend : sq_trans (cxTr, ([] : Queue)) (sq_action.send "p" "a" "S") (SessionType.tEnd, ([] : Queue)) :=
      sq_trans.send hST
    have hRecv : sq_trans (T07, [cxQx]) (sq_action.recv "r" "a" "S") (T07, [cxQx, QueueMessage.msg "r" "a" "S"]) :=
      sq_trans.recv
    have hTr : net_trans N' (net_label.τ_comm "r" "p" "a" "S")
        ((N'.replace "r" (SessionType.tEnd, [])).replace "p" (T07, [cxQx, QueueMessage.msg "r" "a" "S"])) :=
      net_trans.comm (by decide) hSend hRecv hMemR hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S2: has comm q->p
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N') := networkLookup_mem hQ
    have hMemP : (("p", (T07, [cxRa])) ∈ N') := networkLookup_mem hP
    have hST : st_trans cxTq (st_label.out "p" "x" "S") SessionType.tEnd := by
      apply st_trans.intC
      simp [cxTq]
    have hSend : sq_trans (cxTq, ([] : Queue)) (sq_action.send "p" "x" "S") (SessionType.tEnd, ([] : Queue)) :=
      sq_trans.send hST
    have hRecv : sq_trans (T07, [cxRa]) (sq_action.recv "q" "x" "S") (T07, [cxRa, QueueMessage.msg "q" "x" "S"]) :=
      sq_trans.recv
    have hTr : net_trans N' (net_label.τ_comm "q" "p" "x" "S")
        ((N'.replace "q" (SessionType.tEnd, [])).replace "p" (T07, [cxRa, QueueMessage.msg "q" "x" "S"])) :=
      net_trans.comm (by decide) hSend hRecv hMemQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S3: has deq ra
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemP : (("p", (T07, [cxQx, cxRa])) ∈ N') := networkLookup_mem hP
    have hST : st_trans T07 (st_label.inp "r" "a" "S") CoT_branch := by
      apply st_trans.tRec
      show st_trans T07unfold (st_label.inp "r" "a" "S") CoT_branch
      unfold T07unfold
      apply st_trans.extC
      simp
    have hDeq : Queue.dequeue [cxQx, cxRa] (QueueMessage.msg "r" "a" "S") = some [cxQx] := by decide
    have hSQ : sq_trans (T07, [cxQx, cxRa]) (sq_action.dequeue "r" "a" "S") (CoT_branch, [cxQx]) :=
      sq_trans.dequeue hST hDeq
    have hTr : net_trans N' (net_label.τ_dequeue "p" "r" "a" "S") (N'.replace "p" (CoT_branch, [cxQx])) :=
      net_trans.dequeue hSQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S4: has comm q->p
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemQ : (("q", (cxTq, ([] : Queue))) ∈ N') := networkLookup_mem hQ
    have hMemP : (("p", (CoT_branch, ([] : Queue))) ∈ N') := networkLookup_mem hP
    have hST : st_trans cxTq (st_label.out "p" "x" "S") SessionType.tEnd := by
      apply st_trans.intC
      simp [cxTq]
    have hSend : sq_trans (cxTq, ([] : Queue)) (sq_action.send "p" "x" "S") (SessionType.tEnd, ([] : Queue)) :=
      sq_trans.send hST
    have hRecv : sq_trans (CoT_branch, ([] : Queue)) (sq_action.recv "q" "x" "S") (CoT_branch, [QueueMessage.msg "q" "x" "S"]) :=
      sq_trans.recv
    have hTr : net_trans N' (net_label.τ_comm "q" "p" "x" "S")
        ((N'.replace "q" (SessionType.tEnd, [])).replace "p" (CoT_branch, [QueueMessage.msg "q" "x" "S"])) :=
      net_trans.comm (by decide) hSend hRecv hMemQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S5: has deq ra
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemP : (("p", (T07, [cxRa, cxQx])) ∈ N') := networkLookup_mem hP
    have hST : st_trans T07 (st_label.inp "r" "a" "S") CoT_branch := by
      apply st_trans.tRec
      show st_trans T07unfold (st_label.inp "r" "a" "S") CoT_branch
      unfold T07unfold
      apply st_trans.extC
      simp
    have hDeq : Queue.dequeue [cxRa, cxQx] (QueueMessage.msg "r" "a" "S") = some [cxQx] := by decide
    have hSQ : sq_trans (T07, [cxRa, cxQx]) (sq_action.dequeue "r" "a" "S") (CoT_branch, [cxQx]) :=
      sq_trans.dequeue hST hDeq
    have hTr : net_trans N' (net_label.τ_dequeue "p" "r" "a" "S") (N'.replace "p" (CoT_branch, [cxQx])) :=
      net_trans.dequeue hSQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S6: has deq qx
    obtain ⟨hP, hQ, hR⟩ := h
    have hMemP : (("p", (CoT_branch, [cxQx])) ∈ N') := networkLookup_mem hP
    have hST : st_trans CoT_branch (st_label.inp "q" "x" "S") SessionType.tEnd := by
      unfold CoT_branch
      apply st_trans.extC
      simp
    have hDeq : Queue.dequeue [cxQx] (QueueMessage.msg "q" "x" "S") = some ([] : Queue) := by decide
    have hSQ : sq_trans (CoT_branch, [cxQx]) (sq_action.dequeue "q" "x" "S") (SessionType.tEnd, []) :=
      sq_trans.dequeue hST hDeq
    have hTr : net_trans N' (net_label.τ_dequeue "p" "q" "x" "S") (N'.replace "p" (SessionType.tEnd, [])) :=
      net_trans.dequeue hSQ hMemP
    exact hStuck ⟨_, _, by trivial, hTr⟩
  · -- S7: all empty, no orphans (queues empty => dequeue none)
    obtain ⟨hP, hQ, hR⟩ := h
    -- hmem : (r,(T,Q)) ∈ N', need Q=[] from shape + uniqueness? Actually shape gives lookups, need to show Q empty
    -- r must be p/q/r (via CxInv roles? Need hInv for roles? We have hInv from reachable? Actually we have hInv? No, we have hShape + hStar, need hInv for roles? We have hInv via cxInv_reachable hStar, but we didn't have it in this branch? We have hWF/hInv from outer? Actually this theorem's premises: hStar, hStuck, hmem, hQdeq. We have hShape via reachable, hWF via reachable, hInv via reachable? We didn't include hInv in this proof yet. Need to get hInv for roles.
    have hInvN := cxInv_reachable hStar
    obtain ⟨hPinv, hQinv, hRinv, hRoles, hNoP⟩ := hInvN
    have hRrole : r = "p" ∨ r = "q" ∨ r = "r" := hRoles _ hmem
    rcases hRrole with rfl | rfl | rfl
    · -- r=p: lookup p = (tEnd,[]), uniqueness gives Q=[]
      have hMemP : (("p", (SessionType.tEnd, ([] : Queue))) ∈ N') := networkLookup_mem hP
      have hEq := network_mem_unique hWF hmem hMemP
      have hQ0 : Q = [] := congrArg Prod.snd hEq
      rw [hQ0] at hQdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
    · have hMemQ : (("q", (SessionType.tEnd, ([] : Queue))) ∈ N') := networkLookup_mem hQ
      have hEq := network_mem_unique hWF hmem hMemQ
      have hQ0 : Q = [] := congrArg Prod.snd hEq
      rw [hQ0] at hQdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQdeq
    · have hMemR : (("r", (SessionType.tEnd, ([] : Queue))) ∈ N') := networkLookup_mem hR
      have hEq := network_mem_unique hWF hmem hMemR
      have hQ0 : Q = [] := congrArg Prod.snd hEq
      rw [hQ0] at hQdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQdeq

theorem cxN_outputLive : IsOutputLiveNetwork cxN :=
  ⟨cxN_outputLiveInf, cxN_noOrphan_stuck⟩

end CxStuck


end CxOutputLive

/-- Empty queues fold to the source types themselves. -/
theorem fold_nil (T : SessionType) :
    monitor_fold_val_partial (T, []) = some T := by
  have hEx : ∃ T', monitor_fold (T, []) T' := ⟨T, rfl⟩
  have hfold : ∀ M, monitor_fold (T, []) M → M = T := by
    intro M h
    unfold monitor_fold monitor_fold_aux at h
    exact h
  unfold monitor_fold_val_partial
  split
  · next h => exact congrArg some (hfold _ (Classical.choose_spec h))
  · next h => exact absurd hEx h

/-- The consistent instrumentation of `cxN` is defined. -/
theorem cxN_consistent : consistentInstrumentation cxN = some cxMN := by
  simp only [consistentInstrumentation, cxN, cxMN, fold_nil]

/-- `q` can send `x` to `p` in the unmonitored network. -/
theorem cxN_comm :
    net_trans cxN (net_label.τ_comm "q" "p" "x" "S")
      ((cxN.replace "q" (SessionType.tEnd, [])).replace "p"
        (T07, [QueueMessage.msg "q" "x" "S"])) := by
  have hmem_s : (("p", "x", "S", SessionType.tEnd) : Role × Lab × DataSort × SessionType) ∈
      [("p", "x", "S", SessionType.tEnd)] := by simp
  have hsend : sq_trans (cxTq, []) (sq_action.send "p" "x" "S") ((SessionType.tEnd, [])) :=
    sq_trans.send (st_trans.intC hmem_s)
  have hrecv : sq_trans (T07, []) (sq_action.recv "q" "x" "S")
      (T07, [QueueMessage.msg "q" "x" "S"]) :=
    sq_trans.recv
  have hmem_p : (("q", (cxTq, [])) ∈ cxN) := by simp [cxN]
  have hmem_q : (("p", (T07, [])) ∈ cxN) := by simp [cxN]
  exact net_trans.comm (by decide : ("q" : Role) ≠ "p") hsend hrecv hmem_p hmem_q

/-- Any monitored `q → p` communication for `x` needs an inductive accept of
    `q?x` from `T07` — the step the finite soundness proof would have to fill. -/
theorem monitored_x_comm_needs_accept {MN' : MonitoredNetwork}
    (hTr : mon_net_trans cxMN (mon_net_label.τ_comm "q" "p" "x" "S") MN') :
    ∃ V, mon_tr_yes T07 (ext_tag.recv "q" "x" "S") V := by
  generalize hL : (mon_net_label.τ_comm "q" "p" "x" "S") = lbl at hTr
  cases hTr with
  | lift h _ =>
    cases h <;> simp_all [mon_net_label.ofmon_label]
  | comm _ h_recv _ hmem_q =>
    cases hL
    simp only [cxMN, List.mem_cons, List.mem_nil_iff, or_false] at hmem_q
    rcases hmem_q with h | h | h
    · cases h
      cases h_recv with
      | good_recv hSQ hYes => exact ⟨_, hYes⟩
    · have hne : ("p" : Role) ≠ "q" := by decide
      exact absurd (congrArg Prod.fst h) hne
    · have hne : ("p" : Role) ≠ "r" := by decide
      exact absurd (congrArg Prod.fst h) hne

/-- The monitored network admits no `q → p` `x`-communication: any such step
    would need an inductive `q?x` acceptance from `T07`, which does not exist. -/
theorem cxMN_no_tau_comm_qp :
    ¬ ∃ MN', mon_net_trans cxMN (mon_net_label.τ_comm "q" "p" "x" "S") MN' := by
  rintro ⟨MN', hTr⟩
  obtain ⟨V, hYes⟩ := monitored_x_comm_needs_accept hTr
  exact T07_no_inductive_x_any ⟨V, hYes⟩

/-- `cxN` and its consistent instrumentation are not internally bisimilar:
    the network can do `q → p` `x` (`cxN_comm`), which the monitored network
    cannot match. -/
theorem cx_not_bisimilar : ¬ InternallyBisimilar cxN cxMN := by
  rintro ⟨R, hR0, hBis⟩
  have hInt : is_internal_net_label (net_label.τ_comm "q" "p" "x" "S") := by
    trivial
  obtain ⟨MN', μ₂, _, hMap, hTr2, _⟩ :=
    (hBis hR0 (net_label.τ_comm "q" "p" "x" "S") hInt).1 _ cxN_comm
  have hMap' : μ₂ = mon_net_label.τ_comm "q" "p" "x" "S" := by
    simpa [netLabelToMonNetLabel] using hMap.symm
  subst hMap'
  exact cxMN_no_tau_comm_qp ⟨_, hTr2⟩

/-- Main statement: all non-`Prunable` hypotheses can hold while `Prunable`
    fails and the needed inductive `x`-acceptance is the coinductive-only one.
    Strengthened to output-liveness + half-duplexity (same `cxN` already
    satisfies both), and the network and its consistent instrumentation are
    not internally bisimilar. -/
theorem monitor_soundness_needs_prunable :
    ∃ (N : Network) (MN : MonitoredNetwork),
      N.WellFormed ∧ N.NoSelf ∧ N.RolesPresent ∧
      consistentInstrumentation N = some MN ∧
      ¬ Network.Prunable N ∧
      IsOutputLiveNetwork N ∧ IsHalfDuplex N ∧
      ¬ InternallyBisimilar N MN := by
  refine ⟨cxN, cxMN, cxN_wellformed, cxN_noself, cxN_rolespresent,
    cxN_consistent, ?_, cxN_outputLive, cxN_halfDuplex, cx_not_bisimilar⟩
  intro hPrune
  have hmem : (("p", (T07, [])) ∈ cxN) := by simp [cxN]
  exact T07_not_prunable (hPrune _ hmem)
