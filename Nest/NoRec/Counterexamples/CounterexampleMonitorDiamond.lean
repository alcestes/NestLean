import Nest.SessionUtils
import Nest.NoRec.Counterexamples.ProofUtils

/-!
# Monitor diamond claims: verdicts.

Certified evidence for two diamond claims about `mon_tr_yes` (monitor-yes)
transitions, for nonrec well-formed session types.

## Claim 1 (FALSE as stated)

> If `M --l1--> M' --l2--> M''` and `M --l2--> M'''` with `l1`, `l2`
> involving different roles, then `M''' --l1--> M''`.

Refuted by a send/send witness (`monitor_diamond_false_norec`): with
`M = intChoice [(p,a,M'), (q,b,tEnd)]`, `M' = intChoice [(q,b,tEnd)]`,
`l1 = send p a sa`, `l2 = send q b sb`, all three premises fire by base,
yet `M''' = tEnd` admits no `l1`-step. The two sends involve different
roles (`p ≠ q`), and `M` is nonrec and well-formed.

Remark: the restriction to two receives (`recv p ..` / `recv q ..`, `p ≠ q`)
is ALSO false in general — the Python-model diamond checker finds
`diverge` and `missing-join` witnesses at 3 roles / 2 labels (e.g. seed 4:
`M -recv p b s-> A -recv r a s-> B`, `M -recv r a s-> A2`,
`A2 -recv p b s-> B2 ≠ B`; Lean certification open). Notably, 2-role
fuzzing (13k peaks) and single-label 3-role fuzzing (10k peaks) are
clean, so the failure needs both role- and label-distinguishable
pruning. Only the as-stated general form is certified false here.

## Claim 2 (TRUE)

> In a draining approx-trace, every adjacent speculative+dequeue pair
> `Tᵢ --lᵢ--> Tᵢ₊₁ --lᵢ₊₁--> Tᵢ₊₂` projects to monitor steps and completes
> to a diamond: some `M'` has `Tᵢ --lᵢ₊₁--> M' --lᵢ--> Tᵢ₊₂`.

Proved as `spec_dequeue_monitor_diamond_norec`, stated on the two consecutive
`over_trans` steps (the surrounding drain and its emptiness play no role in
the local diamond — the lemma applies to every such adjacent pair of any
`over_trans_trace`). Proof: both steps lift to maximal monitor firings
(`over_trans_lifts_to_mon_tr_yes`); the dequeue hit lies in the queue while
the spec role is absent from it, so the roles differ and the side label
is off-role; the taken branch fires the side label, hence survives the
maximal filter (`sd_kept_of_acceptable`), giving `M'` via
`sd_maxPfxExt_of_kept_ne_norec`; completion is base on the taken key, pinned by
`mon_tr_yes_target_unique`.

This file is evidence only (built as part of `Nest.lean`); it imports only
`Nest.SessionUtils`.
-/

-- ================================================================
-- Claim 1 refutation: send/send witness.
-- ================================================================

/-- Witness continuation: accepts `send q b sb` into `tEnd`. -/
private def Dia1_M' : SessionType :=
  SessionType.internalChoice [("q", "b", "sb", SessionType.tEnd)]

/-- Witness source: on `send p a sa` goes to `Dia1_M'`; on `send q b sb`
    goes to `tEnd`. -/
private def Dia1_M : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa", Dia1_M'), ("q", "b", "sb", SessionType.tEnd)]

/-- The diamond-refutation witness continuation is recursion-free. -/
private lemma Dia1_M'_NoRec : Dia1_M'.NoRec := by
  unfold Dia1_M'
  apply SessionType.NoRec.internalChoice
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | h
  · exact SessionType.NoRec.end
  · simp at h

/-- The diamond-refutation witness continuation has no duplicate keys. -/
private lemma Dia1_M'_NoDupl : Dia1_M'.NoDupl := by
  unfold Dia1_M'
  apply SessionType.NoDupl.internalChoice
  · decide
  · decide
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | h
    · exact SessionType.NoDupl.end
    · simp at h

/-- The diamond-refutation witness continuation is closed. -/
private lemma Dia1_M'_Closed : Dia1_M'.IsClosed := by
  unfold Dia1_M' SessionType.IsClosed
  decide

/-- The diamond-refutation witness continuation is contractive. -/
private lemma Dia1_M'_Contractive : Dia1_M'.Contractive := by
  unfold Dia1_M'
  apply SessionType.Contractive.internalChoice
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | h
  · exact SessionType.Contractive.end
  · simp at h

/-- The diamond-refutation witness source is recursion-free. -/
private lemma Dia1_M_NoRec : Dia1_M.NoRec := by
  unfold Dia1_M
  apply SessionType.NoRec.internalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact Dia1_M'_NoRec
  · exact SessionType.NoRec.end

/-- The diamond-refutation witness source is well-formed. -/
private lemma Dia1_M_WF : Dia1_M.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Dia1_M
    apply SessionType.NoDupl.internalChoice
    · decide
    · decide
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact Dia1_M'_NoDupl
      · exact SessionType.NoDupl.end
  · unfold Dia1_M SessionType.IsClosed
    decide
  · unfold Dia1_M
    apply SessionType.Contractive.internalChoice
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact Dia1_M'_Contractive
    · exact SessionType.Contractive.end

/-- Base send firing helper (maximal-via-base). -/
private lemma Dia1_send {branches : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
    (huniq : List.Nodup (List.map (λ x => (x.1, x.2.1, x.2.2.1)) branches))
    (hmem : (p, lab, S, T) ∈ branches) :
    mon_tr_yes (SessionType.internalChoice branches) (ext_tag.send p lab S) T := by
  have hb : mon_tr_yes_base (SessionType.internalChoice branches)
      (ext_tag.send p lab S) T :=
    mon_tr_yes_base.intC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `tEnd` admits no maximal yes-transition. -/
private lemma Dia1_tEndNo : ∀ {γ : ext_tag} {T' : SessionType},
    ¬ mon_tr_yes SessionType.tEnd γ T' := by
  intro γ T' h
  rcases h with ⟨hE, _⟩
  cases hE with
  | base hb => cases hb

/-- Certified refutation of Claim 1 as stated. -/
theorem monitor_diamond_false_norec :
    ∃ (M M' M'' M''' : SessionType) (p q : Role) (l1 l2 : ext_tag),
      p ≠ q ∧ l1 = ext_tag.send p "a" "sa" ∧ l2 = ext_tag.send q "b" "sb" ∧
      M.NoRec ∧ M.WellFormed ∧
      mon_tr_yes M l1 M' ∧ mon_tr_yes M' l2 M'' ∧ mon_tr_yes M l2 M''' ∧
      ¬ mon_tr_yes M''' l1 M'' := by
  refine ⟨Dia1_M, Dia1_M', SessionType.tEnd, SessionType.tEnd,
    "p", "q", ext_tag.send "p" "a" "sa", ext_tag.send "q" "b" "sb",
    by decide, rfl, rfl, Dia1_M_NoRec, Dia1_M_WF, ?_, ?_, ?_, ?_⟩
  · -- `M --l1--> M'`: base on the `(p,a,sa)` key.
    apply Dia1_send (p := "p") (lab := "a") (S := "sa") (T := Dia1_M')
    · decide
    · exact List.mem_cons.mpr (Or.inl rfl)
  · -- `M' --l2--> tEnd`: base on the `(q,b,sb)` key.
    apply Dia1_send (p := "q") (lab := "b") (S := "sb") (T := SessionType.tEnd)
    · decide
    · exact List.mem_cons.mpr (Or.inl rfl)
  · -- `M --l2--> tEnd`: base on the `(q,b,sb)` key.
    apply Dia1_send (p := "q") (lab := "b") (S := "sb") (T := SessionType.tEnd)
    · decide
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  · -- Completion fails: `tEnd` admits nothing.
    exact Dia1_tEndNo

-- ================================================================
-- Claim 2 proof: spec+dequeue diamond.
-- ================================================================

/-- A successful scan finds its message in the queue. -/
private lemma sd_go_found : ∀ (seen left : Queue) (msg : QueueMessage) (Q' : Queue),
    Queue.dequeue.go seen left msg = some Q' → msg ∈ seen ++ left := by
  intro seen left
  induction left generalizing seen with
  | nil =>
    intro msg Q' h
    simp [Queue.dequeue.go] at h
  | cons m left' ih =>
    intro msg Q' h
    simp only [Queue.dequeue.go] at h
    by_cases heq : m = msg
    · subst heq
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · simp [heq] at h
      by_cases heq2 : m.1 = msg.1
      · simp [heq2] at h
      · simp [heq2] at h
        have hmem := ih (seen ++ [m]) msg Q' h
        simpa [List.append_assoc] using hmem


/-- Certified proof of Claim 2, local form: a speculative step immediately
    followed by a dequeue step (unpacked `over_trans.specInp` / `over_trans.dequeue`
    components — rewrap with those constructors to apply to trace steps)
    projects to monitor steps and completes to a diamond. The surrounding
    drain and its emptiness play no role: this applies to every such
    adjacent pair of any `over_trans_trace`. -/
theorem spec_dequeue_monitor_diamond_norec
    {T1 T2 T3 : SessionType} {Q Q' : Queue}
    {p q : Role} {lp lq : Lab} {Sp Sq : DataSort}
    (hNR1 : T1.NoRec) (hWF1 : T1.WellFormed)
    (hST1 : st_trans T1 (st_label.inp p lp Sp) T2)
    (hAbs : ∀ m ∈ Q, m.1 ≠ p)
    (hST2 : st_trans T2 (st_label.inp q lq Sq) T3)
    (hQ : Q.dequeue (QueueMessage.msg q lq Sq) = some Q') :
    mon_tr_yes T1 (ext_tag.recv p lp Sp) T2 ∧
    mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 ∧
    ∃ M', mon_tr_yes T1 (ext_tag.recv q lq Sq) M' ∧
      mon_tr_yes M' (ext_tag.recv p lp Sp) T3 := by
  have hWF2 : T2.WellFormed := by
    obtain ⟨branchesW, hTeqW, hmemW⟩ := st_trans_inp_ext_c_of_norec hNR1 hST1
    exact over_trans_preserves_wf (over_trans.specInp hTeqW hmemW hAbs) hWF1
  -- Both steps project to maximal monitor firings.
  have hY1 : mon_tr_yes T1 (ext_tag.recv p lp Sp) T2 :=
    st_trans_inp_imp_mon_tr_yes hST1 hWF1
  have hY2 : mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 :=
    st_trans_inp_imp_mon_tr_yes hST2 hWF2
  -- The dequeued message is in the queue while `p` is absent: roles differ.
  have hmemQ : QueueMessage.msg q lq Sq ∈ Q := by
    have hgo : Queue.dequeue.go [] Q (QueueMessage.msg q lq Sq) = some Q' := hQ
    have hfound := sd_go_found [] Q _ _ hgo
    simpa using hfound
  have hnepq : q ≠ p := by
    have habs := hAbs _ hmemQ
    simpa using habs
  -- The spec source is an external choice on `p`; the taken branch is keyed.
  obtain ⟨branches, hTeq, hmem⟩ := st_trans_inp_ext_c_of_norec hNR1 hST1
  have hNRc : (SessionType.externalChoice p branches).NoRec := by
    rw [← hTeq]
    exact hNR1
  have hNDc : (SessionType.externalChoice p branches).NoDupl := by
    rw [← hTeq]
    exact hWF1.1
  have hClc : (SessionType.externalChoice p branches).IsClosed := by
    rw [← hTeq]
    exact hWF1.2.1
  have hCoc : (SessionType.externalChoice p branches).Contractive := by
    rw [← hTeq]
    exact hWF1.2.2
  have hWF2 : T2.WellFormed :=
    ⟨noDupl_of_mem_extBranches hNDc hmem, isClosed_of_mem_extBranches hClc hmem,
      isContractive_of_mem_extBranches hCoc hmem⟩
  have hpair : List.Nodup
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches) := by
    cases hNDc with
    | externalChoice h_nodup _ _ => exact nodup_of_nodup_labels h_nodup
  -- The taken branch fires the side label, so it survives the maximal filter.
  have hacc : ∃ T'', mon_tr_yes T2 (ext_tag.recv q lq Sq) T'' := ⟨T3, hY2⟩
  obtain ⟨U, hmemK⟩ := sd_kept_of_acceptable (pe := p) hmem hacc
  have hne_kept : extBranchesWithmon_tr_yes p branches q lq Sq
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ [] :=
    List.ne_nil_of_mem hmemK
  have hSide : mon_tr_yes T1 (ext_tag.recv q lq Sq)
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    rw [hTeq]
    exact sd_maxPfxExt_of_kept_ne_norec hNRc hNDc hnepq hne_kept
  -- Completion is base on the taken key, pinned by determinism.
  obtain ⟨T0s, hmem0, hYU⟩ := mem_extBranchesWithmon_tr_yes_recv hmemK
  have hYU' : mon_tr_yes T0s (ext_tag.recv q lq Sq) U := hYU
  have hT0eq : T0s = T2 := unique_target_of_nodup_ext hpair hmem0 hmem
  subst T0s
  have hU : U = T3 := mon_tr_yes_target_unique hWF2 hYU' hY2
  subst U
  have huniqK : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    have hsub : (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        (extBranchesWithmon_tr_yes p branches q lq Sq
          (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))).Sublist
        (List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
          branches.attach) :=
      sd_filterMap_keys_sublist ?hkeyOrd
    have hatt : List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
        branches.attach =
        List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches :=
      List.attach_map_val
        (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
    rw [hatt] at hsub
    exact hsub.nodup hpair
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  have hb : mon_tr_yes_base
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.recv p lp Sp) T3 :=
    mon_tr_yes_base.extC huniqK hmemK
  have hComp : mon_tr_yes
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.recv p lp Sp) T3 :=
    ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
  exact ⟨hY1, hY2, _, hSide, hComp⟩

/-- Accepting branches survive the internal maximal filter. -/
private lemma sd_kept_of_acceptable_int
    {branches : List (Role × Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    {r' : Role} {l' : Lab} {s' : DataSort} {T0' : SessionType}
    (hmemB : (r', l', s', T0') ∈ branches)
    (hacc : ∃ T'', mon_tr_yes T0' (ext_tag.recv q lab S) T'') :
    ∃ T1, (r', l', s', T1) ∈ intBranchesWithmon_tr_yes branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') := by
  unfold intBranchesWithmon_tr_yes
  simp only [List.mem_filterMap]
  refine ⟨hacc.choose, ⟨(r', l', s', T0'), hmemB⟩, List.mem_attach _ _, ?_⟩
  dsimp only
  split
  · next h =>
    cases proof_irrel h hacc
    rfl
  · next hdrop =>
    exact absurd hacc hdrop

/-- Maximal prefix over the full internal filter kept-list. -/
private lemma sd_maxPfxInt_of_kept_ne_norec
    {branches : List (Role × Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    (hNR : (SessionType.internalChoice branches).NoRec)
    (hND : SessionType.NoDupl (SessionType.internalChoice branches))
    (hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈ branches → q ≠ p')
    (hne_kept : intBranchesWithmon_tr_yes branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ []) :
    mon_tr_yes (SessionType.internalChoice branches) (ext_tag.recv q lab S)
      (SessionType.internalChoice (intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
  have htriple : List.Nodup
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
        branches) := by
    cases hND with
    | internalChoice h_nodup _ _ => exact nodup_triple_of_nodup_pair h_nodup
  have hpair : List.Nodup
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
        branches) := by
    cases hND with
    | internalChoice h_nodup _ _ => exact h_nodup
  have hne : branches ≠ [] ∧
      intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ [] :=
    ⟨hND.ne_of_internalChoice, hne_kept⟩
  have hall : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort),
      (r', l', s', T0') ∈ branches →
      (r', l', s', T1) ∈ intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') →
      mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1 := by
    intro T0' T1 r' l' s' hmemB hmemK
    obtain ⟨T0s, hmem0, hY⟩ := mem_intBranchesWithmon_tr_yes_recv hmemK
    obtain ⟨hE, _⟩ := hY
    have hT0eq : T0s = T0' := unique_target_of_nodup_int htriple hmem0 hmemB
    subst hT0eq
    exact hE
  have hNodupKept : List.Nodup ((intBranchesWithmon_tr_yes branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    have hatt : List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
        branches.attach =
        List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
          branches :=
      List.attach_map_val
        (f := fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
    have hsub : (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
        (intBranchesWithmon_tr_yes branches q lab S
          (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))).Sublist
        (List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
          branches.attach) :=
      sd_filterMap_keys_sublist ?hkeyLab
    rw [hatt] at hsub
    exact hsub.nodup hpair
    · intro a ha b hb
      rcases a with ⟨⟨r', l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  have hkey : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (r', l', s', T1) ∈ intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') →
      ∃ T0', (r', l', s', T0') ∈ branches := by
    intro r' l' s' T1 hmemK
    obtain ⟨T0s, hmem0, _⟩ := mem_intBranchesWithmon_tr_yes_recv hmemK
    exact ⟨T0s, hmem0⟩
  have hallMax : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort)
      (hmemB : (r', l', s', T0') ∈ branches)
      (hmemK : (r', l', s', T1) ∈ intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 r' l' s' hmemB hmemK hsub
    obtain ⟨T0s, hmem0, hY⟩ := mem_intBranchesWithmon_tr_yes_recv hmemK
    obtain ⟨hE, hM⟩ := hY
    have hT0eq : T0s = T0' := unique_target_of_nodup_int htriple hmem0 hmemB
    subst hT0eq
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (r', l', s', T0') ∈ branches →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1) →
      ∃ T1, (r', l', s', T1) ∈ intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') := by
    intro r' l' s' T0' hmemB hex
    have hNR0 : T0'.NoRec := noRec_of_mem_intBranches hNR hmemB
    have hND0 : T0'.NoDupl := noDupl_of_mem_intBranches hND hmemB
    obtain ⟨T1', hMax⟩ := acceptable_to_maximal_norec hNR0 hND0 hex
    exact sd_kept_of_acceptable_int hmemB ⟨T1', hMax⟩
  have horder : List.Sublist
      ((intBranchesWithmon_tr_yes branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')).map
        (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
        branches) := by
    have hatt : List.map
        (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1, a.val.2.2.1))
        branches.attach =
        List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
          branches :=
      List.attach_map_val
        (f := fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
    rw [← hatt]
    refine sd_filterMap_keys_sublist ?hkeyOrd
    · intro a ha b hb
      rcases a with ⟨⟨r', l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  exact ⟨mon_tr_yes_exist.pfxInt hne hno rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := hno) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- NoRec send-firing forces an `intC` head (`extC` prunes by tag mismatch,
    `tRec` by `NoRec`). Local copy kept in this file to avoid extra imports. -/
private lemma st_trans_out_int_c_of_norec {T T' : SessionType} {r : Role} {lab : Lab} {S : DataSort}
    (hNR : T.NoRec) (hST : st_trans T (st_label.out r lab S) T') :
    ∃ branches, T = SessionType.internalChoice branches ∧ (r, lab, S, T') ∈ branches := by
  cases hST with
  | intC hmem => exact ⟨_, rfl, hmem⟩
  | tRec h => cases hNR

/-- Send/dequeue diamond (the missing pairwise piece for drain reordering):
    a fresh-send step immediately followed by a dequeue step projects to
    monitor steps and completes to a diamond. Freshness supplies the
    prefix side condition (`q` is in the queue, hence differs from every
    branch sender); the taken send-branch fires the dequeue label, so
    coverage keeps its key and determinism pins the join. -/
theorem send_dequeue_monitor_diamond_norec
    {T1 T2 T3 : SessionType} {Q Q' : Queue}
    {branches : List (Role × Lab × DataSort × SessionType)}
    {p q : Role} {lp lq : Lab} {Sp Sq : DataSort}
    (hNR1 : T1.NoRec) (hWF1 : T1.WellFormed)
    (hEq : T1 = SessionType.internalChoice branches)
    (hST1 : st_trans T1 (st_label.out p lp Sp) T2)
    (hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
    (hST2 : st_trans T2 (st_label.inp q lq Sq) T3)
    (hQ : Q.dequeue (QueueMessage.msg q lq Sq) = some Q') :
    mon_tr_yes T1 (ext_tag.send p lp Sp) T2 ∧
    mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 ∧
    ∃ M', mon_tr_yes T1 (ext_tag.recv q lq Sq) M' ∧
      mon_tr_yes M' (ext_tag.send p lp Sp) T3 := by
  have hY1 : mon_tr_yes T1 (ext_tag.send p lp Sp) T2 :=
    st_trans_out_imp_mon_tr_yes hST1 hWF1
  have hWF2 : T2.WellFormed :=
    over_trans_preserves_wf (over_trans.sendFresh hEq hST1 hFresh) hWF1
  have hY2 : mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 :=
    st_trans_inp_imp_mon_tr_yes hST2 hWF2
  have hmemQ : QueueMessage.msg q lq Sq ∈ Q := by
    have hgo : Queue.dequeue.go [] Q (QueueMessage.msg q lq Sq) = some Q' := hQ
    have hfound := sd_go_found [] Q _ _ hgo
    simpa using hfound
  obtain ⟨branches', hTeq', hmem'⟩ := st_trans_out_int_c_of_norec hNR1 hST1
  have hBeq : branches' = branches := by
    rw [hTeq'] at hEq
    injection hEq
  subst hBeq
  have hNRc : (SessionType.internalChoice branches').NoRec := by
    rw [← hTeq']
    exact hNR1
  have hNDc : (SessionType.internalChoice branches').NoDupl := by
    rw [← hTeq']
    exact hWF1.1
  have htriple : List.Nodup
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
        branches') :=
    hNDc.triple_nodup_of_internalChoice
  have hno : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches' → q ≠ r' := by
    intro r' l' s' U hmemB
    exact hFresh _ _ _ _ hmemB _ hmemQ
  have hacc : ∃ T'', mon_tr_yes T2 (ext_tag.recv q lq Sq) T'' := ⟨T3, hY2⟩
  obtain ⟨U, hmemK⟩ := sd_kept_of_acceptable_int hmem' hacc
  have hne_kept : intBranchesWithmon_tr_yes branches' q lq Sq
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ [] :=
    List.ne_nil_of_mem hmemK
  have hSide : mon_tr_yes (SessionType.internalChoice branches')
      (ext_tag.recv q lq Sq)
      (SessionType.internalChoice (intBranchesWithmon_tr_yes branches' q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) :=
    sd_maxPfxInt_of_kept_ne_norec hNRc hNDc hno hne_kept
  obtain ⟨T0s, hmem0, hYU⟩ := mem_intBranchesWithmon_tr_yes_recv hmemK
  have hYU' : mon_tr_yes T0s (ext_tag.recv q lq Sq) U := hYU
  have hT0eq : T0s = T2 := unique_target_of_nodup_int htriple hmem0 hmem'
  subst T0s
  have hClc : (SessionType.internalChoice branches').IsClosed := by
    rw [← hTeq']
    exact hWF1.2.1
  have hCoc : (SessionType.internalChoice branches').Contractive := by
    rw [← hTeq']
    exact hWF1.2.2
  have hWF2 : T2.WellFormed :=
    ⟨noDupl_of_mem_intBranches hNDc hmem', isClosed_of_mem_intBranches hClc hmem',
      isContractive_of_mem_intBranches hCoc hmem'⟩
  have hU : U = T3 := mon_tr_yes_target_unique hWF2 hYU' hY2
  subst U
  have huniqK : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      (intBranchesWithmon_tr_yes branches' q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    have hsub : (List.map
        (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
        (intBranchesWithmon_tr_yes branches' q lq Sq
          (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))).Sublist
        (List.map (fun a : {x // x ∈ branches'} => (a.val.1, a.val.2.1, a.val.2.2.1))
          branches'.attach) :=
      sd_filterMap_keys_sublist ?hkeyOrd
    have hatt : List.map
        (fun a : {x // x ∈ branches'} => (a.val.1, a.val.2.1, a.val.2.2.1))
        branches'.attach =
        List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
          branches' :=
      List.attach_map_val
        (f := fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
    rw [hatt] at hsub
    exact hsub.nodup htriple
    · intro a ha b hb
      rcases a with ⟨⟨r', l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  have hb : mon_tr_yes_base
      (SessionType.internalChoice (intBranchesWithmon_tr_yes branches' q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.send p lp Sp) T3 :=
    mon_tr_yes_base.intC huniqK hmemK
  have hTs : T1 = SessionType.internalChoice branches' := hTeq'
  have hSide' : mon_tr_yes T1 (ext_tag.recv q lq Sq)
      (SessionType.internalChoice (intBranchesWithmon_tr_yes branches' q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    rw [hTs]
    exact hSide
  have hComp : mon_tr_yes
      (SessionType.internalChoice (intBranchesWithmon_tr_yes branches' q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.send p lp Sp) T3 :=
    ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
  exact ⟨hY1, hY2, _, hSide', hComp⟩

/-- Dequeue/dequeue diamond for distinct roles: two consecutive `over_trans.dequeue`
    steps (unpacked `st_trans` + scan components — rewrap with `over_trans.dequeue` to
    apply to trace steps) with different message roles project to monitor steps
    and complete to a diamond. Same skeleton as `spec_dequeue_monitor_diamond_norec`:
    the role inequality is now a hypothesis (scans alone don't supply it),
    standing in for the absence-derived `q ≠ p` there. Same-role pairs admit
    no such diamond in general (the swapped on-role label need not even be
    offered — FIFO order matters). -/
theorem deq_dequeue_monitor_diamond_norec
    {T1 T2 T3 : SessionType} {Q Q1 Q' : Queue}
    {p q : Role} {lp lq : Lab} {Sp Sq : DataSort}
    (hNR1 : T1.NoRec) (hWF1 : T1.WellFormed)
    (hST1 : st_trans T1 (st_label.inp p lp Sp) T2)
    (hQ1 : Q.dequeue (QueueMessage.msg p lp Sp) = some Q1)
    (hST2 : st_trans T2 (st_label.inp q lq Sq) T3)
    (_hQ2 : Q1.dequeue (QueueMessage.msg q lq Sq) = some Q')
    (hnepq : q ≠ p) :
    mon_tr_yes T1 (ext_tag.recv p lp Sp) T2 ∧
    mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 ∧
    ∃ M', mon_tr_yes T1 (ext_tag.recv q lq Sq) M' ∧
      mon_tr_yes M' (ext_tag.recv p lp Sp) T3 := by
  -- Note: only the first scan is needed (WF threading); the second is framing
  -- so the lemma applies to adjacent `over_trans.dequeue` pairs as stated.
  have hWF2 : T2.WellFormed := by
    obtain ⟨branchesW, hTeqW, hmemW⟩ := st_trans_inp_ext_c_of_norec hNR1 hST1
    exact over_trans_preserves_wf (over_trans.dequeue hTeqW hmemW hQ1) hWF1
  -- Both steps project to maximal monitor firings.
  have hY1 : mon_tr_yes T1 (ext_tag.recv p lp Sp) T2 :=
    st_trans_inp_imp_mon_tr_yes hST1 hWF1
  have hY2 : mon_tr_yes T2 (ext_tag.recv q lq Sq) T3 :=
    st_trans_inp_imp_mon_tr_yes hST2 hWF2
  -- The first source is an external choice on `p`; the taken branch is keyed.
  obtain ⟨branches, hTeq, hmem⟩ := st_trans_inp_ext_c_of_norec hNR1 hST1
  have hNRc : (SessionType.externalChoice p branches).NoRec := by
    rw [← hTeq]
    exact hNR1
  have hNDc : (SessionType.externalChoice p branches).NoDupl := by
    rw [← hTeq]
    exact hWF1.1
  have hClc : (SessionType.externalChoice p branches).IsClosed := by
    rw [← hTeq]
    exact hWF1.2.1
  have hCoc : (SessionType.externalChoice p branches).Contractive := by
    rw [← hTeq]
    exact hWF1.2.2
  have hWF2 : T2.WellFormed :=
    ⟨noDupl_of_mem_extBranches hNDc hmem, isClosed_of_mem_extBranches hClc hmem,
      isContractive_of_mem_extBranches hCoc hmem⟩
  have hpair : List.Nodup
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches) := by
    cases hNDc with
    | externalChoice h_nodup _ _ => exact nodup_of_nodup_labels h_nodup
  -- The taken branch fires the side label, so it survives the maximal filter.
  have hacc : ∃ T'', mon_tr_yes T2 (ext_tag.recv q lq Sq) T'' := ⟨T3, hY2⟩
  obtain ⟨U, hmemK⟩ := sd_kept_of_acceptable (pe := p) hmem hacc
  have hne_kept : extBranchesWithmon_tr_yes p branches q lq Sq
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ [] :=
    List.ne_nil_of_mem hmemK
  have hSide : mon_tr_yes T1 (ext_tag.recv q lq Sq)
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    rw [hTeq]
    exact sd_maxPfxExt_of_kept_ne_norec hNRc hNDc hnepq hne_kept
  -- Completion is base on the taken key, pinned by determinism.
  obtain ⟨T0s, hmem0, hYU⟩ := mem_extBranchesWithmon_tr_yes_recv hmemK
  have hYU' : mon_tr_yes T0s (ext_tag.recv q lq Sq) U := hYU
  have hT0eq : T0s = T2 := unique_target_of_nodup_ext hpair hmem0 hmem
  subst T0s
  have hU : U = T3 := mon_tr_yes_target_unique hWF2 hYU' hY2
  subst U
  have huniqK : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
    have hsub : (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        (extBranchesWithmon_tr_yes p branches q lq Sq
          (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))).Sublist
        (List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
          branches.attach) :=
      sd_filterMap_keys_sublist ?hkeyOrd
    have hatt : List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
        branches.attach =
        List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches :=
      List.attach_map_val
        (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
    rw [hatt] at hsub
    exact hsub.nodup hpair
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  have hb : mon_tr_yes_base
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.recv p lp Sp) T3 :=
    mon_tr_yes_base.extC huniqK hmemK
  have hComp : mon_tr_yes
      (SessionType.externalChoice p (extBranchesWithmon_tr_yes p branches q lq Sq
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')))
      (ext_tag.recv p lp Sp) T3 :=
    ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
  exact ⟨hY1, hY2, _, hSide, hComp⟩
