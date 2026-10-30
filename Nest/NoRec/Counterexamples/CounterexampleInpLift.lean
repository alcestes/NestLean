import Nest.SessionUtils

open Cslib

/-
Counterexample: `stuck_witness_inp_lift` (`Nest.StuckWitness`) and
`fresh_dequeue_never_enabled_at` are FALSE — queue absorption can
PRUNE the distinguished branch, a case the advertised/HD case split misses.

Root instance: `Tq = externalChoice "p" [("a","sa",Aa), ("b","sb",tEnd)]`
with `Aa = externalChoice "r" [("x","sx",tEnd)]`, prefix `Qq = [msg "r"]`
(fresh for `"p"`), distinguished `msg = msg "p" "b" "sb"`.
- `hEnc`: `Qq` absorbs to `M = externalChoice "p" [("a","sa",tEnd)]`
  (the `("b","sb")`-branch takes no `recv "r"`, so maximal coverage drops it).
- `hNo`: `M` says no to `recv "p" "b" "sb"` (its only key is `("a","sa")`).
- Yet `st_trans`-input on `("b","sb")` fires and the dequeue scan succeeds past
  the `p`-free prefix — so the distinguished dequeue FIRES while `hNo` holds.

Consequences (all via this instance, `net_trans_star.refl`, no evolution needed):
- `stuck_witness_inp_lift` is false (all its hypotheses hold; its `∃ M'`
  conclusion is `CxInpLiftFalse`).
- `fresh_dequeue_never_enabled_at` is false (add `LxFresh`; the firing step
  is `CxFire`; conclusion is `CxFreshAtFalse`).
- Hence `fresh_dequeue_never_enabled_sound`,
  `stuck_encQueue_dequeue_never_enabled_fresh`, and any never-fire supply
  for `mem_star_of_neverFire` are unprovable
  by this route — the whole `hNo`-preservation chain via lifting is dead.
- The instance is `NoRec` (`LxTqNR_norec`) and fresh (`LxFresh`), so NoRec/freshness
  strengthenings do NOT repair it. What is missing is branch stability: the
  distinguished `("b","sb")`-branch must survive absorption of `Qq` (i.e. the
  session-`hNo` transfer the commented-out `hNo_pushback_to_session` wanted).
- `hHDNi` holds (`LxHD`: only `LxNi`/`LxN1` are τ-reachable, checked pairwise),
  so half-duplex does not repair it either.
- Conversely, consistent instrumentation DOES repair it:
  `CxConsExcluded` proves `¬ ∃ MN, consistentInstrumentation LxNi = some MN`
  (full-queue absorption would force a yes-recv from `LxM` against `LxNo`;
  the prefix-absorption target pins to `LxM` by coverage, `LxKeptPin`).
  So the misalignment leveraged here is exactly what consistency forbids —
  and `stuck_witness_inp_lift_norec` shows consistency
  collapses the lifting problem to determinism.

Status: evidence file, NOT imported in `Nest.lean` (unresolved refutation).
-/

def LxAa : SessionType :=
  SessionType.externalChoice "r" [("x", "sx", SessionType.tEnd)]

def LxTq : SessionType :=
  SessionType.externalChoice "p"
    [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)]

def LxQq : Queue := [QueueMessage.msg "r" "x" "sx"]

def LxMsg : QueueMessage := QueueMessage.msg "p" "b" "sb"

def LxM : SessionType :=
  SessionType.externalChoice "p" [("a", "sa", SessionType.tEnd)]

def LxNi : Network :=
  [("q", (LxTq, LxQq ++ [LxMsg])),
   ("p", (SessionType.tEnd, [])), ("r", (SessionType.tEnd, []))]

def LxN1 : Network :=
  Network.replace LxNi "q" (SessionType.tEnd, LxQq)

/-- `tEnd` admits no receive yes-existential. -/
private lemma t_end_no_exist_recv {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ mon_tr_yes_exist SessionType.tEnd (ext_tag.recv q lab S) T' := by
  intro h
  cases h with
  | base hb => cases hb

/-- The `("a","sa")`-branch absorbs the prefix. -/
private lemma LxAaRecv : mon_tr_yes_exist LxAa (ext_tag.recv "r" "x" "sx") SessionType.tEnd := by
  unfold LxAa
  apply mon_tr_yes_exist.base
  apply mon_tr_yes_base.extC
  · simp
  · simp

/-- `tEnd` takes no `st_trans` step. -/
private lemma st_trans_t_end_absurd {α : st_label} {T' : SessionType} :
    ¬ st_trans SessionType.tEnd α T' := by
  intro h
  cases h

/-- `LxTq` takes no output step (external choice). -/
private lemma LxTqOutAbsurd {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ st_trans LxTq (st_label.out p lab S) T' := by
  intro h
  cases h

/-- Any nonempty kept-list for the `Aa`-absorption yields a `tEnd`
    subderivation — impossible. (The only source branch is `(x,sx,tEnd)`.) -/
private lemma LxAaKeptContra {kept' : List (Lab × DataSort × SessionType)}
    (hne2 : kept' ≠ [])
    (hkey' : ∀ (l : Lab) (s : DataSort) (T1 : SessionType), (l, s, T1) ∈ kept' →
      ∃ T0, (l, s, T0) ∈ [("x", "sx", SessionType.tEnd)])
    (hall' : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ [("x", "sx", SessionType.tEnd)] → (l, s, T1) ∈ kept' →
        mon_tr_yes_exist T0 (ext_tag.recv "r" "x" "sx") T1) :
    False := by
  match kept', hne2 with
  | [], h => exact absurd rfl h
  | k :: tl, _ =>
    obtain ⟨l, s, T1⟩ := k
    have hk : (l, s, T1) ∈ (l, s, T1) :: tl := by simp
    obtain ⟨T0, hT0⟩ := hkey' l s T1 hk
    simp at hT0
    rcases hT0 with ⟨rfl, rfl, rfl⟩
    exact absurd (hall' _ _ _ _ (by simp) hk) t_end_no_exist_recv

/-- `hEnc`: the prefix absorbs to `LxM`, pruning the `("b","sb")`-branch. -/
lemma LxEnc : monitor_fold (LxTq, LxQq) LxM := by
  have hne : [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] ≠ [] ∧
      [("a", "sa", SessionType.tEnd)] ≠ [] := by simp [LxTq, LxM]
  have hneq : "r" ≠ "p" := by decide
  have hkept : LxM = SessionType.externalChoice "p"
      [("a", "sa", SessionType.tEnd)] := rfl
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] →
      (l, s, T1) ∈ [("a", "sa", SessionType.tEnd)] →
        mon_tr_yes_exist T0 (ext_tag.recv "r" "x" "sx") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp at hmemK
      rcases hmemK with ⟨rfl, rfl, rfl⟩
      exact LxAaRecv
    · simp at hmemK
  have hnodup : List.Nodup (List.map (fun x : Lab × DataSort × SessionType => x.1)
      [("a", "sa", SessionType.tEnd)]) := by simp [LxM]
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ [("a", "sa", SessionType.tEnd)] →
        ∃ T0, (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] := by
    intro l s T1 hmemK
    simp at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩
    exact ⟨LxAa, by simp⟩
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)])
      (hmemK : (l, s, T1) ∈ [("a", "sa", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "r" "x" "sx") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp at hmemK
      rcases hmemK with ⟨rfl, rfl, rfl⟩
      cases hsub with
      | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
      | pfxExt hne' hneq' hkept' hall' hnodup' hkey' =>
        exact absurd (LxAaKeptContra hne'.2 hkey' hall') id
    · simp at hmemK
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "r" "x" "sx") T1) →
        ∃ T1, (l, s, T1) ∈ [("a", "sa", SessionType.tEnd)] := by
    intro l s T0 hmemB hacc
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨SessionType.tEnd, by simp⟩
    · obtain ⟨T1, hT1⟩ := hacc
      exact absurd hT1 t_end_no_exist_recv
  have horder : List.Sublist
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        [("a", "sa", SessionType.tEnd)])
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)]) := by decide
  unfold monitor_fold monitor_fold_aux LxQq
  refine ⟨LxM, ?_, rfl⟩
  exact ⟨@mon_tr_yes_exist.pfxExt "p"
      [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)]
      [("a", "sa", SessionType.tEnd)] "r" "x" "sx" LxM hne hneq hkept
      hall hnodup hkey,
    @mon_tr_yes_max_deriv.pfxExt "p"
      [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)]
      [("a", "sa", SessionType.tEnd)] "r" "x" "sx" LxM hne hneq hkept
      hall hnodup hkey hallMax hcover horder⟩

/-- `hNo`: `LxM` says no to the distinguished receive (only key `("a","sa")`). -/
lemma LxNo : ∀ M', ¬ mon_tr_yes LxM (ext_tag.recv "p" "b" "sb") M' := by
  intro M' h
  rcases h with ⟨hE, _⟩
  cases hE with
  | base hb =>
    cases hb with
    | extC _ hmem =>
      simp at hmem
  | pfxExt _ hneq _ _ _ _ => exact absurd rfl hneq

/-- The distinguished input fires at the session. -/
lemma LxST : st_trans LxTq (st_label.inp "p" "b" "sb") SessionType.tEnd := by
  apply st_trans.extC
  simp [LxTq]

/-- Queue membership in a single-message queue pins the message. -/
private lemma queue_mem_singleton {m a : QueueMessage} (h : QueueMem m [a]) : m = a := by
  cases h with
  | head => rfl
  | tail h' => cases h'

/-- Queue membership in a two-message queue splits. -/
private lemma queue_mem_pair {m a b : QueueMessage} (h : QueueMem m [a, b]) : m = a ∨ m = b := by
  cases h with
  | head => exact Or.inl rfl
  | tail h' =>
    cases h' with
    | head => exact Or.inr rfl
    | tail h'' => cases h''

/-- The dequeue scan succeeds past the `p`-free prefix. -/
lemma LxDeq : (LxQq ++ [LxMsg]).dequeue (QueueMessage.msg "p" "b" "sb") = some LxQq := by
  have hrp : ("r" : Role) ≠ "p" := by decide
  have hmsg : QueueMessage.msg "r" "x" "sx" ≠ QueueMessage.msg "p" "b" "sb" := by
    intro h
    injection h with h1 _ _
    exact hrp h1
  show Queue.dequeue.go [] [QueueMessage.msg "r" "x" "sx", QueueMessage.msg "p" "b" "sb"]
    (QueueMessage.msg "p" "b" "sb") = some [QueueMessage.msg "r" "x" "sx"]
  unfold Queue.dequeue.go
  rw [if_neg hmsg, if_neg hrp]
  unfold Queue.dequeue.go
  rw [if_pos rfl]
  rfl

/-- Freshness holds (`"r" ≠ "p"`). -/
lemma LxFresh : ¬ QueueContainsFrom LxQq "p" := by
  rintro ⟨lab, S, hm⟩
  unfold LxQq at hm
  have heq := queue_mem_singleton hm
  simp at heq

/-- The instance is recursion-free (NoRec strengthenings fall too). -/
lemma LxTqNR_norec : LxTq.NoRec := by
  apply SessionType.NoRec.externalChoice
  intro x hx
  unfold LxTq at hx
  simp at hx
  rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · apply SessionType.NoRec.externalChoice
    intro y hy
    unfold LxAa at hy
    simp at hy
    rcases hy with ⟨rfl, rfl, rfl⟩
    exact SessionType.NoRec.end
  · exact SessionType.NoRec.end

private lemma LxAaWF : LxAa.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice
    · decide
    · decide
    · intro x hx
      unfold LxAa at hx
      simp at hx
      rcases hx with ⟨rfl, rfl, rfl⟩
      exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.externalChoice
    intro x hx
    unfold LxAa at hx
    simp at hx
    rcases hx with ⟨rfl, rfl, rfl⟩
    exact SessionType.Contractive.end

lemma LxTqWF : LxTq.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice
    · decide
    · decide
    · intro x hx
      unfold LxTq at hx
      simp at hx
      rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact LxAaWF.1
      · exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.externalChoice
    intro x hx
    unfold LxTq at hx
    simp at hx
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact LxAaWF.2.2
    · exact SessionType.Contractive.end

private lemma t_end_wf : SessionType.tEnd.WellFormed := by
  refine ⟨SessionType.NoDupl.end, ?_, SessionType.Contractive.end⟩
  unfold SessionType.IsClosed
  decide

lemma LxMemNi : ("q", (LxTq, LxQq ++ [LxMsg])) ∈ LxNi := by
  simp [LxNi]

lemma LxNiWF : LxNi.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro x hx
    simp [LxNi] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact LxTqWF
    · exact t_end_wf
    · exact t_end_wf
  · intro q T Q p lab S hmem hQmem
    simp [LxNi] at hmem
    rcases hmem with h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      unfold LxQq LxMsg at hQmem
      simp at hQmem
      rcases hQmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨(SessionType.tEnd, []), by simp [LxNi]⟩
      · exact ⟨(SessionType.tEnd, []), by simp [LxNi]⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp at hQmem
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp at hQmem

/-- Blocked scan: no `("a","sa")`-from-`"p"` message is dequeuable. -/
private lemma hnonePa : (LxQq ++ [LxMsg]).dequeue
    (QueueMessage.msg "p" "a" "sa") = none := by
  have hrp : ("r" : Role) ≠ "p" := by decide
  have hba : ("b" : Lab) ≠ "a" := by decide
  have hmsg1 : QueueMessage.msg "r" "x" "sx" ≠ QueueMessage.msg "p" "a" "sa" := by
    intro h
    injection h with h1 _ _
    exact hrp h1
  have hmsg2 : QueueMessage.msg "p" "b" "sb" ≠ QueueMessage.msg "p" "a" "sa" := by
    intro h
    injection h with _ h2 _
    exact hba h2
  have hsame : (QueueMessage.msg "p" "b" "sb").1 = (QueueMessage.msg "p" "a" "sa").1 := rfl
  show Queue.dequeue.go [] [QueueMessage.msg "r" "x" "sx", QueueMessage.msg "p" "b" "sb"]
    (QueueMessage.msg "p" "a" "sa") = none
  unfold Queue.dequeue.go
  rw [if_neg hmsg1, if_neg hrp]
  unfold Queue.dequeue.go
  rw [if_neg hmsg2, if_pos hsame]

/-- The only τ-step from `LxNi` is the distinguished dequeue, to `LxN1`. -/
private lemma LxStepNi {δ : net_label} {N2 : Network}
    (hInt : is_internal_net_label δ) (hTr : net_trans LxNi δ N2) : N2 = LxN1 := by
  cases δ with
  | io_send _ _ _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ _ _ => simp [is_internal_net_label] at hInt
  | τ_dequeue r p lab S =>
    cases hTr with
    | dequeue hSQ hmem =>
      simp [LxNi] at hmem
      rcases hmem with h | h | h
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST hQ =>
          cases hST with
          | extC hmemB =>
            simp at hmemB
            rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · -- ("a","sa"): scan for a p-message past [r-msg, b-msg] blocks.
              rw [hnonePa] at hQ
              nomatch hQ
            · -- ("b","sb"): the distinguished fire.
              rw [LxDeq] at hQ
              injection hQ with hqq
              subst hqq
              rfl
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST _ => exact absurd hST st_trans_t_end_absurd
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST _ => exact absurd hST st_trans_t_end_absurd
  | τ_comm p q lab S =>
    cases hTr with
    | comm _hne h_send h_recv hmem_p hmem_q =>
      cases h_send with
      | send hST =>
        simp [LxNi] at hmem_p
        rcases hmem_p with h | h | h
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST LxTqOutAbsurd
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST st_trans_t_end_absurd
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST st_trans_t_end_absurd

/-- No τ-step from `LxN1` (all types `tEnd`). -/
private lemma LxStepN1 {δ : net_label} {N2 : Network}
    (hInt : is_internal_net_label δ) (hTr : net_trans LxN1 δ N2) : False := by
  cases δ with
  | io_send _ _ _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ _ _ => simp [is_internal_net_label] at hInt
  | τ_dequeue r p lab S =>
    cases hTr with
    | dequeue hSQ hmem =>
      simp [LxN1, Network.replace, LxNi] at hmem
      rcases hmem with h | h | h
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST _ => exact absurd hST st_trans_t_end_absurd
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST _ => exact absurd hST st_trans_t_end_absurd
      · rcases h with ⟨rfl, rfl, rfl⟩
        cases hSQ with
        | dequeue hST _ => exact absurd hST st_trans_t_end_absurd
  | τ_comm p q lab S =>
    cases hTr with
    | comm _hne h_send h_recv hmem_p hmem_q =>
      cases h_send with
      | send hST =>
        simp [LxN1, Network.replace, LxNi] at hmem_p
        rcases hmem_p with h | h | h
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST st_trans_t_end_absurd
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST st_trans_t_end_absurd
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact absurd hST st_trans_t_end_absurd

/-- τ-reachable states from `LxNi` are exactly `LxNi` and `LxN1`
    (conjunction induction: the mid-state of a step from `LxNi` is `LxN1`,
    whose futures stay `LxN1`). -/
private lemma LxReachAux {A B : Network} (h : net_trans_star A B) :
    (A = LxNi → B = LxNi ∨ B = LxN1) ∧ (A = LxN1 → B = LxN1) := by
  induction h with
  | refl =>
    refine ⟨?_, ?_⟩
    · intro hA
      subst hA
      exact Or.inl rfl
    · intro hA
      subst hA
      exact rfl
  | step hInt hTr hStar ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · intro hA
      subst hA
      have hM := LxStepNi hInt hTr
      subst hM
      exact Or.inr (ih2 rfl)
    · intro hA
      subst hA
      exact (LxStepN1 hInt hTr).elim

lemma LxReach : ∀ {N'}, net_trans_star LxNi N' → N' = LxNi ∨ N' = LxN1 := by
  intro N' h
  exact (LxReachAux h).1 rfl

/-- Pin the queue of a role in `LxNi`. -/
private lemma LxPinNi {a : Role} {Q : Queue}
    (h : NetworkHasQueue LxNi a Q) :
    (a = "q" ∧ Q = LxQq ++ [LxMsg]) ∨ (a = "p" ∧ Q = []) ∨ (a = "r" ∧ Q = []) := by
  obtain ⟨T, hmem⟩ := h
  simp [LxNi] at hmem
  rcases hmem with h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Pin the queue of a role in `LxN1`. -/
private lemma LxPinN1 {a : Role} {Q : Queue}
    (h : NetworkHasQueue LxN1 a Q) :
    (a = "q" ∧ Q = LxQq) ∨ (a = "p" ∧ Q = []) ∨ (a = "r" ∧ Q = []) := by
  obtain ⟨T, hmem⟩ := h
  simp [LxN1, Network.replace, LxNi] at hmem
  rcases hmem with h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private lemma noContainsNil {r : Role} : ¬ QueueContainsFrom ([] : Queue) r := by
  rintro ⟨_, _, h⟩
  cases h

/-- Half-duplexity holds (both reachable states checked pairwise). -/
lemma LxHD : IsHalfDuplex LxNi := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  rcases LxReach hStar with rfl | rfl
  · rcases LxPinNi hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases LxPinNi hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- q/q: q's queue has no q-message.
      unfold LxQq LxMsg at hCq
      obtain ⟨lab, S, hm⟩ := hCq
      rcases queue_mem_pair hm with h | h <;> simp at h
    · exact absurd hCq noContainsNil
    · exact absurd hCq noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · rcases LxPinN1 hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases LxPinN1 hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- q/q: [r-msg] has no q-message.
      unfold LxQq at hCq
      obtain ⟨lab, S, hm⟩ := hCq
      have heq := queue_mem_singleton hm
      simp at heq
    · exact absurd hCq noContainsNil
    · exact absurd hCq noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil

/-- The distinguished dequeue fires. -/
lemma CxFire : net_trans LxNi (net_label.τ_dequeue "q" "p" "b" "sb") LxN1 := by
  apply net_trans.dequeue _ LxMemNi
  apply sq_trans.dequeue LxST
  exact LxDeq

/-- `stuck_witness_inp_lift` conclusion, instantiated: false (`LxNo`). -/
theorem CxInpLiftFalse :
    (∃ M', mon_tr_yes LxM (ext_tag.recv "p" "b" "sb") M') → False := by
  rintro ⟨M', h⟩
  exact LxNo M' h

/-- `fresh_dequeue_never_enabled_at` conclusion, instantiated: false (`CxFire`). -/
theorem CxFreshAtFalse :
    (∀ N'', ¬ net_trans LxNi (net_label.τ_dequeue "q" "p" "b" "sb") N'') → False := by
  intro h
  exact h LxN1 CxFire

/-! ## Consistency excludes the counterexample (self-contained).

`consistentInstrumentation LxNi = some _` would force full-queue absorption
(`encQueueValPartial_some_iff`, `Basic`), which unfolds directly (both queues
are concrete singletons — no sequence machinery needed) into a prefix
yes-step plus a distinguished yes-step from the prefix target; coverage pins
that target to `LxM` (`LxKeptPin`: the only acceptable branch is `(a,sa)`,
to `tEnd`), yielding a yes-recv from `LxM` against `LxNo`. So the
misalignment the counterexample leverages (prefix absorbs, full queue does
not) is exactly what consistent instrumentation forbids. Everything here is
`Basic`-only, keeping this evidence independent of the proof files. -/

/-- Base-case pin: a base `recv "r" "x" "sx"`-step of `LxAa` selects
    `("x","sx",tEnd)`. -/
private lemma LxAaBaseTarget {T1 : SessionType}
    (hb : mon_tr_yes_base LxAa (ext_tag.recv "r" "x" "sx") T1) :
    T1 = SessionType.tEnd := by
  cases hb with
  | extC _ hmem =>
    simp at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    rfl

/-- The `Aa`-absorption target is pinned to `tEnd` (base pins by
    branch-membership; any `pfxExt` subderivation starts from `tEnd`,
    via `LxAaKeptContra`). -/
private lemma LxAaAbsTarget {T1 : SessionType}
    (h : mon_tr_yes_exist LxAa (ext_tag.recv "r" "x" "sx") T1) :
    T1 = SessionType.tEnd := by
  cases h with
  | base hb => exact LxAaBaseTarget hb
  | pfxExt hne' hneq' hkept' hall' hnodup' hkey' =>
    exact absurd (LxAaKeptContra hne'.2 hkey' hall') id

/-- Base-case contradiction: a base step of `LxTq` cannot carry a tag whose
    role differs from `"p"` (the `γ` binder keeps dependent elimination from
    seeing the literal conflict; `cases` would otherwise fail instead of
    pruning). -/
private lemma LxBaseContra {U1 : SessionType} {γ : ext_tag}
    (hγ : ext_tag.recv "r" "x" "sx" = γ)
    (hb : mon_tr_yes_base LxTq γ U1) : False := by
  cases hb with
  | extC _ _ =>
    simp at hγ

/-- Any `recv "r" "x" "sx"` kept-list of `LxTq`'s branches is
    `[("a","sa",tEnd)]`: every element equals `(a,sa,tEnd)` (`(a,sa)` absorbs
    to `tEnd` by `LxAaAbsTarget`; `(b,sb)` is `tEnd` and accepts nothing),
    and nonemptiness + nodup cap the length at one. Maximality is not
    needed — only the existential `hall`/`hkey`. -/
private lemma LxKeptPin {k : List (Lab × DataSort × SessionType)}
    (hne : [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] ≠ [] ∧ k ≠ [])
    (hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)] →
      (l, s, T1) ∈ k → mon_tr_yes_exist T0 (ext_tag.recv "r" "x" "sx") T1)
    (hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType), (l, s, T1) ∈ k →
      ∃ T0, (l, s, T0) ∈ [("a", "sa", LxAa), ("b", "sb", SessionType.tEnd)])
    (hnodup : List.Nodup (List.map (fun x : Lab × DataSort × SessionType => x.1) k)) :
    k = [("a", "sa", SessionType.tEnd)] := by
  have hall1 : ∀ x ∈ k, x = ("a", "sa", SessionType.tEnd) := by
    intro x hx
    obtain ⟨l, s, T1⟩ := x
    obtain ⟨T0, hT0⟩ := hkey l s T1 hx
    simp at hT0
    rcases hT0 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hTeq := LxAaAbsTarget (hall _ _ _ _ (by simp) hx)
      subst hTeq
      rfl
    · exact absurd (hall _ _ _ _ (by simp) hx) t_end_no_exist_recv
  have h0 : k ≠ [] := hne.2
  obtain ⟨hd, tl, hdtl⟩ := List.exists_cons_of_ne_nil h0
  have hmhd : hd ∈ k := by rw [hdtl]; simp
  have hhd := hall1 hd hmhd
  subst hhd
  rcases tl with _ | ⟨hd2, tl2⟩
  · exact hdtl
  · exfalso
    have hm2 : hd2 ∈ k := by rw [hdtl]; simp
    have heq2 := hall1 hd2 hm2
    subst heq2
    rw [hdtl] at hnodup
    simp at hnodup

/-- Any maximal `recv "r" "x" "sx"`-absorption of `LxTq` lands at `LxM`
    (existential pinning suffices — maximality is not needed here). -/
private lemma LxAbsUnique {U1 : SessionType}
    (h : mon_tr_yes LxTq (ext_tag.recv "r" "x" "sx") U1) : U1 = LxM := by
  rcases h with ⟨hE, _⟩
  unfold LxTq at hE
  cases hE with
  | base hb => exact (LxBaseContra rfl hb).elim
  | pfxExt hne _ hkept hall hnodup hkey =>
    have hkEq := LxKeptPin hne hall hkey hnodup
    have hLM : SessionType.externalChoice "p"
        [("a", "sa", SessionType.tEnd)] = LxM := rfl
    rw [hkept, hkEq, hLM]

/-- Consistent instrumentation is impossible here: full-queue absorption
    unfolds (concrete singleton queues) into a prefix yes-step plus a
    distinguished yes-step from the prefix target, which `LxAbsUnique` pins
    to `LxM` — against `LxNo`. -/
theorem CxConsExcluded : ¬ ∃ MN, consistentInstrumentation LxNi = some MN := by
  rintro ⟨MN, hMN⟩
  have hFullVal : ∃ Mc, monitor_fold_val_partial (LxTq, LxQq ++ [LxMsg]) = some Mc :=
    (consistentInstrumentation_some_iff LxNi).mp ⟨MN, hMN⟩ _ LxMemNi
  have hEncFull : ∃ Mfull, monitor_fold (LxTq, LxQq ++ [LxMsg]) Mfull :=
    (encQueueValPartial_some_iff _).mp hFullVal
  obtain ⟨Mfull, hEncFull⟩ := hEncFull
  have hAux : ∃ U1, mon_tr_yes LxTq (ext_tag.recv "r" "x" "sx") U1 ∧
      monitor_fold_aux [QueueMessage.msg "p" "b" "sb"] U1 Mfull := hEncFull
  obtain ⟨U1, hYes1, hAux2⟩ := hAux
  have hAux2' : ∃ U2, mon_tr_yes U1 (ext_tag.recv "p" "b" "sb") U2 ∧ Mfull = U2 :=
    hAux2
  obtain ⟨U2, hYes2, _⟩ := hAux2'
  have hU1 : U1 = LxM := LxAbsUnique hYes1
  subst hU1
  exact LxNo U2 hYes2
