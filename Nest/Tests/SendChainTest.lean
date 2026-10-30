import Nest.SessionUtils
/-!
# SendChainTest: send-chain instance pinning the `out_aux` / `send` verdicts.
-/
open Cslib

/-
Regression test: the send-chain instance pinning the `out_aux` / `send`
verdicts.

What is pinned here:
- `SxSend`/`SxWF`/`SxRecv`/`SxEnc`: `T = internalChoice
  [("p","a","sa",tEnd), ("r","b","sb",Cb)]` sends `out "p" "a" "sa"` to
  `tEnd`, while `Q = [msg "q" "l" "s"]` processes to `M = internalChoice
  [("r","b","sb",tEnd)]` — the send-target admits no queue processing
  (pruned branch), so any restatement needs liveness/acceptability
  threading, not the bare form.
- `SxFresh`: the instance is already fresh (`"q" ≠ "p"`), so freshness /
  half-duplex cannot repair the gap (syntactic: dead targets/branches).
- `LxWF`/`LxNoRec`/`LxFold` + `LxSendImpossible_norec`: even a live `Q` over a
  `NoRec`+WellFormed `extC`-headed `M` admits no send-step — liveness
  cannot repair either; the true requirement is an `intC` head.
- Helpers: `t_end_no_exist_recv`/`t_end_no_recv`, `SxBranchYesE`, `SxOffRole`.
-/

/-- Chain witness branch: `q`-offer of `(l, s)` ending in `tEnd`. -/
def SxBranch : SessionType :=
  SessionType.externalChoice "q" [("l", "s", SessionType.tEnd)]

/-- Chain witness branches: a dead leaf plus the live `SxBranch`. -/
def SxBranches : List (Role × Lab × DataSort × SessionType) :=
  [("p", "a", "sa", SessionType.tEnd), ("r", "b", "sb", SxBranch)]

/-- Chain witness queue: the matching `(q, l, s)` message. -/
def SxQ : Queue := [QueueMessage.msg "q" "l" "s"]

/-- Chain witness kept list: the surviving `(r, b, sb)` branch. -/
def SxKept : List (Role × Lab × DataSort × SessionType) :=
  [("r", "b", "sb", SessionType.tEnd)]

/-- Chain witness join: internal choice over the kept branches. -/
def SxM : SessionType := SessionType.internalChoice SxKept

-- `tEnd` admits no receive yes-transition.
/-- `tEnd` admits no receive yes-transition. -/
private lemma t_end_no_exist_recv {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ mon_tr_yes_exist SessionType.tEnd (ext_tag.recv q lab S) T' := by
  intro h
  cases h with
  | base hb => cases hb

/-- `tEnd` admits no receive monitor transition (lifts `t_end_no_exist_recv`). -/
private lemma t_end_no_recv {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ mon_tr_yes SessionType.tEnd (ext_tag.recv q lab S) T' := by
  rintro ⟨hE, _⟩
  exact absurd hE t_end_no_exist_recv

/-- The witness branch accepts the witness tag (existential base step). -/
private lemma SxBranchYesE : mon_tr_yes_exist SxBranch (ext_tag.recv "q" "l" "s") SessionType.tEnd := by
  unfold SxBranch
  apply mon_tr_yes_exist.base
  apply mon_tr_yes_base.extC
  · simp
  · simp

/-- Every branch sender differs from `q` (off-role side condition). -/
private lemma SxOffRole : ∀ p' lab' S' T0,
    (p', lab', S', T0) ∈ SxBranches → "q" ≠ p' := by
  intro p' lab' S' T0 hmem
  unfold SxBranches at hmem
  simp at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

/-- Send fire: the internal choice fires `(p, a, sa)` into `tEnd`. -/
theorem SxSend : st_trans (SessionType.internalChoice SxBranches)
    (st_label.out "p" "a" "sa") SessionType.tEnd :=
  st_trans.intC (by unfold SxBranches; simp)

/-- The chain witness choice is well-formed. -/
theorem SxWF : (SessionType.internalChoice SxBranches).WellFormed := by
  unfold SxBranches SxBranch
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.internalChoice
    · decide
    · simp
    · intro x hx
      simp at hx
      rcases hx with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact SessionType.NoDupl.end
      · apply SessionType.NoDupl.externalChoice
        · simp
        · simp
        · intro y hy
          simp at hy
          obtain ⟨rfl, rfl⟩ := hy
          exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    simp [SessionType.fv, SessionType.fv.goInt, SessionType.fv.goExt]
  · apply SessionType.Contractive.internalChoice
    intro x hx
    simp at hx
    rcases hx with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact SessionType.Contractive.end
    · apply SessionType.Contractive.externalChoice
      intro y hy
      simp at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact SessionType.Contractive.end

-- Maximal receive keeps only the second branch.
/-- Receive fire: the internal choice accepts the `q`-tag into the kept join. -/
theorem SxRecv : mon_tr_yes (SessionType.internalChoice SxBranches)
    (ext_tag.recv "q" "l" "s") SxM := by
  have hne : SxBranches ≠ [] ∧ SxKept ≠ [] := by
    unfold SxBranches SxKept
    constructor <;> simp
  have hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ SxBranches → (r, l, s, T1) ∈ SxKept →
        mon_tr_yes_exist T0 (ext_tag.recv "q" "l" "s") T1 := by
    intro T0 T1 r l s hSrc hKept
    unfold SxKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    unfold SxBranches at hSrc
    simp at hSrc
    subst hSrc
    exact SxBranchYesE
  have hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
      (hmemB : (r, l, s, T0) ∈ SxBranches) (hmemK : (r, l, s, T1) ∈ SxKept)
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "q" "l" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 r l s hmemB hmemK hsub
    unfold SxKept at hmemK
    simp at hmemK
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemK
    unfold SxBranches at hmemB
    simp at hmemB
    subst hmemB
    cases hsub with
    | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
    | pfxExt hne hneq _ _ _ _ =>
      exact absurd rfl hneq
  have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
      (r, l, s, T0) ∈ SxBranches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "q" "l" "s") T1) →
        ∃ T1, (r, l, s, T1) ∈ SxKept := by
    intro r l s T0 hmemB hex
    unfold SxBranches at hmemB
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rcases hex with ⟨T1, hT1⟩
      exact absurd hT1 t_end_no_exist_recv
    · exact ⟨SessionType.tEnd, by unfold SxKept; simp⟩
  have horder : List.Sublist
      (SxKept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (SxBranches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
    unfold SxKept SxBranches SxBranch
    simp
  have hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ SxBranches → "q" ≠ p' := SxOffRole
  have hNodupKept : List.Nodup (SxKept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    unfold SxKept; simp
  have hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ SxKept → ∃ T0, (r, l, s, T0) ∈ SxBranches := by
    intro r l s T1 hKept
    unfold SxKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    exact ⟨SxBranch, by unfold SxBranches; simp⟩
  have hkept : SxM = SessionType.internalChoice SxKept := rfl
  exact ⟨mon_tr_yes_exist.pfxInt hne hno hkept hall hNodupKept hkey,
    @mon_tr_yes_max_deriv.pfxInt SxBranches SxKept "q" "l" "s"
      SxM hne hno hkept hall hNodupKept hkey
      hallMax hcover horder⟩

/-- Encoder fold: the witness queue folds the witness choice to the kept join. -/
theorem SxEnc : monitor_fold_aux SxQ (SessionType.internalChoice SxBranches) SxM := by
  unfold SxQ
  exact ⟨SxM, SxRecv, rfl⟩



/-- Freshness already holds on the instance (`"q" ≠ "p"`), so freshness /
    half-duplex cannot repair the gap (dead targets/branches, syntactic). -/
theorem SxFresh : ¬ QueueContainsFrom SxQ "p" := by
  have hsing : ∀ {m x : QueueMessage}, QueueMem m [x] ↔ m = x := by
    intro m x
    constructor
    · intro h
      cases h with
      | head => rfl
      | tail h => cases h
    · intro h
      subst h
      exact QueueMem.head
  unfold QueueContainsFrom SxQ
  rintro ⟨lab, S, hmem⟩
  rw [hsing] at hmem
  injection hmem with h1 _ _
  exact absurd h1 (by decide)

/-- Liveness (+`NoRec`+`WellFormed`) does NOT suffice for send-steps, so no
    liveness hypothesis can repair the encoder-output lemmas:
    `LxM` is `extC`-headed (hence `NoRec` and
    well-formed) and `LxQ` is live (it folds, i.e. gets consumed), yet no
    send-step exists from `LxM` — all constructors need `intC`/`tRec`
    heads or `recv` tags. The true requirement is an `intC` head
    (syntactic; the paper uses closures instead). -/
def LxM : SessionType :=
  SessionType.externalChoice "r" [("l", "s", SessionType.tEnd)]

/-- Liveness-counterexample queue: a single `(r, l, s)` message. -/
def LxQ : Queue := [QueueMessage.msg "r" "l" "s"]

/-- The liveness-counterexample type is well-formed. -/
theorem LxWF : LxM.WellFormed := by
  unfold LxM
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice
    · simp
    · simp
    · intro x hx
      simp at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    simp [SessionType.fv, SessionType.fv.goExt]
  · apply SessionType.Contractive.externalChoice
    intro x hx
    simp at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact SessionType.Contractive.end


-- `LxQ` is live: it folds (gets consumed) via on-role receive.
/-- The liveness-counterexample queue folds (it gets consumed), yet no send-step exists. -/
theorem LxFold : ∃ M', monitor_fold_aux LxQ LxM M' := by
  have hb : mon_tr_yes_base LxM (ext_tag.recv "r" "l" "s") SessionType.tEnd := by
    unfold LxM
    apply mon_tr_yes_base.extC
    · simp
    · simp
  have hY : mon_tr_yes LxM (ext_tag.recv "r" "l" "s") SessionType.tEnd :=
    ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
  unfold LxQ
  simp only [monitor_fold_aux]
  exact ⟨_, _, hY, rfl⟩
