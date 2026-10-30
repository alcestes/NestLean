import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.StuckWitness
import Nest.NoRec.PruneFunctions
import Nest.NoRec.NoRecEncoder

/-!
# DrainCore: drainability core: choice-function bridges, queue order, cannot-core.

over_trans preservation under NoRec, choice-function core bridges (`toDeep`/`toCore`/`suffix`),
queue order and oldest-uniqueness, branch-target uniqueness, and the `Cannot` failure core
with absence-implies-no-dequeue. Feeds the step classification and survival layers.
-/

section DrainCoreover_trans

/-- Overapprox steps preserve `NoRec` (branch targets are strict subterms; the `tRec` arm is
   vacuous). -/
theorem over_trans_preserves_norec {stq stq' : SessionTypeWithQueue} {α : st_label}
    (h : over_trans stq α stq') (hNR : stq.1.NoRec) : stq'.1.NoRec := by
  cases h with
  | dequeue hEq hmem hQ =>
    rw [hEq] at hNR
    exact noRec_of_mem_extBranches hNR hmem
  | specInp hEq hmem hAbs =>
    rw [hEq] at hNR
    exact noRec_of_mem_extBranches hNR hmem
  | sendFresh hEq hST hFresh =>
    subst hEq
    cases hST with
    | intC hmem => exact noRec_of_mem_intBranches hNR hmem
  | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR hU)


/-- `over_trans_trace` concatenates. -/
theorem over_trans_trace_append : ∀ {a b : SessionTypeWithQueue} {ρ : List st_label},
    over_trans_trace a ρ b → ∀ {σ : List st_label} {c : SessionTypeWithQueue},
    over_trans_trace b σ c → over_trans_trace a (ρ ++ σ) c := by
  intro a b ρ h1
  induction h1 with
  | refl _ =>
    intro σ c h2
    simpa using h2
  | step h hT ih =>
    intro σ c h2
    exact over_trans_trace.step h (ih h2)


/-- An `internalChoice` can fire speculatively from `Qi`: none of its
    branch roles has messages in `Qi` (so a `sendFresh` step is
    available for every branch). Read at the firing state (`Qᵢ`), not
    the trace end: fireability is a per-site property. -/
def int_choice_fireable (Ti : SessionType) (Qi : Queue)
    (branches : List (Role × Lab × DataSort × SessionType)) : Prop :=
  ∀ (br : Role × Lab × DataSort × SessionType), br ∈ branches →
    ∀ (m : QueueMessage), m ∈ Qi → m.1 ≠ br.1



end DrainCoreover_trans

section DrainCoreBridge

/-- On-trace bundle for the `Deep`-to-`Core` choice construction:
    `(Ti, Qi)` lies on the witness trace `ρ` from `(T, Q)` to
    `(Tn, [])`. -/
private def deep_on_trace (T : SessionType) (Q : Queue) (Tn : SessionType)
    (ρ : List st_label) (Ti : SessionType) (Qi : Queue) : Prop :=
  ∃ ρ1 ρ2 : List st_label, over_trans_trace (T, Q) ρ1 (Ti, Qi) ∧
    over_trans_trace (Ti, Qi) ρ2 (Tn, []) ∧ ρ = ρ1 ++ ρ2


/-- `Core`-deep upgrades to `Deep` (repackage the stored choice
    function into per-site existentials; mirror of
    `CannotAlwaysDrainInternalDeepCore.toDef`). -/
theorem CanAlwaysDrainInternalDeepCore.toDeep {T : SessionType} {Q : Queue}
    (h : CanAlwaysDrainInternalDeepCore T Q) :
    CanAlwaysDrainInternalDeep T Q := by
  cases h with
  | mk T0 Q0 Tn ρ ch hTr hInt hEm hEc hTrec =>
    refine ⟨Tn, ρ, hTr, ?_⟩
    · intro Ti Qi ρ1 ρ2 h1 h2 heq
      refine ⟨?_, ?_, ?_⟩
      · intro branches hEq hneB
        exact hInt Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB
      · intro p branches hEq hneB hnd
        exact ⟨ch Ti Qi p branches,
          hEm Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB hnd,
          hEc Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB hnd⟩
      · intro X B hEq
        exact hTrec Ti Qi ρ1 ρ2 X B h1 h2 heq hEq


/-- `Deep` upgrades to `Core`-deep: build the per-site choice
    function from the per-site existentials (`Classical.choice`
    over an all-states existential with the on-trace conditions as
    a hypothesis; off-trace states take a dummy triple). -/
theorem CanAlwaysDrainInternalDeep.toCore {T : SessionType} {Q : Queue}
    (h : CanAlwaysDrainInternalDeep T Q) :
    CanAlwaysDrainInternalDeepCore T Q := by
  obtain ⟨Tn, ρ, hTr, hall⟩ := h
  classical
  have hCh : ∀ (Ti : SessionType) (Qi : Queue) (p : Role)
      (branches : List (Lab × DataSort × SessionType)),
      deep_on_trace T Q Tn ρ Ti Qi →
      Ti = SessionType.externalChoice p branches → branches ≠ [] →
      NoDequeueFrom Ti Qi →
      ∃ (br : Lab × DataSort × SessionType),
        br ∈ branches ∧ CanAlwaysDrainInternalDeepCore br.2.2 Qi := by
    intro Ti Qi p branches hOn hEq hneB hnd
    obtain ⟨ρ1, ρ2, h1, h2, heq⟩ := hOn
    obtain ⟨-, hExt, -⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
    exact hExt p branches hEq hneB hnd
  have hEx : ∀ (Ti : SessionType) (Qi : Queue) (p : Role)
      (branches : List (Lab × DataSort × SessionType)),
      ∃ (br : Lab × DataSort × SessionType),
        (deep_on_trace T Q Tn ρ Ti Qi ∧
          Ti = SessionType.externalChoice p branches ∧ branches ≠ [] ∧
          NoDequeueFrom Ti Qi) →
        br ∈ branches ∧ CanAlwaysDrainInternalDeepCore br.2.2 Qi := by
    intro Ti Qi p branches
    by_cases hCon : (deep_on_trace T Q Tn ρ Ti Qi ∧
      Ti = SessionType.externalChoice p branches ∧ branches ≠ [] ∧
      NoDequeueFrom Ti Qi)
    · obtain ⟨ρ1, ρ2, h1, h2, heq⟩ := hCon.1
      obtain ⟨-, hExt, -⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
      obtain ⟨br, hmem, hcore⟩ := hExt p branches hCon.2.1 hCon.2.2.1 hCon.2.2.2
      exact ⟨br, fun _ => ⟨hmem, hcore⟩⟩
    · exact ⟨("", "", SessionType.tEnd), fun hcon => absurd hcon hCon⟩
  refine CanAlwaysDrainInternalDeepCore.mk T Q Tn ρ
    (fun Ti Qi p branches => Classical.choose (hEx Ti Qi p branches)) hTr ?_ ?_ ?_ ?_
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB br hmem
    obtain ⟨hInt, -, -⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
    exact hInt branches hEq hneB br hmem
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB hnd
    exact ((Classical.choose_spec (hEx Ti Qi p branches)
      ⟨⟨ρ1, ρ2, h1, h2, heq⟩, hEq, hneB, hnd⟩).1)
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB hnd
    exact ((Classical.choose_spec (hEx Ti Qi p branches)
      ⟨⟨ρ1, ρ2, h1, h2, heq⟩, hEq, hneB, hnd⟩).2)
  · intro Ti Qi ρ1 ρ2 X B h1 h2 heq hEq
    obtain ⟨-, -, hTrec⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
    exact hTrec X B hEq


/-- Suffix of a `Deep` witness is `Deep` of its midpoint: the drain
    suffix plus the on-trace conditions restricted through the
    prefix (`ρ = (ρ1 ++ σ1) ++ σ2` by `heq`, `geq2`, append assoc). -/
theorem CanAlwaysDrainInternalDeep.suffix {T0 T1 Tn : SessionType}
    {Q0 Q1 : Queue} {ρ ρ1 ρ2 : List st_label}
    (hall : ∀ (Ti : SessionType) (Qi : Queue) (σ1 σ2 : List st_label),
      over_trans_trace (T0, Q0) σ1 (Ti, Qi) →
      over_trans_trace (Ti, Qi) σ2 (Tn, []) →
      ρ = σ1 ++ σ2 →
      ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
        Ti = SessionType.internalChoice branches → branches ≠ [] →
        ∀ (br : Role × Lab × DataSort × SessionType),
          br ∈ branches → CanAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
      (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
        Ti = SessionType.externalChoice p branches → branches ≠ [] →
        NoDequeueFrom Ti Qi →
        ∃ (br : Lab × DataSort × SessionType),
          br ∈ branches ∧ CanAlwaysDrainInternalDeepCore br.2.2 Qi) ∧
      (∀ (X : String) (B : SessionType),
        Ti = SessionType.tRec X B →
        CanAlwaysDrainInternalDeepCore B Qi)))
    (h1 : over_trans_trace (T0, Q0) ρ1 (T1, Q1))
    (h2 : over_trans_trace (T1, Q1) ρ2 (Tn, []))
    (heq : ρ = ρ1 ++ ρ2) :
    CanAlwaysDrainInternalDeep T1 Q1 := by
  refine ⟨Tn, ρ2, h2, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq2
  exact hall Ti Qi (ρ1 ++ σ1) σ2 (over_trans_trace_append h1 g1) g2
    (by rw [heq, geq2, List.append_assoc])



end DrainCoreBridge

section DrainCoreOrder

end DrainCoreOrder

section DrainCoreTargetUnique

/-- Same `extC` key fires to the same target (`NoDupl` labels). -/
private theorem ext_target_unique_aux
    : ∀ (bs : List (Lab × DataSort × SessionType))
    (lab : Lab) (S : DataSort) (T1 T2 : SessionType),
    (List.map (fun x : Lab × DataSort × SessionType => x.1) bs).Nodup →
    (lab, S, T1) ∈ bs → (lab, S, T2) ∈ bs → T1 = T2 := by
  intro bs
  induction bs with
  | nil =>
    intro lab S T1 T2 hn h1 h2
    simp at h1
  | cons b bs ih =>
    intro lab S T1 T2 hn h1 h2
    rw [List.mem_cons] at h1 h2
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hmem, hnod⟩ := hn
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl, rfl⟩ := h2
        rfl
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        have hcon : lab ∈
            List.map (fun x : Lab × DataSort × SessionType => x.1) bs :=
          List.mem_map.mpr ⟨(lab, S, T2), h2, rfl⟩
        exact absurd hcon hmem
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl⟩ := h2
        have hcon : lab ∈
            List.map (fun x : Lab × DataSort × SessionType => x.1) bs :=
          List.mem_map.mpr ⟨(lab, S, T1), h1, rfl⟩
        exact absurd hcon hmem
      · exact ih _ _ _ _ hnod h1 h2


/-- Same `extC` key fires to the same target (`NoDupl` head). -/
theorem ext_target_unique_norec {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T1 T2 : SessionType}
    (hND : SessionType.NoDupl (SessionType.externalChoice p branches))
    (h1 : (lab, S, T1) ∈ branches) (h2 : (lab, S, T2) ∈ branches) :
    T1 = T2 := by
  cases hND with
  | externalChoice h_nodup h_ne h_branches =>
    exact ext_target_unique_aux _ _ _ _ _ h_nodup h1 h2


/-- Same `intC` key fires to the same target (`NoDupl` pairs). -/
private theorem int_target_unique_aux
    : ∀ (bs : List (Role × Lab × DataSort × SessionType))
    (p : Role) (lab : Lab) (S : DataSort) (T1 T2 : SessionType),
    (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) bs).Nodup →
    (p, lab, S, T1) ∈ bs → (p, lab, S, T2) ∈ bs → T1 = T2 := by
  intro bs
  induction bs with
  | nil =>
    intro p lab S T1 T2 hn h1 h2
    simp at h1
  | cons b bs ih =>
    intro p lab S T1 T2 hn h1 h2
    rw [List.mem_cons] at h1 h2
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hmem, hnod⟩ := hn
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl, rfl⟩ := h2
        rfl
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
        have hcon : (p, lab) ∈
            List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
              bs :=
          List.mem_map.mpr ⟨(p, lab, S, T2), h2, rfl⟩
        exact absurd hcon hmem
    · rcases h2 with h2 | h2
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
        have hcon : (p, lab) ∈
            List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
              bs :=
          List.mem_map.mpr ⟨(p, lab, S, T1), h1, rfl⟩
        exact absurd hcon hmem
      · exact ih _ _ _ _ _ hnod h1 h2


/-- Same `intC` key fires to the same target (`NoDupl` head). -/
theorem int_target_unique_norec
    {branches : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T1 T2 : SessionType}
    (hND : SessionType.NoDupl (SessionType.internalChoice branches))
    (h1 : (p, lab, S, T1) ∈ branches) (h2 : (p, lab, S, T2) ∈ branches) :
    T1 = T2 := by
  cases hND with
  | internalChoice h_nodup h_ne h_branches =>
    exact int_target_unique_aux _ _ _ _ _ _ h_nodup h1 h2


/-- Core of deep failure below: same statement, except the per-site
    `intC` witness is supplied by an explicit choice function (rather
    than a per-site existential), because the kernel rejects `∃`/`∧`
    wrapping the recursive occurrence when their payload mentions
    local variables. -/
inductive CannotAlwaysDrainInternalDeepCore : SessionType → Queue → Prop where
  | mk (T0 : SessionType) (Q0 : Queue) (Tn : SessionType) (Qn : Queue)
      (ρ : List st_label)
      (choice : SessionType → Queue →
        List (Role × Lab × DataSort × SessionType) →
        Role × Lab × DataSort × SessionType) :
      over_trans_trace (T0, Q0) ρ (Tn, Qn) →
      Qn ≠ [] →
      (Tn = SessionType.tEnd ∨
        (∃ (branches : List (Role × Lab × DataSort × SessionType))
          (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
          (m : QueueMessage),
          Tn = SessionType.internalChoice branches ∧
          (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
      ((∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
        (lab : Lab) (S : DataSort) (m : QueueMessage),
        Tn = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
        m = QueueMessage.msg p lab S ∧
        ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
      (∃ (X : String) (B U : SessionType),
        Tn = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
        (U = SessionType.tEnd ∨
          (∃ (branches : List (Role × Lab × DataSort × SessionType))
            (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
            (m : QueueMessage),
            U = SessionType.internalChoice branches ∧
            (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
          (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
            (lab : Lab) (S : DataSort) (m : QueueMessage),
            U = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
            m = QueueMessage.msg p lab S ∧
            ∀ (T' : SessionType), (lab, S, T') ∉ branches))))) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, Qn) →
        ρ = ρ1 ++ ρ2 →
        ∀ (branches : List (Role × Lab × DataSort × SessionType)),
          Ti = SessionType.internalChoice branches → branches ≠ [] →
          int_choice_fireable Ti Qi branches →
          choice Ti Qi branches ∈ branches) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, Qn) →
        ρ = ρ1 ++ ρ2 →
        ∀ (branches : List (Role × Lab × DataSort × SessionType)),
          Ti = SessionType.internalChoice branches → branches ≠ [] →
          int_choice_fireable Ti Qi branches →
          CannotAlwaysDrainInternalDeepCore (choice Ti Qi branches).2.2.2 Qi) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label)
        (p : Role) (branches : List (Lab × DataSort × SessionType)),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, Qn) →
        ρ = ρ1 ++ ρ2 → Ti = SessionType.externalChoice p branches →
        branches ≠ [] → (∀ m ∈ Qi, m.1 ≠ p) →
        ∀ (br : Lab × DataSort × SessionType),
          br ∈ branches → CannotAlwaysDrainInternalDeepCore br.2.2 Qi) →
      CannotAlwaysDrainInternalDeepCore T0 Q0



end DrainCoreTargetUnique

section DrainCoreCannot

/-- Deep failure: a witness `over_trans` trace (`st_label`s are the
    approx-labels) from `(T₀, Q₀)` to a failure-nonempty end — `Qₙ ≠ []`
    with `Tₙ` ended, a blocked `internalChoice`, an
    `externalChoice` whose oldest queued message from its owner has
    an absent key, or a `tRec` head whose body unfolds (via
    `UnfoldStar`) to one of those — such that every state `(Tᵢ, Qᵢ)` lying on that
    trace (including the endpoints) satisfies: some
    `internalChoice`-branch target is bad for the same queue (the
    adversarial selection), and every speculative
    `externalChoice`-branch target (no owner message queued) is bad
    for the same queue (the spec's `Qⱼ` is read as `Qᵢ`, since `j`
    ranges over branches, not trace positions). Stated over the
    choice-function core above, so only `∀`/`→` guard the recursion. -/
def CannotAlwaysDrainInternalDeep (T0 : SessionType) (Q0 : Queue) : Prop :=
  ∃ (Tn : SessionType) (Qn : Queue) (ρ : List st_label),
    over_trans_trace (T0, Q0) ρ (Tn, Qn) ∧ Qn ≠ [] ∧
    (Tn = SessionType.tEnd ∨
      (∃ (branches : List (Role × Lab × DataSort × SessionType))
        (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
        (m : QueueMessage),
        Tn = SessionType.internalChoice branches ∧
        (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
      ((∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
        (lab : Lab) (S : DataSort) (m : QueueMessage),
        Tn = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
        m = QueueMessage.msg p lab S ∧
        ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
      (∃ (X : String) (B U : SessionType),
        Tn = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
        (U = SessionType.tEnd ∨
          (∃ (branches : List (Role × Lab × DataSort × SessionType))
            (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
            (m : QueueMessage),
            U = SessionType.internalChoice branches ∧
            (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
          (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
            (lab : Lab) (S : DataSort) (m : QueueMessage),
            U = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
            m = QueueMessage.msg p lab S ∧
            ∀ (T' : SessionType), (lab, S, T') ∉ branches))))) ∧
    ∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
      over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
      over_trans_trace (Ti, Qi) ρ2 (Tn, Qn) →
      ρ = ρ1 ++ ρ2 →
      ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
        Ti = SessionType.internalChoice branches → branches ≠ [] →
        int_choice_fireable Ti Qi branches →
        ∃ (br : Role × Lab × DataSort × SessionType),
          br ∈ branches ∧ CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
      (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
        Ti = SessionType.externalChoice p branches → branches ≠ [] →
        (∀ m ∈ Qi, m.1 ≠ p) →
        ∀ (br : Lab × DataSort × SessionType),
          br ∈ branches → CannotAlwaysDrainInternalDeepCore br.2.2 Qi))


/-- Absence implies no-dequeue: a successful dequeue scan exhibits a
    same-sender message in the queue (so speculative states, with no
    owner message, never dequeue). Needs no `NoRec` — the `st_trans` is
    pinned by constructor clash off the `extC` equation. -/
theorem absence_imp_noDequeueFrom {Ti : SessionType} {Qi : Queue} {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    (hEq : Ti = SessionType.externalChoice p branches)
    (habs : ∀ m ∈ Qi, m.1 ≠ p) : NoDequeueFrom Ti Qi := by
  intro ⟨T', Q', r, lab, S, hST, hQd⟩
  subst hEq
  cases hST with
  | extC _ =>
    obtain ⟨seen, left, hQeq, -, -⟩ := queue_dequeue_some_iff hQd
    have hmemQ : QueueMessage.msg p lab S ∈ Qi := by
      rw [hQeq]
      simp
    exact habs _ hmemQ rfl


/-- `Core`-deep failure upgrades to `Def` failure (repackage the stored
    choice function into per-site existentials). -/
theorem CannotAlwaysDrainInternalDeepCore.toDef {T : SessionType} {Q : Queue}
    (h : CannotAlwaysDrainInternalDeepCore T Q) :
    CannotAlwaysDrainInternalDeep T Q := by
  cases h with
  | mk T0 Q0 Tn Qn ρ ch hTr hne hend hIM hID hE =>
    refine ⟨Tn, Qn, ρ, hTr, hne, ?_, ?_⟩
    · rcases hend with hT | hI | hA | hR
      · exact Or.inl hT
      · exact Or.inr (Or.inl hI)
      · exact Or.inr (Or.inr (Or.inl hA))
      · exact Or.inr (Or.inr (Or.inr hR))
    · intro Ti Qi ρ1 ρ2 h1 h2 heq
      refine ⟨?_, ?_⟩
      · intro branches hEq hneB hfire
        exact ⟨ch Ti Qi branches, hIM Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB hfire,
          hID Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB hfire⟩
      · intro p branches hEq hneB habs br hmem
        exact hE Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB habs br hmem


/-- On-trace bundle for the `Cannot`-to-`Core` choice construction:
    `(Ti, Qi)` lies on the witness trace `ρ` from `(T, Q)` to
    `(Tn, Qn)`. -/
private def cannot_on_trace (T : SessionType) (Q : Queue) (Tn : SessionType)
    (Qn : Queue) (ρ : List st_label) (Ti : SessionType) (Qi : Queue) : Prop :=
  ∃ ρ1 ρ2 : List st_label, over_trans_trace (T, Q) ρ1 (Ti, Qi) ∧
    over_trans_trace (Ti, Qi) ρ2 (Tn, Qn) ∧ ρ = ρ1 ++ ρ2


/-- `Cannot` upgrades to `Core`-bad: build the per-site choice
    function from the per-site existentials (`Classical.choose`
    over an all-states existential with the on-trace conditions as
    a hypothesis; off-trace states take a dummy branch). Mirror of
    `CanAlwaysDrainInternalDeep.toCore`. -/
theorem CannotAlwaysDrainInternalDeep.toCore {T : SessionType} {Q : Queue}
    (h : CannotAlwaysDrainInternalDeep T Q) :
    CannotAlwaysDrainInternalDeepCore T Q := by
  obtain ⟨Tn, Qn, ρ, hTr, hne, hend, hall⟩ := h
  classical
  have hCh : ∀ (Ti : SessionType) (Qi : Queue)
      (branches : List (Role × Lab × DataSort × SessionType)),
      cannot_on_trace T Q Tn Qn ρ Ti Qi →
      Ti = SessionType.internalChoice branches → branches ≠ [] →
      int_choice_fireable Ti Qi branches →
      ∃ (br : Role × Lab × DataSort × SessionType),
        br ∈ branches ∧ CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi := by
    intro Ti Qi branches hOn hEq hneB hfire
    obtain ⟨ρ1, ρ2, h1, h2, heq⟩ := hOn
    obtain ⟨hInt, -⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
    exact hInt branches hEq hneB hfire
  have hEx : ∀ (Ti : SessionType) (Qi : Queue)
      (branches : List (Role × Lab × DataSort × SessionType)),
      ∃ (br : Role × Lab × DataSort × SessionType),
        (cannot_on_trace T Q Tn Qn ρ Ti Qi ∧
          Ti = SessionType.internalChoice branches ∧ branches ≠ [] ∧
          int_choice_fireable Ti Qi branches) →
        br ∈ branches ∧ CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi := by
    intro Ti Qi branches
    by_cases hCon : (cannot_on_trace T Q Tn Qn ρ Ti Qi ∧
      Ti = SessionType.internalChoice branches ∧ branches ≠ [] ∧
      int_choice_fireable Ti Qi branches)
    · obtain ⟨ρ1, ρ2, h1, h2, heq⟩ := hCon.1
      obtain ⟨hInt, -⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
      obtain ⟨br, hmem, hcore⟩ :=
        hInt branches hCon.2.1 hCon.2.2.1 hCon.2.2.2
      exact ⟨br, fun _ => ⟨hmem, hcore⟩⟩
    · exact ⟨("p", "a", "sa", SessionType.tEnd), fun hcon => absurd hcon hCon⟩
  refine CannotAlwaysDrainInternalDeepCore.mk T Q Tn Qn ρ
    (fun Ti Qi branches => Classical.choose (hEx Ti Qi branches))
    hTr hne hend ?_ ?_ ?_
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB hfire
    exact ((Classical.choose_spec (hEx Ti Qi branches))
      ⟨⟨ρ1, ρ2, h1, h2, heq⟩, hEq, hneB, hfire⟩).1
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hneB hfire
    exact ((Classical.choose_spec (hEx Ti Qi branches))
      ⟨⟨ρ1, ρ2, h1, h2, heq⟩, hEq, hneB, hfire⟩).2
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hneB habs br hmem
    obtain ⟨-, hExt⟩ := hall Ti Qi ρ1 ρ2 h1 h2 heq
    exact hExt p branches hEq hneB habs br hmem



end DrainCoreCannot

section ListUtilities

/-- `find?` results are members satisfying the predicate. -/
theorem find?_some_mem {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
    by_cases hp : p hd = true
    · have h2 : (hd :: tl).find? p = some hd := by simp [List.find?, hp]
      rw [h2] at h
      obtain rfl := Option.some_inj.mp h
      exact ⟨List.mem_cons.mpr (Or.inl rfl), hp⟩
    · have h2 : (hd :: tl).find? p = tl.find? p := by simp [List.find?, hp]
      rw [h2] at h
      obtain ⟨hmem, hpred⟩ := ih h
      exact ⟨List.mem_cons.mpr (Or.inr hmem), hpred⟩

end ListUtilities
