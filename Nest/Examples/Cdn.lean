import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun

namespace Cdn

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/07_cdn.scala`
   (Scala package `cdn`; file `07_cdn.scala` maps to this module since
   Lean module names may not start with a digit).
   Translated below are the four `lst_*` local session types
   (`lst_User`, `lst_LocalDNS`, `lst_IntAuthDNS`, `lst_ExtAuthDNS`;
   none uses recursion). Switch setup, IP rules, port checks and
   monitor wiring from `setup` are not session types and are not
   translated. Translation conventions: `IntChoice` branches become
   `internalChoice` branches `(agent, label, sort, cont)`; `ExtChoice`
   branches become `externalChoice` branches `(label, sort, cont)`;
   `Rec`/`Var`/`End` become `tRec`/`tVar`/`tEnd`. Agents become roles,
   labels stay labels. The Scala types carry no payload sorts, so
   every branch uses the placeholder sort `"unit"`. -/

/-- `lst_User`. -/
def User : SessionType :=
  SessionType.internalChoice
    [("LocalDNS", "DNSQuery", "unit",
      SessionType.externalChoice "LocalDNS"
        [("IPAddr", "unit", SessionType.tEnd)])]

/-- `lst_LocalDNS`. -/
def LocalDNS : SessionType :=
  SessionType.externalChoice "User"
    [("DNSQuery", "unit",
      SessionType.internalChoice
        [("IntAuthDNS", "AuthQuery", "unit",
          SessionType.externalChoice "IntAuthDNS"
            [("Hostname", "unit",
              SessionType.internalChoice
                [("ExtAuthDNS", "AuthQuery", "unit",
                  SessionType.externalChoice "ExtAuthDNS"
                    [("IPAddr", "unit",
                      SessionType.internalChoice
                        [("User", "IPAddr", "unit",
                          SessionType.tEnd)])])])])])]

/-- `lst_IntAuthDNS`. -/
def IntAuthDNS : SessionType :=
  SessionType.externalChoice "LocalDNS"
    [("AuthQuery", "unit",
      SessionType.internalChoice
        [("LocalDNS", "Hostname", "unit", SessionType.tEnd)])]

/-- `lst_ExtAuthDNS`. -/
def ExtAuthDNS : SessionType :=
  SessionType.externalChoice "LocalDNS"
    [("AuthQuery", "unit",
      SessionType.internalChoice
        [("LocalDNS", "IPAddr", "unit", SessionType.tEnd)])]

-- All four types are recursion-free: certified by the generic `NoRec` lemmas.
/-- `User` is recursion-free (boolean check). -/
theorem User_norec : User.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `User` (empty seen set, via recursion-freedom). -/
theorem User_deep : Prunable [] User :=
  norec_deep User_norec []
/-- Monitorability of `User` (finite prune closure, via recursion-freedom). -/
theorem User_mon : Drainability.Monitorable User :=
  norec_monitorable User_norec

/-- `LocalDNS` is recursion-free (boolean check). -/
theorem LocalDNS_norec : LocalDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `LocalDNS` (empty seen set, via recursion-freedom). -/
theorem LocalDNS_deep : Prunable [] LocalDNS :=
  norec_deep LocalDNS_norec []
/-- Monitorability of `LocalDNS` (finite prune closure, via recursion-freedom). -/
theorem LocalDNS_mon : Drainability.Monitorable LocalDNS :=
  norec_monitorable LocalDNS_norec

/-- `IntAuthDNS` is recursion-free (boolean check). -/
theorem IntAuthDNS_norec : IntAuthDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `IntAuthDNS` (empty seen set, via recursion-freedom). -/
theorem IntAuthDNS_deep : Prunable [] IntAuthDNS :=
  norec_deep IntAuthDNS_norec []
/-- Monitorability of `IntAuthDNS` (finite prune closure, via recursion-freedom). -/
theorem IntAuthDNS_mon : Drainability.Monitorable IntAuthDNS :=
  norec_monitorable IntAuthDNS_norec

/-- `ExtAuthDNS` is recursion-free (boolean check). -/
theorem ExtAuthDNS_norec : ExtAuthDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `ExtAuthDNS` (empty seen set, via recursion-freedom). -/
theorem ExtAuthDNS_deep : Prunable [] ExtAuthDNS :=
  norec_deep ExtAuthDNS_norec []
/-- Monitorability of `ExtAuthDNS` (finite prune closure, via recursion-freedom). -/
theorem ExtAuthDNS_mon : Drainability.Monitorable ExtAuthDNS :=
  norec_monitorable ExtAuthDNS_norec

/-- Empty-queue network for the four cdn roles. -/
def Net : Network :=
  [("User", (User, [])),
   ("LocalDNS", (LocalDNS, [])),
   ("IntAuthDNS", (IntAuthDNS, [])),
   ("ExtAuthDNS", (ExtAuthDNS, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact User.wfCheck_sound (by decide)
  · exact LocalDNS.wfCheck_sound (by decide)
  · exact IntAuthDNS.wfCheck_sound (by decide)
  · exact ExtAuthDNS.wfCheck_sound (by decide)

/-- `Net` has no self-mention: each role is absent from its own type. -/
theorem Net_noSelf : Net.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- `Net` contains every role occurring in its member types. -/
theorem Net_rolesPresent : Net.RolesPresent := by
  intro q T Q s hmem hOcc
  have hmemR : s ∈ rolesOf T := occurs_mem hOcc
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [User, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩
  · simp only [LocalDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(User, []), by decide⟩
    · exact ⟨(IntAuthDNS, []), by decide⟩
    · exact ⟨(IntAuthDNS, []), by decide⟩
    · exact ⟨(ExtAuthDNS, []), by decide⟩
    · exact ⟨(ExtAuthDNS, []), by decide⟩
    · exact ⟨(User, []), by decide⟩
  · simp only [IntAuthDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩
  · simp only [ExtAuthDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)

/-- Continuation of `User` after sending `DNSQuery` to `LocalDNS`. -/
def U1 : SessionType :=
  SessionType.externalChoice "LocalDNS" [("IPAddr", "unit", SessionType.tEnd)]
/-- Final send of `LocalDNS` to `User` carrying `IPAddr`. -/
def L5 : SessionType :=
  SessionType.internalChoice [("User", "IPAddr", "unit", SessionType.tEnd)]
/-- `LocalDNS` waits for `IPAddr` from `ExtAuthDNS` before replying to `User`. -/
def L4 : SessionType :=
  SessionType.externalChoice "ExtAuthDNS" [("IPAddr", "unit", L5)]
/-- `LocalDNS` queries `ExtAuthDNS` after learning the hostname. -/
def L3 : SessionType :=
  SessionType.internalChoice [("ExtAuthDNS", "AuthQuery", "unit", L4)]
/-- `LocalDNS` waits for `Hostname` from `IntAuthDNS`. -/
def L2 : SessionType :=
  SessionType.externalChoice "IntAuthDNS" [("Hostname", "unit", L3)]
/-- `LocalDNS` queries `IntAuthDNS` after the user request. -/
def L1 : SessionType :=
  SessionType.internalChoice [("IntAuthDNS", "AuthQuery", "unit", L2)]
/-- `IntAuthDNS` answers `Hostname` to `LocalDNS`. -/
def I1 : SessionType :=
  SessionType.internalChoice [("LocalDNS", "Hostname", "unit", SessionType.tEnd)]
/-- `ExtAuthDNS` answers `IPAddr` to `LocalDNS`. -/
def E1 : SessionType :=
  SessionType.internalChoice [("LocalDNS", "IPAddr", "unit", SessionType.tEnd)]

-- ============ OUT-step characterizations ============
theorem User_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans User (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "DNSQuery" ∧ S = "unit" ∧ T' = U1 := by
  intro h
  unfold User at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem U1_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans U1 (st_label.out p lab S) T') : False := by
  unfold U1 at h
  cases h

theorem LocalDNS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans LocalDNS (st_label.out p lab S) T') : False := by
  unfold LocalDNS at h
  cases h

theorem L1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans L1 (st_label.out p lab S) T' →
    p = "IntAuthDNS" ∧ lab = "AuthQuery" ∧ S = "unit" ∧ T' = L2 := by
  intro h
  unfold L1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem L2_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans L2 (st_label.out p lab S) T') : False := by
  unfold L2 at h
  cases h

theorem L3_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans L3 (st_label.out p lab S) T' →
    p = "ExtAuthDNS" ∧ lab = "AuthQuery" ∧ S = "unit" ∧ T' = L4 := by
  intro h
  unfold L3 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem L4_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans L4 (st_label.out p lab S) T') : False := by
  unfold L4 at h
  cases h

theorem L5_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans L5 (st_label.out p lab S) T' →
    p = "User" ∧ lab = "IPAddr" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold L5 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem IntAuthDNS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans IntAuthDNS (st_label.out p lab S) T') : False := by
  unfold IntAuthDNS at h
  cases h

theorem I1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans I1 (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "Hostname" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold I1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem ExtAuthDNS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans ExtAuthDNS (st_label.out p lab S) T') : False := by
  unfold ExtAuthDNS at h
  cases h

theorem E1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans E1 (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "IPAddr" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold E1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem tEnd_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

-- ============ INP-step characterizations ============
theorem User_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans User (st_label.inp p lab S) T') : False := by
  unfold User at h
  cases h

theorem U1_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans U1 (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "IPAddr" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold U1 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem LocalDNS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans LocalDNS (st_label.inp p lab S) T' →
    p = "User" ∧ lab = "DNSQuery" ∧ S = "unit" ∧ T' = L1 := by
  intro h
  unfold LocalDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem L1_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans L1 (st_label.inp p lab S) T') : False := by
  unfold L1 at h
  cases h

theorem L2_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans L2 (st_label.inp p lab S) T' →
    p = "IntAuthDNS" ∧ lab = "Hostname" ∧ S = "unit" ∧ T' = L3 := by
  intro h
  unfold L2 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem L3_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans L3 (st_label.inp p lab S) T') : False := by
  unfold L3 at h
  cases h

theorem L4_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans L4 (st_label.inp p lab S) T' →
    p = "ExtAuthDNS" ∧ lab = "IPAddr" ∧ S = "unit" ∧ T' = L5 := by
  intro h
  unfold L4 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem L5_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans L5 (st_label.inp p lab S) T') : False := by
  unfold L5 at h
  cases h

theorem IntAuthDNS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans IntAuthDNS (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "AuthQuery" ∧ S = "unit" ∧ T' = I1 := by
  intro h
  unfold IntAuthDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem I1_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans I1 (st_label.inp p lab S) T') : False := by
  unfold I1 at h
  cases h

theorem ExtAuthDNS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans ExtAuthDNS (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "AuthQuery" ∧ S = "unit" ∧ T' = E1 := by
  intro h
  unfold ExtAuthDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem E1_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans E1 (st_label.inp p lab S) T') : False := by
  unfold E1 at h
  cases h

theorem tEnd_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h

-- ============ Reachable states (whole-network enumeration) ============
-- Messages
abbrev mUD : QueueMessage := QueueMessage.msg "User" "DNSQuery" "unit"
abbrev mLA : QueueMessage := QueueMessage.msg "LocalDNS" "AuthQuery" "unit"
abbrev mIH : QueueMessage := QueueMessage.msg "IntAuthDNS" "Hostname" "unit"
abbrev mEI : QueueMessage := QueueMessage.msg "ExtAuthDNS" "IPAddr" "unit"
abbrev mLI : QueueMessage := QueueMessage.msg "LocalDNS" "IPAddr" "unit"

def S0 : Network :=
  [("User", (User, [])), ("LocalDNS", (LocalDNS, [])),
   ("IntAuthDNS", (IntAuthDNS, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S1 : Network :=
  [("LocalDNS", (LocalDNS, [mUD])), ("User", (U1, [])),
   ("IntAuthDNS", (IntAuthDNS, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S2 : Network :=
  [("LocalDNS", (L1, [])), ("User", (U1, [])),
   ("IntAuthDNS", (IntAuthDNS, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S3 : Network :=
  [("IntAuthDNS", (IntAuthDNS, [mLA])), ("LocalDNS", (L2, [])),
   ("User", (U1, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S4 : Network :=
  [("IntAuthDNS", (I1, [])), ("LocalDNS", (L2, [])),
   ("User", (U1, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S5 : Network :=
  [("LocalDNS", (L2, [mIH])), ("IntAuthDNS", (SessionType.tEnd, [])),
   ("User", (U1, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S6 : Network :=
  [("LocalDNS", (L3, [])), ("IntAuthDNS", (SessionType.tEnd, [])),
   ("User", (U1, [])), ("ExtAuthDNS", (ExtAuthDNS, []))]
def S7 : Network :=
  [("ExtAuthDNS", (ExtAuthDNS, [mLA])), ("LocalDNS", (L4, [])),
   ("IntAuthDNS", (SessionType.tEnd, [])), ("User", (U1, []))]
def S8 : Network :=
  [("ExtAuthDNS", (E1, [])), ("LocalDNS", (L4, [])),
   ("IntAuthDNS", (SessionType.tEnd, [])), ("User", (U1, []))]
def S9 : Network :=
  [("LocalDNS", (L4, [mEI])), ("ExtAuthDNS", (SessionType.tEnd, [])),
   ("IntAuthDNS", (SessionType.tEnd, [])), ("User", (U1, []))]
def S10 : Network :=
  [("LocalDNS", (L5, [])), ("ExtAuthDNS", (SessionType.tEnd, [])),
   ("IntAuthDNS", (SessionType.tEnd, [])), ("User", (U1, []))]
def S11 : Network :=
  [("User", (U1, [mLI])), ("LocalDNS", (SessionType.tEnd, [])),
   ("ExtAuthDNS", (SessionType.tEnd, [])), ("IntAuthDNS", (SessionType.tEnd, []))]
def S12 : Network :=
  [("User", (SessionType.tEnd, [])), ("LocalDNS", (SessionType.tEnd, [])),
   ("ExtAuthDNS", (SessionType.tEnd, [])), ("IntAuthDNS", (SessionType.tEnd, []))]

-- Queue computations
theorem qUD : Queue.dequeue [mUD] mUD = some ([] : Queue) := rfl
theorem qLA : Queue.dequeue [mLA] mLA = some ([] : Queue) := rfl
theorem qIH : Queue.dequeue [mIH] mIH = some ([] : Queue) := rfl
theorem qEI : Queue.dequeue [mEI] mEI = some ([] : Queue) := rfl
theorem qLI : Queue.dequeue [mLI] mLI = some ([] : Queue) := rfl

theorem S0_step : ∀ (δ : net_label) (N' : Network),
    net_trans S0 δ N' → is_internal_net_label δ → N' = S1 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := User_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST =>
        have ho := User_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        have ho := User_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S1_step : ∀ (δ : net_label) (N' : Network),
    net_trans S1 δ N' → is_internal_net_label δ → N' = S2 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := LocalDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qUD] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S2_step : ∀ (δ : net_label) (N' : Network),
    net_trans S2 δ N' → is_internal_net_label δ → N' = S3 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        have ho := L1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := L1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST =>
        have ho := L1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S3_step : ∀ (δ : net_label) (N' : Network),
    net_trans S3 δ N' → is_internal_net_label δ → N' = S4 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := IntAuthDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLA] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => IntAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S4_step : ∀ (δ : net_label) (N' : Network),
    net_trans S4 δ N' → is_internal_net_label δ → N' = S5 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := I1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST =>
        have ho := I1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        have ho := I1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S5_step : ∀ (δ : net_label) (N' : Network),
    net_trans S5 δ N' → is_internal_net_label δ → N' = S6 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := L2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qIH] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S7 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        have ho := L3_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        have ho := L3_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := L3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · exact absurd rfl hne

theorem S7_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → N' = S8 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := ExtAuthDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLA] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => ExtAuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S9 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := E1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST =>
        have ho := E1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        have ho := E1_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := L4_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qEI] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => L4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne

theorem S10_step : ∀ (δ : net_label) (N' : Network),
    net_trans S10 δ N' → is_internal_net_label δ → N' = S11 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        have ho := L5_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        have ho := L5_out_iff hST
        obtain ⟨hEq, _, _, _⟩ := ho
        simp at hEq
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := L5_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · exact absurd rfl hne

theorem S11_step : ∀ (δ : net_label) (N' : Network),
    net_trans S11 δ N' → is_internal_net_label δ → N' = S12 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := U1_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLI] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => U1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S12_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

-- Reachability: every τ-reachable network is one of the 13 states.
-- (Auxiliary with variable start so `induction` applies; instantiate at `Net`.)
theorem cdnReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S4 ∨ N1 = S5 ∨ N1 = S6 ∨
    N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S10 ∨ N1 = S11 ∨ N1 = S12) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S4 ∨ N2 = S5 ∨ N2 = S6 ∨
    N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S10 ∨ N2 = S11 ∨ N2 = S12) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := S0_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S1_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S2_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S3_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S4_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S5_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S6_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S7_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S8_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S9_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S10_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S11_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · exact absurd (S12_no_step _ _ hTr hInt) id

theorem cdnReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S4 ∨ N' = S5 ∨ N' = S6 ∨
    N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S10 ∨ N' = S11 ∨ N' = S12) :=
  fun N' hStar => cdnReach_aux Net N' hStar (Or.inl rfl)

-- ============ Explicit transitions (reused for stuck + output-live) ============
theorem t01 : net_trans S0 (net_label.τ_comm "User" "LocalDNS" "DNSQuery" "unit") S1 := by
  have h_send : sq_trans (User, ([] : Queue))
      (sq_action.send "LocalDNS" "DNSQuery" "unit") (U1, []) := by
    apply sq_trans.send
    unfold User
    apply st_trans.intC
    simp [U1]
  have h_recv : sq_trans (LocalDNS, ([] : Queue))
      (sq_action.recv "User" "DNSQuery" "unit") (LocalDNS, [mUD]) :=
    sq_trans.recv
  have hmem_p : ("User", (User, ([] : Queue))) ∈ S0 := by simp [S0]
  have hmem_q : ("LocalDNS", (LocalDNS, ([] : Queue))) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t12 :
    net_trans S1 (net_label.τ_dequeue "LocalDNS" "User" "DNSQuery" "unit") S2 := by
  have hSQ : sq_trans (LocalDNS, [mUD])
      (sq_action.dequeue "User" "DNSQuery" "unit") (L1, []) := by
    apply sq_trans.dequeue
    · unfold LocalDNS
      apply st_trans.extC
      simp [L1, L2, L3, L4, L5]
    · exact qUD
  have hmem : ("LocalDNS", (LocalDNS, [mUD])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem

theorem t23 :
    net_trans S2 (net_label.τ_comm "LocalDNS" "IntAuthDNS" "AuthQuery" "unit") S3 := by
  have h_send : sq_trans (L1, ([] : Queue))
      (sq_action.send "IntAuthDNS" "AuthQuery" "unit") (L2, []) := by
    apply sq_trans.send
    unfold L1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (IntAuthDNS, ([] : Queue))
      (sq_action.recv "LocalDNS" "AuthQuery" "unit") (IntAuthDNS, [mLA]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (L1, ([] : Queue))) ∈ S2 := by simp [S2]
  have hmem_q : ("IntAuthDNS", (IntAuthDNS, ([] : Queue))) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t34 :
    net_trans S3 (net_label.τ_dequeue "IntAuthDNS" "LocalDNS" "AuthQuery" "unit") S4 := by
  have hSQ : sq_trans (IntAuthDNS, [mLA])
      (sq_action.dequeue "LocalDNS" "AuthQuery" "unit") (I1, []) := by
    apply sq_trans.dequeue
    · unfold IntAuthDNS
      apply st_trans.extC
      simp [I1]
    · exact qLA
  have hmem : ("IntAuthDNS", (IntAuthDNS, [mLA])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem

theorem t45 :
    net_trans S4 (net_label.τ_comm "IntAuthDNS" "LocalDNS" "Hostname" "unit") S5 := by
  have h_send : sq_trans (I1, ([] : Queue))
      (sq_action.send "LocalDNS" "Hostname" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold I1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (L2, ([] : Queue))
      (sq_action.recv "IntAuthDNS" "Hostname" "unit") (L2, [mIH]) :=
    sq_trans.recv
  have hmem_p : ("IntAuthDNS", (I1, ([] : Queue))) ∈ S4 := by simp [S4]
  have hmem_q : ("LocalDNS", (L2, ([] : Queue))) ∈ S4 := by simp [S4]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t56 :
    net_trans S5 (net_label.τ_dequeue "LocalDNS" "IntAuthDNS" "Hostname" "unit") S6 := by
  have hSQ : sq_trans (L2, [mIH])
      (sq_action.dequeue "IntAuthDNS" "Hostname" "unit") (L3, []) := by
    apply sq_trans.dequeue
    · unfold L2
      apply st_trans.extC
      simp [L3]
    · exact qIH
  have hmem : ("LocalDNS", (L2, [mIH])) ∈ S5 := by simp [S5]
  exact net_trans.dequeue hSQ hmem

theorem t67 :
    net_trans S6 (net_label.τ_comm "LocalDNS" "ExtAuthDNS" "AuthQuery" "unit") S7 := by
  have h_send : sq_trans (L3, ([] : Queue))
      (sq_action.send "ExtAuthDNS" "AuthQuery" "unit") (L4, []) := by
    apply sq_trans.send
    unfold L3
    apply st_trans.intC
    simp [L4]
  have h_recv : sq_trans (ExtAuthDNS, ([] : Queue))
      (sq_action.recv "LocalDNS" "AuthQuery" "unit") (ExtAuthDNS, [mLA]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (L3, ([] : Queue))) ∈ S6 := by simp [S6]
  have hmem_q : ("ExtAuthDNS", (ExtAuthDNS, ([] : Queue))) ∈ S6 := by simp [S6]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t78 :
    net_trans S7 (net_label.τ_dequeue "ExtAuthDNS" "LocalDNS" "AuthQuery" "unit") S8 := by
  have hSQ : sq_trans (ExtAuthDNS, [mLA])
      (sq_action.dequeue "LocalDNS" "AuthQuery" "unit") (E1, []) := by
    apply sq_trans.dequeue
    · unfold ExtAuthDNS
      apply st_trans.extC
      simp [E1]
    · exact qLA
  have hmem : ("ExtAuthDNS", (ExtAuthDNS, [mLA])) ∈ S7 := by simp [S7]
  exact net_trans.dequeue hSQ hmem

theorem t89 :
    net_trans S8 (net_label.τ_comm "ExtAuthDNS" "LocalDNS" "IPAddr" "unit") S9 := by
  have h_send : sq_trans (E1, ([] : Queue))
      (sq_action.send "LocalDNS" "IPAddr" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold E1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (L4, ([] : Queue))
      (sq_action.recv "ExtAuthDNS" "IPAddr" "unit") (L4, [mEI]) :=
    sq_trans.recv
  have hmem_p : ("ExtAuthDNS", (E1, ([] : Queue))) ∈ S8 := by simp [S8]
  have hmem_q : ("LocalDNS", (L4, ([] : Queue))) ∈ S8 := by simp [S8]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t910 :
    net_trans S9 (net_label.τ_dequeue "LocalDNS" "ExtAuthDNS" "IPAddr" "unit") S10 := by
  have hSQ : sq_trans (L4, [mEI])
      (sq_action.dequeue "ExtAuthDNS" "IPAddr" "unit") (L5, []) := by
    apply sq_trans.dequeue
    · unfold L4
      apply st_trans.extC
      simp [L5]
    · exact qEI
  have hmem : ("LocalDNS", (L4, [mEI])) ∈ S9 := by simp [S9]
  exact net_trans.dequeue hSQ hmem

theorem t1011 :
    net_trans S10 (net_label.τ_comm "LocalDNS" "User" "IPAddr" "unit") S11 := by
  have h_send : sq_trans (L5, ([] : Queue))
      (sq_action.send "User" "IPAddr" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold L5
    apply st_trans.intC
    simp
  have h_recv : sq_trans (U1, ([] : Queue))
      (sq_action.recv "LocalDNS" "IPAddr" "unit") (U1, [mLI]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (L5, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("User", (U1, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t1112 :
    net_trans S11 (net_label.τ_dequeue "User" "LocalDNS" "IPAddr" "unit") S12 := by
  have hSQ : sq_trans (U1, [mLI])
      (sq_action.dequeue "LocalDNS" "IPAddr" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold U1
      apply st_trans.extC
      simp
    · exact qLI
  have hmem : ("User", (U1, [mLI])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem

-- ============ Half-duplex ============
/-- `Net` is half-duplex: opposite queues never both fill. -/
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := cdnReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil

-- ============ Output-liveness: infinite fair paths ============
/-- Every infinite fair path from `Net` is output-live. -/
theorem cdnOL_inf : IsOutputLiveInfinitePathNetwork Net := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  have hStar : net_trans_star Net (path.seq i) := path_star_reachable h0 i
  have hR := cdnReach _ hStar
  rcases hR with h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mUD] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "User" := congrArg (fun m => m.1) hmem
      have hlab : lab = "DNSQuery" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "User" "DNSQuery" "unit"
        ⟨S2, by rw [h]; exact t12⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLA] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "AuthQuery" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "IntAuthDNS" "LocalDNS" "AuthQuery" "unit"
        ⟨S4, by rw [h]; exact t34⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mIH] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "IntAuthDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Hostname" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "IntAuthDNS" "Hostname" "unit"
        ⟨S6, by rw [h]; exact t56⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLA] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "AuthQuery" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ExtAuthDNS" "LocalDNS" "AuthQuery" "unit"
        ⟨S8, by rw [h]; exact t78⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEI] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ExtAuthDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "IPAddr" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "ExtAuthDNS" "IPAddr" "unit"
        ⟨S10, by rw [h]; exact t910⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLI] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "IPAddr" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "User" "LocalDNS" "IPAddr" "unit"
        ⟨S12, by rw [h]; exact t1112⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)

-- ============ Output-liveness: stuck states have no orphans ============
/-- Every reachable stuck network from `Net` has no orphans. -/
theorem cdnOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := cdnReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact hStuck ⟨_, _, by trivial, t01⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t12⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t23⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t34⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t45⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t56⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t67⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t78⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t89⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t910⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1011⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1112⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

/-- `Net` is output-live: fair paths drain queues, stuck states are clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨cdnOL_inf, cdnOL_stuck⟩

end Cdn
