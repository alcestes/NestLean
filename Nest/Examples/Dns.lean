import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun

namespace Dns

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/05_dns.scala`
   (Scala package `dns`; file `05_dns.scala` maps to this module since
   Lean module names may not start with a digit).
   Translated below are the five `lst_*` local session types
   (`lst_DNSClient`, `lst_LocalDNS`, `lst_RootDNS`, `lst_TLDDNS`,
   `lst_AuthDNS`). The file imports `vpn.a_Auth` but no session type
   below uses it. Switch setup, IP rules, port checks and monitor
   wiring from `setup` are not session types and are not translated.
   Translation conventions: `IntChoice` branches become
   `internalChoice` branches `(agent, label, sort, cont)`; `ExtChoice`
   branches become `externalChoice` branches `(label, sort, cont)`;
   `Rec`/`Var`/`End` become `tRec`/`tVar`/`tEnd` (none of these types
   use recursion). Agents become roles, labels stay labels. The Scala
   types carry no payload sorts, so every branch uses the placeholder
   sort `"unit"`. -/

/-- `lst_DNSClient`. -/
def DNSClient : SessionType :=
  SessionType.internalChoice
    [("LocalDNS", "RqsIP", "unit",
      SessionType.externalChoice "LocalDNS"
        [("RspIP", "unit", SessionType.tEnd)])]

/-- `lst_LocalDNS`. -/
def LocalDNS : SessionType :=
  SessionType.externalChoice "Client"
    [("RqsIP", "unit",
      SessionType.internalChoice
        [("RootDNS", "RqsRoot", "unit",
          SessionType.externalChoice "RootDNS"
            [("RspRoot", "unit",
              SessionType.internalChoice
                [("TLDDNS", "RqsTLD", "unit",
                  SessionType.externalChoice "TLDDNS"
                    [("RspTLD", "unit",
                      SessionType.internalChoice
                        [("AuthDNS", "RqsAuth", "unit",
                          SessionType.externalChoice "AuthDNS"
                            [("RspAuth", "unit",
                              SessionType.internalChoice
                                [("Client", "RspIP", "unit",
                                  SessionType.tEnd)])])])])])])])]

/-- `lst_RootDNS`. -/
def RootDNS : SessionType :=
  SessionType.externalChoice "LocalDNS"
    [("RqsRoot", "unit",
      SessionType.internalChoice
        [("LocalDNS", "RspRoot", "unit", SessionType.tEnd)])]

/-- `lst_TLDDNS`. -/
def TLDDNS : SessionType :=
  SessionType.externalChoice "LocalDNS"
    [("RqsTLD", "unit",
      SessionType.internalChoice
        [("LocalDNS", "RspTLD", "unit", SessionType.tEnd)])]

/-- `lst_AuthDNS`. -/
def AuthDNS : SessionType :=
  SessionType.externalChoice "LocalDNS"
    [("RqsAuth", "unit",
      SessionType.internalChoice
        [("LocalDNS", "RspAuth", "unit", SessionType.tEnd)])]

-- All five types are recursion-free: certified by the generic `NoRec` lemmas.
/-- `DNSClient` is recursion-free (boolean check). -/
theorem DNSClient_norec : DNSClient.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `DNSClient` (empty seen set, via recursion-freedom). -/
theorem DNSClient_deep : Prunable [] DNSClient :=
  norec_deep DNSClient_norec []
/-- Monitorability of `DNSClient` (finite prune closure, via recursion-freedom). -/
theorem DNSClient_mon : Drainability.Monitorable DNSClient :=
  norec_monitorable DNSClient_norec

/-- `LocalDNS` is recursion-free (boolean check). -/
theorem LocalDNS_norec : LocalDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `LocalDNS` (empty seen set, via recursion-freedom). -/
theorem LocalDNS_deep : Prunable [] LocalDNS :=
  norec_deep LocalDNS_norec []
/-- Monitorability of `LocalDNS` (finite prune closure, via recursion-freedom). -/
theorem LocalDNS_mon : Drainability.Monitorable LocalDNS :=
  norec_monitorable LocalDNS_norec

/-- `RootDNS` is recursion-free (boolean check). -/
theorem RootDNS_norec : RootDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `RootDNS` (empty seen set, via recursion-freedom). -/
theorem RootDNS_deep : Prunable [] RootDNS :=
  norec_deep RootDNS_norec []
/-- Monitorability of `RootDNS` (finite prune closure, via recursion-freedom). -/
theorem RootDNS_mon : Drainability.Monitorable RootDNS :=
  norec_monitorable RootDNS_norec

/-- `TLDDNS` is recursion-free (boolean check). -/
theorem TLDDNS_norec : TLDDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `TLDDNS` (empty seen set, via recursion-freedom). -/
theorem TLDDNS_deep : Prunable [] TLDDNS :=
  norec_deep TLDDNS_norec []
/-- Monitorability of `TLDDNS` (finite prune closure, via recursion-freedom). -/
theorem TLDDNS_mon : Drainability.Monitorable TLDDNS :=
  norec_monitorable TLDDNS_norec

/-- `AuthDNS` is recursion-free (boolean check). -/
theorem AuthDNS_norec : AuthDNS.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `AuthDNS` (empty seen set, via recursion-freedom). -/
theorem AuthDNS_deep : Prunable [] AuthDNS :=
  norec_deep AuthDNS_norec []
/-- Monitorability of `AuthDNS` (finite prune closure, via recursion-freedom). -/
theorem AuthDNS_mon : Drainability.Monitorable AuthDNS :=
  norec_monitorable AuthDNS_norec

/-- Empty-queue network for the five DNS roles. -/
def Net : Network :=
  [("Client", (DNSClient, [])),
   ("LocalDNS", (LocalDNS, [])),
   ("RootDNS", (RootDNS, [])),
   ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact DNSClient.wfCheck_sound (by decide)
  · exact LocalDNS.wfCheck_sound (by decide)
  · exact RootDNS.wfCheck_sound (by decide)
  · exact TLDDNS.wfCheck_sound (by decide)
  · exact AuthDNS.wfCheck_sound (by decide)

/-- `Net` has no self-mention: each role is absent from its own type. -/
theorem Net_noSelf : Net.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide

/-- `Net` contains every role occurring in its member types. -/
theorem Net_rolesPresent : Net.RolesPresent := by
  intro q T Q s hmem hOcc
  have hmemR : s ∈ rolesOf T := occurs_mem hOcc
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [DNSClient, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩
  · simp only [LocalDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(DNSClient, []), by decide⟩
    · exact ⟨(RootDNS, []), by decide⟩
    · exact ⟨(RootDNS, []), by decide⟩
    · exact ⟨(TLDDNS, []), by decide⟩
    · exact ⟨(TLDDNS, []), by decide⟩
    · exact ⟨(AuthDNS, []), by decide⟩
    · exact ⟨(AuthDNS, []), by decide⟩
    · exact ⟨(DNSClient, []), by decide⟩
  · simp only [RootDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩
  · simp only [TLDDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩
  · simp only [AuthDNS, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(LocalDNS, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)

/-- Client continuation after sending `RqsIP` (waits for `RspIP`). -/
def DnsC1 : SessionType :=
  SessionType.externalChoice "LocalDNS" [("RspIP", "unit", SessionType.tEnd)]
/-- LocalDNS continuation after dequeuing `RqsIP` (sends `RqsRoot`). -/
def DnsL7 : SessionType :=
  SessionType.internalChoice [("Client", "RspIP", "unit", SessionType.tEnd)]
/-- LocalDNS continuation after sending `RqsAuth` (waits for `RspAuth`). -/
def DnsL6 : SessionType :=
  SessionType.externalChoice "AuthDNS" [("RspAuth", "unit", DnsL7)]
/-- LocalDNS continuation after dequeuing `RspTLD` (sends `RqsAuth`). -/
def DnsL5 : SessionType :=
  SessionType.internalChoice [("AuthDNS", "RqsAuth", "unit", DnsL6)]
/-- LocalDNS continuation after sending `RqsTLD` (waits for `RspTLD`). -/
def DnsL4 : SessionType :=
  SessionType.externalChoice "TLDDNS" [("RspTLD", "unit", DnsL5)]
/-- LocalDNS continuation after dequeuing `RspRoot` (sends `RqsTLD`). -/
def DnsL3 : SessionType :=
  SessionType.internalChoice [("TLDDNS", "RqsTLD", "unit", DnsL4)]
/-- LocalDNS continuation after sending `RqsRoot` (waits for `RspRoot`). -/
def DnsL2 : SessionType :=
  SessionType.externalChoice "RootDNS" [("RspRoot", "unit", DnsL3)]
/-- LocalDNS continuation after dequeuing `RqsIP` (sends `RqsRoot`). -/
def DnsL1 : SessionType :=
  SessionType.internalChoice [("RootDNS", "RqsRoot", "unit", DnsL2)]
/-- RootDNS continuation after dequeuing `RqsRoot` (sends `RspRoot`). -/
def DnsR1 : SessionType :=
  SessionType.internalChoice [("LocalDNS", "RspRoot", "unit", SessionType.tEnd)]
/-- TLDDNS continuation after dequeuing `RqsTLD` (sends `RspTLD`). -/
def DnsT1 : SessionType :=
  SessionType.internalChoice [("LocalDNS", "RspTLD", "unit", SessionType.tEnd)]
/-- AuthDNS continuation after dequeuing `RqsAuth` (sends `RspAuth`). -/
def DnsA1 : SessionType :=
  SessionType.internalChoice [("LocalDNS", "RspAuth", "unit", SessionType.tEnd)]

-- ============ OUT-step characterizations ============
/-- `DNSClient` sends `RqsIP` to `LocalDNS` and continues as `DnsC1`. -/
theorem DNSClient_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DNSClient (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "RqsIP" ∧ S = "unit" ∧ T' = DnsC1 := by
  intro h
  unfold DNSClient at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsC1` never sends. -/
theorem DnsC1_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsC1 (st_label.out p lab S) T') : False := by
  unfold DnsC1 at h
  cases h
/-- `LocalDNS` never sends (external offer). -/
theorem LocalDNS_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans LocalDNS (st_label.out p lab S) T') : False := by
  unfold LocalDNS at h
  cases h
/-- `DnsL1` sends `RqsRoot` to `RootDNS` and continues as `DnsL2`. -/
theorem DnsL1_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL1 (st_label.out p lab S) T' →
    p = "RootDNS" ∧ lab = "RqsRoot" ∧ S = "unit" ∧ T' = DnsL2 := by
  intro h
  unfold DnsL1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL2` never sends. -/
theorem DnsL2_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL2 (st_label.out p lab S) T') : False := by
  unfold DnsL2 at h
  cases h
/-- `DnsL3` sends `RqsTLD` to `TLDDNS` and continues as `DnsL4`. -/
theorem DnsL3_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL3 (st_label.out p lab S) T' →
    p = "TLDDNS" ∧ lab = "RqsTLD" ∧ S = "unit" ∧ T' = DnsL4 := by
  intro h
  unfold DnsL3 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL4` never sends. -/
theorem DnsL4_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL4 (st_label.out p lab S) T') : False := by
  unfold DnsL4 at h
  cases h
/-- `DnsL5` sends `RqsAuth` to `AuthDNS` and continues as `DnsL6`. -/
theorem DnsL5_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL5 (st_label.out p lab S) T' →
    p = "AuthDNS" ∧ lab = "RqsAuth" ∧ S = "unit" ∧ T' = DnsL6 := by
  intro h
  unfold DnsL5 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL6` never sends. -/
theorem DnsL6_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL6 (st_label.out p lab S) T') : False := by
  unfold DnsL6 at h
  cases h
/-- `DnsL7` sends `RspIP` to `Client` and ends. -/
theorem DnsL7_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL7 (st_label.out p lab S) T' →
    p = "Client" ∧ lab = "RspIP" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold DnsL7 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `RootDNS` never sends. -/
theorem RootDNS_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans RootDNS (st_label.out p lab S) T') : False := by
  unfold RootDNS at h
  cases h
/-- `DnsR1` sends `RspRoot` to `LocalDNS` and ends. -/
theorem DnsR1_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsR1 (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "RspRoot" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold DnsR1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `TLDDNS` never sends. -/
theorem TLDDNS_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans TLDDNS (st_label.out p lab S) T') : False := by
  unfold TLDDNS at h
  cases h
/-- `DnsT1` sends `RspTLD` to `LocalDNS` and ends. -/
theorem DnsT1_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsT1 (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "RspTLD" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold DnsT1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `AuthDNS` never sends. -/
theorem AuthDNS_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans AuthDNS (st_label.out p lab S) T') : False := by
  unfold AuthDNS at h
  cases h
/-- `DnsA1` sends `RspAuth` to `LocalDNS` and ends. -/
theorem DnsA1_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsA1 (st_label.out p lab S) T' →
    p = "LocalDNS" ∧ lab = "RspAuth" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold DnsA1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `tEnd` never sends. -/
theorem tEnd_no_out_dns {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

-- ============ INP-step characterizations ============
/-- `DNSClient` never receives. -/
theorem DNSClient_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DNSClient (st_label.inp p lab S) T') : False := by
  unfold DNSClient at h
  cases h
/-- `DnsC1` receives `RspIP` from `LocalDNS` and ends. -/
theorem DnsC1_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsC1 (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "RspIP" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold DnsC1 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `LocalDNS` receives `RqsIP` from `Client` and continues as `DnsL1`. -/
theorem LocalDNS_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans LocalDNS (st_label.inp p lab S) T' →
    p = "Client" ∧ lab = "RqsIP" ∧ S = "unit" ∧ T' = DnsL1 := by
  intro h
  unfold LocalDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL1` never receives. -/
theorem DnsL1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL1 (st_label.inp p lab S) T') : False := by
  unfold DnsL1 at h
  cases h
/-- `DnsL2` receives `RspRoot` from `RootDNS` and continues as `DnsL3`. -/
theorem DnsL2_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL2 (st_label.inp p lab S) T' →
    p = "RootDNS" ∧ lab = "RspRoot" ∧ S = "unit" ∧ T' = DnsL3 := by
  intro h
  unfold DnsL2 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL3` never receives. -/
theorem DnsL3_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL3 (st_label.inp p lab S) T') : False := by
  unfold DnsL3 at h
  cases h
/-- `DnsL4` receives `RspTLD` from `TLDDNS` and continues as `DnsL5`. -/
theorem DnsL4_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL4 (st_label.inp p lab S) T' →
    p = "TLDDNS" ∧ lab = "RspTLD" ∧ S = "unit" ∧ T' = DnsL5 := by
  intro h
  unfold DnsL4 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL5` never receives. -/
theorem DnsL5_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL5 (st_label.inp p lab S) T') : False := by
  unfold DnsL5 at h
  cases h
/-- `DnsL6` receives `RspAuth` from `AuthDNS` and continues as `DnsL7`. -/
theorem DnsL6_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans DnsL6 (st_label.inp p lab S) T' →
    p = "AuthDNS" ∧ lab = "RspAuth" ∧ S = "unit" ∧ T' = DnsL7 := by
  intro h
  unfold DnsL6 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsL7` never receives. -/
theorem DnsL7_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsL7 (st_label.inp p lab S) T') : False := by
  unfold DnsL7 at h
  cases h
/-- `RootDNS` receives `RqsRoot` from `LocalDNS` and continues as `DnsR1`. -/
theorem RootDNS_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans RootDNS (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "RqsRoot" ∧ S = "unit" ∧ T' = DnsR1 := by
  intro h
  unfold RootDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsR1` never receives. -/
theorem DnsR1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsR1 (st_label.inp p lab S) T') : False := by
  unfold DnsR1 at h
  cases h
/-- `TLDDNS` receives `RqsTLD` from `LocalDNS` and continues as `DnsT1`. -/
theorem TLDDNS_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans TLDDNS (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "RqsTLD" ∧ S = "unit" ∧ T' = DnsT1 := by
  intro h
  unfold TLDDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsT1` never receives. -/
theorem DnsT1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsT1 (st_label.inp p lab S) T') : False := by
  unfold DnsT1 at h
  cases h
/-- `AuthDNS` receives `RqsAuth` from `LocalDNS` and continues as `DnsA1`. -/
theorem AuthDNS_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans AuthDNS (st_label.inp p lab S) T' →
    p = "LocalDNS" ∧ lab = "RqsAuth" ∧ S = "unit" ∧ T' = DnsA1 := by
  intro h
  unfold AuthDNS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
/-- `DnsA1` never receives. -/
theorem DnsA1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans DnsA1 (st_label.inp p lab S) T') : False := by
  unfold DnsA1 at h
  cases h
/-- `tEnd` never receives. -/
theorem tEnd_no_inp_dns {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h

-- ============ Reachable states (whole-network enumeration) ============
abbrev mCRqsIP : QueueMessage := QueueMessage.msg "Client" "RqsIP" "unit"
abbrev mLRqsRoot : QueueMessage := QueueMessage.msg "LocalDNS" "RqsRoot" "unit"
abbrev mRRspRoot : QueueMessage := QueueMessage.msg "RootDNS" "RspRoot" "unit"
abbrev mLRqsTLD : QueueMessage := QueueMessage.msg "LocalDNS" "RqsTLD" "unit"
abbrev mTRspTLD : QueueMessage := QueueMessage.msg "TLDDNS" "RspTLD" "unit"
abbrev mLRqsAuth : QueueMessage := QueueMessage.msg "LocalDNS" "RqsAuth" "unit"
abbrev mARspAuth : QueueMessage := QueueMessage.msg "AuthDNS" "RspAuth" "unit"
abbrev mLRspIP : QueueMessage := QueueMessage.msg "LocalDNS" "RspIP" "unit"

/-- Initial network (equals `Net`). -/
def S0 : Network :=
  [("Client", (DNSClient, [])), ("LocalDNS", (LocalDNS, [])),
   ("RootDNS", (RootDNS, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `Client → LocalDNS : RqsIP` (queued at `LocalDNS`). -/
def S1 : Network :=
  [("LocalDNS", (LocalDNS, [mCRqsIP])), ("Client", (DnsC1, [])),
   ("RootDNS", (RootDNS, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS` dequeues `RqsIP` (ready to send `RqsRoot`). -/
def S2 : Network :=
  [("LocalDNS", (DnsL1, [])), ("Client", (DnsC1, [])),
   ("RootDNS", (RootDNS, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS → RootDNS : RqsRoot` (queued at `RootDNS`). -/
def S3 : Network :=
  [("RootDNS", (RootDNS, [mLRqsRoot])), ("LocalDNS", (DnsL2, [])),
   ("Client", (DnsC1, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `RootDNS` dequeues `RqsRoot` (ready to send `RspRoot`). -/
def S4 : Network :=
  [("RootDNS", (DnsR1, [])), ("LocalDNS", (DnsL2, [])),
   ("Client", (DnsC1, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `RootDNS → LocalDNS : RspRoot` (queued at `LocalDNS`). -/
def S5 : Network :=
  [("LocalDNS", (DnsL2, [mRRspRoot])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, [])),
   ("TLDDNS", (TLDDNS, [])), ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS` dequeues `RspRoot` (ready to send `RqsTLD`). -/
def S6 : Network :=
  [("LocalDNS", (DnsL3, [])), ("RootDNS", (SessionType.tEnd, [])),
   ("Client", (DnsC1, [])), ("TLDDNS", (TLDDNS, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS → TLDDNS : RqsTLD` (queued at `TLDDNS`). -/
def S7 : Network :=
  [("TLDDNS", (TLDDNS, [mLRqsTLD])), ("LocalDNS", (DnsL4, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `TLDDNS` dequeues `RqsTLD` (ready to send `RspTLD`). -/
def S8 : Network :=
  [("TLDDNS", (DnsT1, [])), ("LocalDNS", (DnsL4, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `TLDDNS → LocalDNS : RspTLD` (queued at `LocalDNS`). -/
def S9 : Network :=
  [("LocalDNS", (DnsL4, [mTRspTLD])),
   ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS` dequeues `RspTLD` (ready to send `RqsAuth`). -/
def S10 : Network :=
  [("LocalDNS", (DnsL5, [])), ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, [])),
   ("AuthDNS", (AuthDNS, []))]
/-- After `LocalDNS → AuthDNS : RqsAuth` (queued at `AuthDNS`). -/
def S11 : Network :=
  [("AuthDNS", (AuthDNS, [mLRqsAuth])), ("LocalDNS", (DnsL6, [])),
   ("TLDDNS", (SessionType.tEnd, [])), ("RootDNS", (SessionType.tEnd, [])),
   ("Client", (DnsC1, []))]
/-- After `AuthDNS` dequeues `RqsAuth` (ready to send `RspAuth`). -/
def S12 : Network :=
  [("AuthDNS", (DnsA1, [])), ("LocalDNS", (DnsL6, [])),
   ("TLDDNS", (SessionType.tEnd, [])), ("RootDNS", (SessionType.tEnd, [])),
   ("Client", (DnsC1, []))]
/-- After `AuthDNS → LocalDNS : RspAuth` (queued at `LocalDNS`). -/
def S13 : Network :=
  [("LocalDNS", (DnsL6, [mARspAuth])),
   ("AuthDNS", (SessionType.tEnd, [])),
   ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, []))]
/-- After `LocalDNS` dequeues `RspAuth` (ready to send `RspIP`). -/
def S14 : Network :=
  [("LocalDNS", (DnsL7, [])), ("AuthDNS", (SessionType.tEnd, [])),
   ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, [])), ("Client", (DnsC1, []))]
/-- After `LocalDNS → Client : RspIP` (queued at `Client`). -/
def S15 : Network :=
  [("Client", (DnsC1, [mLRspIP])),
   ("LocalDNS", (SessionType.tEnd, [])),
   ("AuthDNS", (SessionType.tEnd, [])),
   ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, []))]
/-- Terminal network (all `tEnd`, all queues empty). -/
def S16 : Network :=
  [("Client", (SessionType.tEnd, [])),
   ("LocalDNS", (SessionType.tEnd, [])),
   ("AuthDNS", (SessionType.tEnd, [])),
   ("TLDDNS", (SessionType.tEnd, [])),
   ("RootDNS", (SessionType.tEnd, []))]

-- Queue computations
/-- Dequeues `RqsIP` from `Client` at `LocalDNS`. -/
theorem qCRqsIP : Queue.dequeue [mCRqsIP] mCRqsIP = some ([] : Queue) := rfl
/-- Dequeues `RqsRoot` from `LocalDNS` at `RootDNS`. -/
theorem qLRqsRoot : Queue.dequeue [mLRqsRoot] mLRqsRoot = some ([] : Queue) := rfl
/-- Dequeues `RspRoot` from `RootDNS` at `LocalDNS`. -/
theorem qRRspRoot : Queue.dequeue [mRRspRoot] mRRspRoot = some ([] : Queue) := rfl
/-- Dequeues `RqsTLD` from `LocalDNS` at `TLDDNS`. -/
theorem qLRqsTLD : Queue.dequeue [mLRqsTLD] mLRqsTLD = some ([] : Queue) := rfl
/-- Dequeues `RspTLD` from `TLDDNS` at `LocalDNS`. -/
theorem qTRspTLD : Queue.dequeue [mTRspTLD] mTRspTLD = some ([] : Queue) := rfl
/-- Dequeues `RqsAuth` from `LocalDNS` at `AuthDNS`. -/
theorem qLRqsAuth : Queue.dequeue [mLRqsAuth] mLRqsAuth = some ([] : Queue) := rfl
/-- Dequeues `RspAuth` from `AuthDNS` at `LocalDNS`. -/
theorem qARspAuth : Queue.dequeue [mARspAuth] mARspAuth = some ([] : Queue) := rfl
/-- Dequeues `RspIP` from `LocalDNS` at `Client`. -/
theorem qLRspIP : Queue.dequeue [mLRspIP] mLRspIP = some ([] : Queue) := rfl

theorem S0_step : ∀ (δ : net_label) (N' : Network),
    net_trans S0 δ N' → is_internal_net_label δ → N' = S1 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DNSClient_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DNSClient_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DNSClient_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DNSClient_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => RootDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S1_step : ∀ (δ : net_label) (N' : Network),
    net_trans S1 δ N' → is_internal_net_label δ → N' = S2 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := LocalDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qCRqsIP] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => LocalDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => RootDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S2_step : ∀ (δ : net_label) (N' : Network),
    net_trans S2 δ N' → is_internal_net_label δ → N' = S3 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          have ho := DnsL1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsL1_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DnsL1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => RootDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S3_step : ∀ (δ : net_label) (N' : Network),
    net_trans S3 δ N' → is_internal_net_label δ → N' = S4 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := RootDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLRqsRoot] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => RootDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S4_step : ∀ (δ : net_label) (N' : Network),
    net_trans S4 δ N' → is_internal_net_label δ → N' = S5 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsR1_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DnsR1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsR1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsR1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S5_step : ∀ (δ : net_label) (N' : Network),
    net_trans S5 δ N' → is_internal_net_label δ → N' = S6 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := DnsL2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRRspRoot] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S7 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          have ho := DnsL3_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL3_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsL3_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DnsL3_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S7_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → N' = S8 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := TLDDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLRqsTLD] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => TLDDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S9 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsT1_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DnsT1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsT1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsT1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := DnsL4_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qTRspTLD] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S10_step : ∀ (δ : net_label) (N' : Network),
    net_trans S10 δ N' → is_internal_net_label δ → N' = S11 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          have ho := DnsL5_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL5_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL5_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsL5_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)

theorem S11_step : ∀ (δ : net_label) (N' : Network),
    net_trans S11 δ N' → is_internal_net_label δ → N' = S12 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := AuthDNS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLRqsAuth] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => AuthDNS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL6_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)

theorem S12_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → N' = S13 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsA1_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
      · cases h_send with
        | send hST =>
          have ho := DnsA1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsA1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsA1_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL6_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)

theorem S13_step : ∀ (δ : net_label) (N' : Network),
    net_trans S13 δ N' → is_internal_net_label δ → N' = S14 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := DnsL6_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qARspAuth] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsL6_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)

theorem S14_step : ∀ (δ : net_label) (N' : Network),
    net_trans S14 δ N' → is_internal_net_label δ → N' = S15 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · cases h_send with
        | send hST =>
          have ho := DnsL7_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL7_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          have ho := DnsL7_out_iff hST
          obtain ⟨h1, _, _, _⟩ := ho
          simp at h1
      · cases h_send with
        | send hST =>
          cases h_recv with
          | recv =>
            have ho := DnsL7_out_iff hST
            obtain ⟨-, rfl, rfl, rfl⟩ := ho
            rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)

theorem S15_step : ∀ (δ : net_label) (N' : Network),
    net_trans S15 δ N' → is_internal_net_label δ → N' = S16 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := DnsC1_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qLRspIP] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => DnsC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)

theorem S16_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S16 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_dns h)

-- Reachability: every τ-reachable network is one of the 17 states.
-- (Auxiliary with variable start so `induction` applies; instantiate at `Net`.)
theorem dnsReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S4 ∨ N1 = S5 ∨ N1 = S6 ∨
     N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S10 ∨ N1 = S11 ∨ N1 = S12 ∨
     N1 = S13 ∨ N1 = S14 ∨ N1 = S15 ∨ N1 = S16) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S4 ∨ N2 = S5 ∨ N2 = S6 ∨
     N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S10 ∨ N2 = S11 ∨ N2 = S12 ∨
     N2 = S13 ∨ N2 = S14 ∨ N2 = S15 ∨ N2 = S16) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · have h := S12_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S13_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S14_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S15_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · exact absurd (S16_no_step _ _ hTr hInt) id

theorem dnsReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S4 ∨ N' = S5 ∨ N' = S6 ∨
     N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S10 ∨ N' = S11 ∨ N' = S12 ∨
     N' = S13 ∨ N' = S14 ∨ N' = S15 ∨ N' = S16) := by
  intro N' hStar
  have hS0 : S0 = Net := rfl
  have hStar' : net_trans_star S0 N' := by rw [hS0]; exact hStar
  have h0 : S0 = S0 ∨ S0 = S1 ∨ S0 = S2 ∨ S0 = S3 ∨ S0 = S4 ∨ S0 = S5 ∨ S0 = S6 ∨
      S0 = S7 ∨ S0 = S8 ∨ S0 = S9 ∨ S0 = S10 ∨ S0 = S11 ∨ S0 = S12 ∨
      S0 = S13 ∨ S0 = S14 ∨ S0 = S15 ∨ S0 = S16 := Or.inl rfl
  exact dnsReach_aux S0 N' hStar' h0

-- ============ Explicit transitions (reused for stuck + output-live) ============
theorem t01 : net_trans S0 (net_label.τ_comm "Client" "LocalDNS" "RqsIP" "unit") S1 := by
  have h_send : sq_trans (DNSClient, ([] : Queue))
      (sq_action.send "LocalDNS" "RqsIP" "unit") (DnsC1, []) := by
    apply sq_trans.send
    have hEq : DNSClient =
        SessionType.internalChoice [("LocalDNS", "RqsIP", "unit", DnsC1)] := rfl
    rw [hEq]
    apply st_trans.intC
    simp
  have h_recv : sq_trans (LocalDNS, ([] : Queue))
      (sq_action.recv "Client" "RqsIP" "unit") (LocalDNS, [mCRqsIP]) :=
    sq_trans.recv
  have hmem_p : ("Client", (DNSClient, ([] : Queue))) ∈ S0 := by simp [S0]
  have hmem_q : ("LocalDNS", (LocalDNS, ([] : Queue))) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t12 : net_trans S1 (net_label.τ_dequeue "LocalDNS" "Client" "RqsIP" "unit") S2 := by
  have hSQ : sq_trans (LocalDNS, [mCRqsIP])
      (sq_action.dequeue "Client" "RqsIP" "unit") (DnsL1, []) := by
    apply sq_trans.dequeue
    · have hEq : LocalDNS =
          SessionType.externalChoice "Client" [("RqsIP", "unit", DnsL1)] := rfl
      rw [hEq]
      apply st_trans.extC
      simp
    · exact qCRqsIP
  have hmem : ("LocalDNS", (LocalDNS, [mCRqsIP])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem

theorem t23 : net_trans S2 (net_label.τ_comm "LocalDNS" "RootDNS" "RqsRoot" "unit") S3 := by
  have h_send : sq_trans (DnsL1, ([] : Queue))
      (sq_action.send "RootDNS" "RqsRoot" "unit") (DnsL2, []) := by
    apply sq_trans.send
    unfold DnsL1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (RootDNS, ([] : Queue))
      (sq_action.recv "LocalDNS" "RqsRoot" "unit") (RootDNS, [mLRqsRoot]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (DnsL1, ([] : Queue))) ∈ S2 := by simp [S2]
  have hmem_q : ("RootDNS", (RootDNS, ([] : Queue))) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t34 : net_trans S3 (net_label.τ_dequeue "RootDNS" "LocalDNS" "RqsRoot" "unit") S4 := by
  have hSQ : sq_trans (RootDNS, [mLRqsRoot])
      (sq_action.dequeue "LocalDNS" "RqsRoot" "unit") (DnsR1, []) := by
    apply sq_trans.dequeue
    · have hEq : RootDNS =
          SessionType.externalChoice "LocalDNS" [("RqsRoot", "unit", DnsR1)] := rfl
      rw [hEq]
      apply st_trans.extC
      simp
    · exact qLRqsRoot
  have hmem : ("RootDNS", (RootDNS, [mLRqsRoot])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem

theorem t45 : net_trans S4 (net_label.τ_comm "RootDNS" "LocalDNS" "RspRoot" "unit") S5 := by
  have h_send : sq_trans (DnsR1, ([] : Queue))
      (sq_action.send "LocalDNS" "RspRoot" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold DnsR1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (DnsL2, ([] : Queue))
      (sq_action.recv "RootDNS" "RspRoot" "unit") (DnsL2, [mRRspRoot]) :=
    sq_trans.recv
  have hmem_p : ("RootDNS", (DnsR1, ([] : Queue))) ∈ S4 := by simp [S4]
  have hmem_q : ("LocalDNS", (DnsL2, ([] : Queue))) ∈ S4 := by simp [S4]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t56 : net_trans S5 (net_label.τ_dequeue "LocalDNS" "RootDNS" "RspRoot" "unit") S6 := by
  have hSQ : sq_trans (DnsL2, [mRRspRoot])
      (sq_action.dequeue "RootDNS" "RspRoot" "unit") (DnsL3, []) := by
    apply sq_trans.dequeue
    · unfold DnsL2
      apply st_trans.extC
      simp
    · exact qRRspRoot
  have hmem : ("LocalDNS", (DnsL2, [mRRspRoot])) ∈ S5 := by simp [S5]
  exact net_trans.dequeue hSQ hmem

theorem t67 : net_trans S6 (net_label.τ_comm "LocalDNS" "TLDDNS" "RqsTLD" "unit") S7 := by
  have h_send : sq_trans (DnsL3, ([] : Queue))
      (sq_action.send "TLDDNS" "RqsTLD" "unit") (DnsL4, []) := by
    apply sq_trans.send
    unfold DnsL3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (TLDDNS, ([] : Queue))
      (sq_action.recv "LocalDNS" "RqsTLD" "unit") (TLDDNS, [mLRqsTLD]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (DnsL3, ([] : Queue))) ∈ S6 := by simp [S6]
  have hmem_q : ("TLDDNS", (TLDDNS, ([] : Queue))) ∈ S6 := by simp [S6]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t78 : net_trans S7 (net_label.τ_dequeue "TLDDNS" "LocalDNS" "RqsTLD" "unit") S8 := by
  have hSQ : sq_trans (TLDDNS, [mLRqsTLD])
      (sq_action.dequeue "LocalDNS" "RqsTLD" "unit") (DnsT1, []) := by
    apply sq_trans.dequeue
    · have hEq : TLDDNS =
          SessionType.externalChoice "LocalDNS" [("RqsTLD", "unit", DnsT1)] := rfl
      rw [hEq]
      apply st_trans.extC
      simp
    · exact qLRqsTLD
  have hmem : ("TLDDNS", (TLDDNS, [mLRqsTLD])) ∈ S7 := by simp [S7]
  exact net_trans.dequeue hSQ hmem

theorem t89 : net_trans S8 (net_label.τ_comm "TLDDNS" "LocalDNS" "RspTLD" "unit") S9 := by
  have h_send : sq_trans (DnsT1, ([] : Queue))
      (sq_action.send "LocalDNS" "RspTLD" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold DnsT1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (DnsL4, ([] : Queue))
      (sq_action.recv "TLDDNS" "RspTLD" "unit") (DnsL4, [mTRspTLD]) :=
    sq_trans.recv
  have hmem_p : ("TLDDNS", (DnsT1, ([] : Queue))) ∈ S8 := by simp [S8]
  have hmem_q : ("LocalDNS", (DnsL4, ([] : Queue))) ∈ S8 := by simp [S8]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t910 : net_trans S9 (net_label.τ_dequeue "LocalDNS" "TLDDNS" "RspTLD" "unit") S10 := by
  have hSQ : sq_trans (DnsL4, [mTRspTLD])
      (sq_action.dequeue "TLDDNS" "RspTLD" "unit") (DnsL5, []) := by
    apply sq_trans.dequeue
    · unfold DnsL4
      apply st_trans.extC
      simp
    · exact qTRspTLD
  have hmem : ("LocalDNS", (DnsL4, [mTRspTLD])) ∈ S9 := by simp [S9]
  exact net_trans.dequeue hSQ hmem

theorem t1011 : net_trans S10 (net_label.τ_comm "LocalDNS" "AuthDNS" "RqsAuth" "unit") S11 := by
  have h_send : sq_trans (DnsL5, ([] : Queue))
      (sq_action.send "AuthDNS" "RqsAuth" "unit") (DnsL6, []) := by
    apply sq_trans.send
    unfold DnsL5
    apply st_trans.intC
    simp
  have h_recv : sq_trans (AuthDNS, ([] : Queue))
      (sq_action.recv "LocalDNS" "RqsAuth" "unit") (AuthDNS, [mLRqsAuth]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (DnsL5, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("AuthDNS", (AuthDNS, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t1112 : net_trans S11 (net_label.τ_dequeue "AuthDNS" "LocalDNS" "RqsAuth" "unit") S12 := by
  have hSQ : sq_trans (AuthDNS, [mLRqsAuth])
      (sq_action.dequeue "LocalDNS" "RqsAuth" "unit") (DnsA1, []) := by
    apply sq_trans.dequeue
    · have hEq : AuthDNS =
          SessionType.externalChoice "LocalDNS" [("RqsAuth", "unit", DnsA1)] := rfl
      rw [hEq]
      apply st_trans.extC
      simp
    · exact qLRqsAuth
  have hmem : ("AuthDNS", (AuthDNS, [mLRqsAuth])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem

theorem t1213 : net_trans S12 (net_label.τ_comm "AuthDNS" "LocalDNS" "RspAuth" "unit") S13 := by
  have h_send : sq_trans (DnsA1, ([] : Queue))
      (sq_action.send "LocalDNS" "RspAuth" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold DnsA1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (DnsL6, ([] : Queue))
      (sq_action.recv "AuthDNS" "RspAuth" "unit") (DnsL6, [mARspAuth]) :=
    sq_trans.recv
  have hmem_p : ("AuthDNS", (DnsA1, ([] : Queue))) ∈ S12 := by simp [S12]
  have hmem_q : ("LocalDNS", (DnsL6, ([] : Queue))) ∈ S12 := by simp [S12]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t1314 : net_trans S13 (net_label.τ_dequeue "LocalDNS" "AuthDNS" "RspAuth" "unit") S14 := by
  have hSQ : sq_trans (DnsL6, [mARspAuth])
      (sq_action.dequeue "AuthDNS" "RspAuth" "unit") (DnsL7, []) := by
    apply sq_trans.dequeue
    · unfold DnsL6
      apply st_trans.extC
      simp
    · exact qARspAuth
  have hmem : ("LocalDNS", (DnsL6, [mARspAuth])) ∈ S13 := by simp [S13]
  exact net_trans.dequeue hSQ hmem

theorem t1415 : net_trans S14 (net_label.τ_comm "LocalDNS" "Client" "RspIP" "unit") S15 := by
  have h_send : sq_trans (DnsL7, ([] : Queue))
      (sq_action.send "Client" "RspIP" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold DnsL7
    apply st_trans.intC
    simp
  have h_recv : sq_trans (DnsC1, ([] : Queue))
      (sq_action.recv "LocalDNS" "RspIP" "unit") (DnsC1, [mLRspIP]) :=
    sq_trans.recv
  have hmem_p : ("LocalDNS", (DnsL7, ([] : Queue))) ∈ S14 := by simp [S14]
  have hmem_q : ("Client", (DnsC1, ([] : Queue))) ∈ S14 := by simp [S14]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t1516 : net_trans S15 (net_label.τ_dequeue "Client" "LocalDNS" "RspIP" "unit") S16 := by
  have hSQ : sq_trans (DnsC1, [mLRspIP])
      (sq_action.dequeue "LocalDNS" "RspIP" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold DnsC1
      apply st_trans.extC
      simp
    · exact qLRspIP
  have hmem : ("Client", (DnsC1, [mLRspIP])) ∈ S15 := by simp [S15]
  exact net_trans.dequeue hSQ hmem

-- ============ Half-duplex ============
/-- `Net` is half-duplex: opposite queues never both fill. -/
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := dnsReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (first
        | exact absurd hCp noContainsNil
        | exact noContainsNil hCq
        | (obtain ⟨lab, S, hmem⟩ := hCq
           have hmem' := hmem.to_mem
           simp at hmem'))
  · obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil

-- ============ Output-liveness: infinite fair paths ============
/-- Every infinite fair path from `Net` drains its queues. -/
theorem dnsOL_inf : IsOutputLiveInfinitePathNetwork Net := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  have hStar : net_trans_star Net (path.seq i) := path_star_reachable h0 i
  have hR := dnsReach _ hStar
  rcases hR with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mCRqsIP] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "Client" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RqsIP" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "Client" "RqsIP" "unit"
        ⟨S2, by rw [h]; exact t12⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLRqsRoot] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RqsRoot" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "RootDNS" "LocalDNS" "RqsRoot" "unit"
        ⟨S4, by rw [h]; exact t34⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mRRspRoot] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "RootDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RspRoot" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "RootDNS" "RspRoot" "unit"
        ⟨S6, by rw [h]; exact t56⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLRqsTLD] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RqsTLD" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "TLDDNS" "LocalDNS" "RqsTLD" "unit"
        ⟨S8, by rw [h]; exact t78⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mTRspTLD] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "TLDDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RspTLD" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "TLDDNS" "RspTLD" "unit"
        ⟨S10, by rw [h]; exact t910⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLRqsAuth] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RqsAuth" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "AuthDNS" "LocalDNS" "RqsAuth" "unit"
        ⟨S12, by rw [h]; exact t1112⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mARspAuth] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "AuthDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RspAuth" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "LocalDNS" "AuthDNS" "RspAuth" "unit"
        ⟨S14, by rw [h]; exact t1314⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLRspIP] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "LocalDNS" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RspIP" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "Client" "LocalDNS" "RspIP" "unit"
        ⟨S16, by rw [h]; exact t1516⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)

-- ============ Output-liveness: stuck states have no orphans ============
/-- Every reachable stuck network from `Net` has no orphans. -/
theorem dnsOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := dnsReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1213⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1314⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1415⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1516⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

/-- `Net` is output-live: fair paths drain queues, stuck states are clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨dnsOL_inf, dnsOL_stuck⟩

end Dns
