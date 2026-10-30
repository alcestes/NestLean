import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun
import Nest.NoRec.NoRecToolkit

namespace Bookreview

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/01_bookreview.scala`
   (Scala package `bookreview`; file `01_bookreview.scala` maps to this
   module since Lean module names may not start with a digit).
   Translated below are the five `lst_*` local session types
   (`lst_BookClient`, `lst_BookInfo`, `lst_BookReview`, `lst_BookDetails`,
   `lst_BookRatings`). Switch setup, IP rules, port checks and monitor
   wiring from `setup` are not session types and are not translated.
   Translation conventions: `IntChoice(Map((agent, label) -> cont))`
   becomes an `internalChoice` branch `(agent, label, sort, cont)`;
   `ExtChoice(agent, Map(label -> cont, ...))` becomes
   `externalChoice agent [(label, sort, cont), ...]`; `Rec`/`Var`/`End`
   become `tRec`/`tVar`/`tEnd`. Agents become roles, labels stay labels.
   The Scala types carry no payload sorts, so every branch uses the
   placeholder sort `"unit"`. -/

/-- `lst_BookClient`. -/
def BookClient : SessionType :=
  SessionType.internalChoice
    [("Info", "Request", "unit",
      SessionType.externalChoice "Info"
        [("Response", "unit", SessionType.tEnd)])]

/-- `lst_BookInfo`. -/
def BookInfo : SessionType :=
  SessionType.externalChoice "Client"
    [("Request", "unit",
      SessionType.internalChoice
        [("Review", "RqsReview", "unit",
          SessionType.internalChoice
            [("Details", "RqsDetail", "unit",
              SessionType.externalChoice "Review"
                [("RspReview", "unit",
                  SessionType.externalChoice "Details"
                    [("RspDetail", "unit",
                      SessionType.internalChoice
                        [("Client", "Response", "unit",
                          SessionType.tEnd)])])])])])]

/-- `lst_BookReview`. -/
def BookReview : SessionType :=
  SessionType.externalChoice "Info"
    [("RqsReview", "unit",
      SessionType.internalChoice
        [("Ratings", "RqsRatings", "unit",
          SessionType.externalChoice "Ratings"
            [("RspRatings", "unit",
              SessionType.internalChoice
                [("Info", "RspReview", "unit", SessionType.tEnd)])])])]

/-- `lst_BookDetails`. -/
def BookDetails : SessionType :=
  SessionType.externalChoice "Info"
    [("RqsDetail", "unit",
      SessionType.internalChoice
        [("Info", "RspDetail", "unit", SessionType.tEnd)])]

/-- `lst_BookRatings`. -/
def BookRatings : SessionType :=
  SessionType.externalChoice "Review"
    [("RqsRatings", "unit",
      SessionType.internalChoice
        [("Review", "RspRatings", "unit", SessionType.tEnd)])]

-- All five types are recursion-free: certified by the generic `NoRec` lemmas.
/-- `BookClient` is recursion-free (boolean check). -/
theorem BookClient_norec : BookClient.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `BookClient` (empty seen set, via recursion-freedom). -/
theorem BookClient_deep : Prunable [] BookClient :=
  norec_deep BookClient_norec []
/-- Monitorability of `BookClient` (finite prune closure, via recursion-freedom). -/
theorem BookClient_mon : Drainability.Monitorable BookClient :=
  norec_monitorable BookClient_norec

/-- `BookInfo` is recursion-free (boolean check). -/
theorem BookInfo_norec : BookInfo.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `BookInfo` (empty seen set, via recursion-freedom). -/
theorem BookInfo_deep : Prunable [] BookInfo :=
  norec_deep BookInfo_norec []
/-- Monitorability of `BookInfo` (finite prune closure, via recursion-freedom). -/
theorem BookInfo_mon : Drainability.Monitorable BookInfo :=
  norec_monitorable BookInfo_norec

/-- `BookReview` is recursion-free (boolean check). -/
theorem BookReview_norec : BookReview.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `BookReview` (empty seen set, via recursion-freedom). -/
theorem BookReview_deep : Prunable [] BookReview :=
  norec_deep BookReview_norec []
/-- Monitorability of `BookReview` (finite prune closure, via recursion-freedom). -/
theorem BookReview_mon : Drainability.Monitorable BookReview :=
  norec_monitorable BookReview_norec

/-- `BookDetails` is recursion-free (boolean check). -/
theorem BookDetails_norec : BookDetails.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `BookDetails` (empty seen set, via recursion-freedom). -/
theorem BookDetails_deep : Prunable [] BookDetails :=
  norec_deep BookDetails_norec []
/-- Monitorability of `BookDetails` (finite prune closure, via recursion-freedom). -/
theorem BookDetails_mon : Drainability.Monitorable BookDetails :=
  norec_monitorable BookDetails_norec

/-- `BookRatings` is recursion-free (boolean check). -/
theorem BookRatings_norec : BookRatings.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `BookRatings` (empty seen set, via recursion-freedom). -/
theorem BookRatings_deep : Prunable [] BookRatings :=
  norec_deep BookRatings_norec []
/-- Monitorability of `BookRatings` (finite prune closure, via recursion-freedom). -/
theorem BookRatings_mon : Drainability.Monitorable BookRatings :=
  norec_monitorable BookRatings_norec

/-- Empty-queue network for the five bookreview roles. -/
def Net : Network :=
  [("Client", (BookClient, [])),
   ("Info", (BookInfo, [])),
   ("Review", (BookReview, [])),
   ("Details", (BookDetails, [])),
   ("Ratings", (BookRatings, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact BookClient.wfCheck_sound (by decide)
  · exact BookInfo.wfCheck_sound (by decide)
  · exact BookReview.wfCheck_sound (by decide)
  · exact BookDetails.wfCheck_sound (by decide)
  · exact BookRatings.wfCheck_sound (by decide)

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
  · simp only [BookClient, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(BookInfo, []), by decide⟩
  · simp only [BookInfo, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(BookClient, []), by decide⟩
    · exact ⟨(BookReview, []), by decide⟩
    · exact ⟨(BookDetails, []), by decide⟩
    · exact ⟨(BookReview, []), by decide⟩
    · exact ⟨(BookDetails, []), by decide⟩
    · exact ⟨(BookClient, []), by decide⟩
  · simp only [BookReview, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | rfl | rfl
    · exact ⟨(BookInfo, []), by decide⟩
    · exact ⟨(BookRatings, []), by decide⟩
    · exact ⟨(BookRatings, []), by decide⟩
    · exact ⟨(BookInfo, []), by decide⟩
  · simp only [BookDetails, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(BookInfo, []), by decide⟩
  · simp only [BookRatings, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl <;> exact ⟨(BookReview, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)


-- ============ Messages ============
abbrev mReq : QueueMessage := QueueMessage.msg "Client" "Request" "unit"
abbrev mRqsReview : QueueMessage := QueueMessage.msg "Info" "RqsReview" "unit"
abbrev mRqsDetail : QueueMessage := QueueMessage.msg "Info" "RqsDetail" "unit"
abbrev mRqsRatings : QueueMessage := QueueMessage.msg "Review" "RqsRatings" "unit"
abbrev mRspRatings : QueueMessage := QueueMessage.msg "Ratings" "RspRatings" "unit"
abbrev mRspReview : QueueMessage := QueueMessage.msg "Review" "RspReview" "unit"
abbrev mRspDetail : QueueMessage := QueueMessage.msg "Details" "RspDetail" "unit"
abbrev mResp : QueueMessage := QueueMessage.msg "Info" "Response" "unit"

-- ============ Continuations ============
def BC1 : SessionType := SessionType.externalChoice "Info" [("Response", "unit", SessionType.tEnd)]
def BI5 : SessionType := SessionType.internalChoice [("Client", "Response", "unit", SessionType.tEnd)]
def BI4 : SessionType := SessionType.externalChoice "Details" [("RspDetail", "unit", BI5)]
def BI3 : SessionType := SessionType.externalChoice "Review" [("RspReview", "unit", BI4)]
def BI2 : SessionType := SessionType.internalChoice [("Details", "RqsDetail", "unit", BI3)]
def BI1 : SessionType := SessionType.internalChoice [("Review", "RqsReview", "unit", BI2)]
def BR3 : SessionType := SessionType.internalChoice [("Info", "RspReview", "unit", SessionType.tEnd)]
def BR2 : SessionType := SessionType.externalChoice "Ratings" [("RspRatings", "unit", BR3)]
def BR1 : SessionType := SessionType.internalChoice [("Ratings", "RqsRatings", "unit", BR2)]
def BD1 : SessionType := SessionType.internalChoice [("Info", "RspDetail", "unit", SessionType.tEnd)]
def BRa1 : SessionType := SessionType.internalChoice [("Review", "RspRatings", "unit", SessionType.tEnd)]

-- ============ OUT/INP characterizations ============
theorem BookClient_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BookClient (st_label.out p lab S) T' →
    p = "Info" ∧ lab = "Request" ∧ S = "unit" ∧ T' = BC1 := by
  intro h
  unfold BookClient at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BookClient_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BookClient (st_label.inp p lab S) T') : False := by
  unfold BookClient at h
  cases h

theorem BC1_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BC1 (st_label.out p lab S) T') : False := by
  unfold BC1 at h
  cases h

theorem BC1_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BC1 (st_label.inp p lab S) T' →
    p = "Info" ∧ lab = "Response" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold BC1 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BookInfo_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BookInfo (st_label.out p lab S) T') : False := by
  unfold BookInfo at h
  cases h

theorem BookInfo_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BookInfo (st_label.inp p lab S) T' →
    p = "Client" ∧ lab = "Request" ∧ S = "unit" ∧ T' = BI1 := by
  intro h
  unfold BookInfo at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BI1 (st_label.out p lab S) T' →
    p = "Review" ∧ lab = "RqsReview" ∧ S = "unit" ∧ T' = BI2 := by
  intro h
  unfold BI1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BI1 (st_label.inp p lab S) T') : False := by
  unfold BI1 at h
  cases h

theorem BI2_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BI2 (st_label.out p lab S) T' →
    p = "Details" ∧ lab = "RqsDetail" ∧ S = "unit" ∧ T' = BI3 := by
  intro h
  unfold BI2 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI2_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BI2 (st_label.inp p lab S) T') : False := by
  unfold BI2 at h
  cases h

theorem BI3_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BI3 (st_label.out p lab S) T') : False := by
  unfold BI3 at h
  cases h

theorem BI3_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BI3 (st_label.inp p lab S) T' →
    p = "Review" ∧ lab = "RspReview" ∧ S = "unit" ∧ T' = BI4 := by
  intro h
  unfold BI3 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI4_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BI4 (st_label.out p lab S) T') : False := by
  unfold BI4 at h
  cases h

theorem BI4_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BI4 (st_label.inp p lab S) T' →
    p = "Details" ∧ lab = "RspDetail" ∧ S = "unit" ∧ T' = BI5 := by
  intro h
  unfold BI4 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI5_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BI5 (st_label.out p lab S) T' →
    p = "Client" ∧ lab = "Response" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold BI5 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BI5_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BI5 (st_label.inp p lab S) T') : False := by
  unfold BI5 at h
  cases h

theorem BookReview_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BookReview (st_label.out p lab S) T') : False := by
  unfold BookReview at h
  cases h

theorem BookReview_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BookReview (st_label.inp p lab S) T' →
    p = "Info" ∧ lab = "RqsReview" ∧ S = "unit" ∧ T' = BR1 := by
  intro h
  unfold BookReview at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BR1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BR1 (st_label.out p lab S) T' →
    p = "Ratings" ∧ lab = "RqsRatings" ∧ S = "unit" ∧ T' = BR2 := by
  intro h
  unfold BR1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BR1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BR1 (st_label.inp p lab S) T') : False := by
  unfold BR1 at h
  cases h

theorem BR2_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BR2 (st_label.out p lab S) T') : False := by
  unfold BR2 at h
  cases h

theorem BR2_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BR2 (st_label.inp p lab S) T' →
    p = "Ratings" ∧ lab = "RspRatings" ∧ S = "unit" ∧ T' = BR3 := by
  intro h
  unfold BR2 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BR3_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BR3 (st_label.out p lab S) T' →
    p = "Info" ∧ lab = "RspReview" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold BR3 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BR3_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BR3 (st_label.inp p lab S) T') : False := by
  unfold BR3 at h
  cases h

theorem BookDetails_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BookDetails (st_label.out p lab S) T') : False := by
  unfold BookDetails at h
  cases h

theorem BookDetails_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BookDetails (st_label.inp p lab S) T' →
    p = "Info" ∧ lab = "RqsDetail" ∧ S = "unit" ∧ T' = BD1 := by
  intro h
  unfold BookDetails at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BD1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BD1 (st_label.out p lab S) T' →
    p = "Info" ∧ lab = "RspDetail" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold BD1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BD1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BD1 (st_label.inp p lab S) T') : False := by
  unfold BD1 at h
  cases h

theorem BookRatings_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BookRatings (st_label.out p lab S) T') : False := by
  unfold BookRatings at h
  cases h

theorem BookRatings_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BookRatings (st_label.inp p lab S) T' →
    p = "Review" ∧ lab = "RqsRatings" ∧ S = "unit" ∧ T' = BRa1 := by
  intro h
  unfold BookRatings at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BRa1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans BRa1 (st_label.out p lab S) T' →
    p = "Review" ∧ lab = "RspRatings" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold BRa1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem BRa1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans BRa1 (st_label.inp p lab S) T') : False := by
  unfold BRa1 at h
  cases h

theorem tEnd_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

theorem tEnd_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h

-- states 86
def S0 : Network := [("Client", (BookClient, [])), ("Info", (BookInfo, [])), ("Review", (BookReview, [])), ("Details", (BookDetails, [])), ("Ratings", (BookRatings, []))]
def S1 : Network := [("Info", (BookInfo, [mReq])), ("Client", (BC1, [])), ("Review", (BookReview, [])), ("Details", (BookDetails, [])), ("Ratings", (BookRatings, []))]
def S2 : Network := [("Info", (BI1, [])), ("Client", (BC1, [])), ("Review", (BookReview, [])), ("Details", (BookDetails, [])), ("Ratings", (BookRatings, []))]
def S3 : Network := [("Review", (BookReview, [mRqsReview])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, [])), ("Ratings", (BookRatings, []))]
def S4 : Network := [("Review", (BR1, [])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, [])), ("Ratings", (BookRatings, []))]
def S5 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Review", (BookReview, [mRqsReview])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S6 : Network := [("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, []))]
def S7 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Review", (BR1, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S8 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Review", (BookReview, [mRqsReview])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S9 : Network := [("Review", (BR1, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S10 : Network := [("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, []))]
def S11 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S12 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Review", (BR1, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S13 : Network := [("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S14 : Network := [("Review", (BR1, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S15 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (BookReview, [mRqsReview])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S16 : Network := [("Details", (BD1, [])), ("Review", (BR1, [])), ("Info", (BI3, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S17 : Network := [("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, []))]
def S18 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S19 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S20 : Network := [("Ratings", (BRa1, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S21 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (BR1, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S22 : Network := [("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S23 : Network := [("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S24 : Network := [("Details", (BD1, [])), ("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S25 : Network := [("Review", (BR1, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, [])), ("Ratings", (BookRatings, []))]
def S26 : Network := [("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI2, [])), ("Client", (BC1, [])), ("Details", (BookDetails, []))]
def S27 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S28 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S29 : Network := [("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S30 : Network := [("Ratings", (BRa1, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S31 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S32 : Network := [("Details", (BD1, [])), ("Ratings", (BRa1, [])), ("Info", (BI3, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S33 : Network := [("Ratings", (BookRatings, [mRqsRatings])), ("Review", (BR2, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S34 : Network := [("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S35 : Network := [("Details", (BD1, [])), ("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S36 : Network := [("Ratings", (BRa1, [])), ("Details", (BD1, [])), ("Review", (BR2, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S37 : Network := [("Info", (BI2, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, [])), ("Details", (BookDetails, []))]
def S38 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S39 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S40 : Network := [("Review", (BR3, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S41 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S42 : Network := [("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S43 : Network := [("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S44 : Network := [("Details", (BD1, [])), ("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S45 : Network := [("Ratings", (BRa1, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (BR2, [])), ("Client", (BC1, []))]
def S46 : Network := [("Ratings", (BRa1, [])), ("Review", (BR2, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S47 : Network := [("Details", (BookDetails, [mRqsDetail])), ("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S48 : Network := [("Details", (BD1, [])), ("Info", (BI3, [])), ("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S49 : Network := [("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S50 : Network := [("Review", (BR3, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S51 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S52 : Network := [("Details", (BD1, [])), ("Review", (BR3, [])), ("Info", (BI3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S53 : Network := [("Review", (BR2, [mRspRatings])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S54 : Network := [("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S55 : Network := [("Details", (BD1, [])), ("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S56 : Network := [("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Client", (BC1, []))]
def S57 : Network := [("Review", (BR3, [])), ("Details", (BD1, [])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI3, [])), ("Client", (BC1, []))]
def S58 : Network := [("Details", (BD1, [])), ("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S59 : Network := [("Info", (BI4, [])), ("Details", (BookDetails, [mRqsDetail])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S60 : Network := [("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S61 : Network := [("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S62 : Network := [("Info", (BI4, [])), ("Review", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S63 : Network := [("Review", (BR3, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S64 : Network := [("Review", (BR3, [])), ("Ratings", (SessionType.tEnd, [])), ("Info", (BI3, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S65 : Network := [("Info", (BI3, [mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Client", (BC1, []))]
def S66 : Network := [("Info", (BI4, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BookDetails, [mRqsDetail])), ("Client", (BC1, []))]
def S67 : Network := [("Info", (BI4, [])), ("Details", (BD1, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S68 : Network := [("Info", (BI3, [mRspReview, mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S69 : Network := [("Details", (BD1, [])), ("Info", (BI4, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S70 : Network := [("Info", (BI3, [mRspDetail, mRspReview])), ("Review", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S71 : Network := [("Info", (BI4, [])), ("Review", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S72 : Network := [("Info", (BI3, [mRspDetail, mRspReview])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S73 : Network := [("Info", (BI4, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (BD1, [])), ("Client", (BC1, []))]
def S74 : Network := [("Info", (BI4, [mRspDetail])), ("Details", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S75 : Network := [("Info", (BI4, [mRspDetail])), ("Review", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S76 : Network := [("Info", (BI4, [mRspDetail])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S77 : Network := [("Info", (BI5, [])), ("Details", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S78 : Network := [("Info", (BI5, [])), ("Review", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S79 : Network := [("Info", (BI5, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Client", (BC1, []))]
def S80 : Network := [("Client", (BC1, [mResp])), ("Info", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, []))]
def S81 : Network := [("Client", (BC1, [mResp])), ("Info", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, []))]
def S82 : Network := [("Client", (BC1, [mResp])), ("Info", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, []))]
def S83 : Network := [("Client", (SessionType.tEnd, [])), ("Info", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, []))]
def S84 : Network := [("Client", (SessionType.tEnd, [])), ("Info", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, []))]
def S85 : Network := [("Client", (SessionType.tEnd, [])), ("Info", (SessionType.tEnd, [])), ("Review", (SessionType.tEnd, [])), ("Ratings", (SessionType.tEnd, [])), ("Details", (SessionType.tEnd, []))]
-- Queue computations
theorem qReq : Queue.dequeue [mReq] mReq = some ([] : Queue) := rfl
theorem qRqsReview : Queue.dequeue [mRqsReview] mRqsReview = some ([] : Queue) := rfl
theorem qRqsDetail : Queue.dequeue [mRqsDetail] mRqsDetail = some ([] : Queue) := rfl
theorem qRqsRatings : Queue.dequeue [mRqsRatings] mRqsRatings = some ([] : Queue) := rfl
theorem qRspRatings : Queue.dequeue [mRspRatings] mRspRatings = some ([] : Queue) := rfl
theorem qRspReview_single : Queue.dequeue [mRspReview] mRspReview = some ([] : Queue) := rfl
theorem qRspDetail_single : Queue.dequeue [mRspDetail] mRspDetail = some ([] : Queue) := rfl
theorem qResp : Queue.dequeue [mResp] mResp = some ([] : Queue) := rfl
theorem qRspDetail_Review_none : Queue.dequeue [mRspDetail] mRspReview = none := rfl
theorem qReviewDetails_Review : Queue.dequeue [mRspReview, mRspDetail] mRspReview = some ([mRspDetail] : Queue) := rfl
theorem qDetailsReview_Review : Queue.dequeue [mRspDetail, mRspReview] mRspReview = some ([mRspDetail] : Queue) := rfl


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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BookClient_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BookClient_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BookClient_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BookClient_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

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
        have hi := BookInfo_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qReq] at hQ
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
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookInfo_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BI1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S3_step : ∀ (δ : net_label) (N' : Network),
    net_trans S3 δ N' → is_internal_net_label δ → N' = S4 ∨ N' = S5 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookReview_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsReview] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S4_step : ∀ (δ : net_label) (N' : Network),
    net_trans S4 δ N' → is_internal_net_label δ → N' = S6 ∨ N' = S7 := by
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S5_step : ∀ (δ : net_label) (N' : Network),
    net_trans S5 δ N' → is_internal_net_label δ → N' = S8 ∨ N' = S9 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookReview_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsReview] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S10 ∨ N' = S11 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inl rfl
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne

theorem S7_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → N' = S12 ∨ N' = S13 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S14 ∨ N' = S15 := by
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
      | dequeue hST hQ =>
        have hi := BookReview_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsReview] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S16 ∨ N' = S13 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S10_step : ∀ (δ : net_label) (N' : Network),
    net_trans S10 δ N' → is_internal_net_label δ → N' = S17 ∨ N' = S18 := by
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne

theorem S11_step : ∀ (δ : net_label) (N' : Network),
    net_trans S11 δ N' → is_internal_net_label δ → N' = S19 ∨ N' = S20 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S12_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → N' = S21 ∨ N' = S22 := by
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S13_step : ∀ (δ : net_label) (N' : Network),
    net_trans S13 δ N' → is_internal_net_label δ → N' = S23 ∨ N' = S24 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S14_step : ∀ (δ : net_label) (N' : Network),
    net_trans S14 δ N' → is_internal_net_label δ → N' = S22 ∨ N' = S21 := by
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
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S15_step : ∀ (δ : net_label) (N' : Network),
    net_trans S15 δ N' → is_internal_net_label δ → N' = S25 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookReview_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsReview] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookReview_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S16_step : ∀ (δ : net_label) (N' : Network),
    net_trans S16 δ N' → is_internal_net_label δ → N' = S21 ∨ N' = S22 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S17_step : ∀ (δ : net_label) (N' : Network),
    net_trans S17 δ N' → is_internal_net_label δ → N' = S26 ∨ N' = S27 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne

theorem S18_step : ∀ (δ : net_label) (N' : Network),
    net_trans S18 δ N' → is_internal_net_label δ → N' = S28 ∨ N' = S29 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S19_step : ∀ (δ : net_label) (N' : Network),
    net_trans S19 δ N' → is_internal_net_label δ → N' = S30 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S20_step : ∀ (δ : net_label) (N' : Network),
    net_trans S20 δ N' → is_internal_net_label δ → N' = S32 ∨ N' = S29 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S21_step : ∀ (δ : net_label) (N' : Network),
    net_trans S21 δ N' → is_internal_net_label δ → N' = S33 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S22_step : ∀ (δ : net_label) (N' : Network),
    net_trans S22 δ N' → is_internal_net_label δ → N' = S34 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S23_step : ∀ (δ : net_label) (N' : Network),
    net_trans S23 δ N' → is_internal_net_label δ → N' = S35 ∨ N' = S29 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S24_step : ∀ (δ : net_label) (N' : Network),
    net_trans S24 δ N' → is_internal_net_label δ → N' = S36 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S25_step : ∀ (δ : net_label) (N' : Network),
    net_trans S25 δ N' → is_internal_net_label δ → N' = S33 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne

theorem S26_step : ∀ (δ : net_label) (N' : Network),
    net_trans S26 δ N' → is_internal_net_label δ → N' = S37 ∨ N' = S38 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne

theorem S27_step : ∀ (δ : net_label) (N' : Network),
    net_trans S27 δ N' → is_internal_net_label δ → N' = S39 ∨ N' = S40 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S28_step : ∀ (δ : net_label) (N' : Network),
    net_trans S28 δ N' → is_internal_net_label δ → N' = S41 ∨ N' = S42 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S29_step : ∀ (δ : net_label) (N' : Network),
    net_trans S29 δ N' → is_internal_net_label δ → N' = S43 ∨ N' = S44 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S30_step : ∀ (δ : net_label) (N' : Network),
    net_trans S30 δ N' → is_internal_net_label δ → N' = S42 ∨ N' = S41 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S31_step : ∀ (δ : net_label) (N' : Network),
    net_trans S31 δ N' → is_internal_net_label δ → N' = S45 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S32_step : ∀ (δ : net_label) (N' : Network),
    net_trans S32 δ N' → is_internal_net_label δ → N' = S41 ∨ N' = S42 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S33_step : ∀ (δ : net_label) (N' : Network),
    net_trans S33 δ N' → is_internal_net_label δ → N' = S46 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookRatings_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsRatings] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookRatings_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S34_step : ∀ (δ : net_label) (N' : Network),
    net_trans S34 δ N' → is_internal_net_label δ → N' = S42 ∨ N' = S41 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S35_step : ∀ (δ : net_label) (N' : Network),
    net_trans S35 δ N' → is_internal_net_label δ → N' = S41 ∨ N' = S42 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S36_step : ∀ (δ : net_label) (N' : Network),
    net_trans S36 δ N' → is_internal_net_label δ → N' = S42 ∨ N' = S41 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S37_step : ∀ (δ : net_label) (N' : Network),
    net_trans S37 δ N' → is_internal_net_label δ → N' = S47 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => BI2_no_inp h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI2_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI2_out_iff hST
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne

theorem S38_step : ∀ (δ : net_label) (N' : Network),
    net_trans S38 δ N' → is_internal_net_label δ → N' = S48 ∨ N' = S49 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S39_step : ∀ (δ : net_label) (N' : Network),
    net_trans S39 δ N' → is_internal_net_label δ → N' = S50 ∨ N' = S51 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S40_step : ∀ (δ : net_label) (N' : Network),
    net_trans S40 δ N' → is_internal_net_label δ → N' = S52 ∨ N' = S49 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S41_step : ∀ (δ : net_label) (N' : Network),
    net_trans S41 δ N' → is_internal_net_label δ → N' = S53 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S42_step : ∀ (δ : net_label) (N' : Network),
    net_trans S42 δ N' → is_internal_net_label δ → N' = S54 ∨ N' = S51 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S43_step : ∀ (δ : net_label) (N' : Network),
    net_trans S43 δ N' → is_internal_net_label δ → N' = S55 ∨ N' = S56 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S44_step : ∀ (δ : net_label) (N' : Network),
    net_trans S44 δ N' → is_internal_net_label δ → N' = S57 ∨ N' = S51 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S45_step : ∀ (δ : net_label) (N' : Network),
    net_trans S45 δ N' → is_internal_net_label δ → N' = S53 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S46_step : ∀ (δ : net_label) (N' : Network),
    net_trans S46 δ N' → is_internal_net_label δ → N' = S53 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BRa1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BRa1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S47_step : ∀ (δ : net_label) (N' : Network),
    net_trans S47 δ N' → is_internal_net_label δ → N' = S58 ∨ N' = S59 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S48_step : ∀ (δ : net_label) (N' : Network),
    net_trans S48 δ N' → is_internal_net_label δ → N' = S60 ∨ N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S49_step : ∀ (δ : net_label) (N' : Network),
    net_trans S49 δ N' → is_internal_net_label δ → N' = S62 ∨ N' = S58 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S50_step : ∀ (δ : net_label) (N' : Network),
    net_trans S50 δ N' → is_internal_net_label δ → N' = S61 ∨ N' = S60 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S51_step : ∀ (δ : net_label) (N' : Network),
    net_trans S51 δ N' → is_internal_net_label δ → N' = S63 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S52_step : ∀ (δ : net_label) (N' : Network),
    net_trans S52 δ N' → is_internal_net_label δ → N' = S60 ∨ N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S53_step : ∀ (δ : net_label) (N' : Network),
    net_trans S53 δ N' → is_internal_net_label δ → N' = S64 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BR2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspRatings] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BR2_no_out h)
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
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S54_step : ∀ (δ : net_label) (N' : Network),
    net_trans S54 δ N' → is_internal_net_label δ → N' = S65 ∨ N' = S60 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S55_step : ∀ (δ : net_label) (N' : Network),
    net_trans S55 δ N' → is_internal_net_label δ → N' = S60 ∨ N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S56_step : ∀ (δ : net_label) (N' : Network),
    net_trans S56 δ N' → is_internal_net_label δ → N' = S66 ∨ N' = S58 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        exact Or.inr rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S57_step : ∀ (δ : net_label) (N' : Network),
    net_trans S57 δ N' → is_internal_net_label δ → N' = S61 ∨ N' = S60 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S58_step : ∀ (δ : net_label) (N' : Network),
    net_trans S58 δ N' → is_internal_net_label δ → N' = S67 ∨ N' = S68 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S59_step : ∀ (δ : net_label) (N' : Network),
    net_trans S59 δ N' → is_internal_net_label δ → N' = S69 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S60_step : ∀ (δ : net_label) (N' : Network),
    net_trans S60 δ N' → is_internal_net_label δ → N' = S70 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S61_step : ∀ (δ : net_label) (N' : Network),
    net_trans S61 δ N' → is_internal_net_label δ → N' = S71 ∨ N' = S68 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S62_step : ∀ (δ : net_label) (N' : Network),
    net_trans S62 δ N' → is_internal_net_label δ → N' = S69 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S63_step : ∀ (δ : net_label) (N' : Network),
    net_trans S63 δ N' → is_internal_net_label δ → N' = S70 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S64_step : ∀ (δ : net_label) (N' : Network),
    net_trans S64 δ N' → is_internal_net_label δ → N' = S72 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_Review_none] at hQ
        cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BR3_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BR3_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S65_step : ∀ (δ : net_label) (N' : Network),
    net_trans S65 δ N' → is_internal_net_label δ → N' = S73 ∨ N' = S68 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspReview_single] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact Or.inr rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S66_step : ∀ (δ : net_label) (N' : Network),
    net_trans S66 δ N' → is_internal_net_label δ → N' = S69 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BookDetails_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRqsDetail] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BookDetails_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S67_step : ∀ (δ : net_label) (N' : Network),
    net_trans S67 δ N' → is_internal_net_label δ → N' = S74 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S68_step : ∀ (δ : net_label) (N' : Network),
    net_trans S68 δ N' → is_internal_net_label δ → N' = S74 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qReviewDetails_Review] at hQ
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
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S69_step : ∀ (δ : net_label) (N' : Network),
    net_trans S69 δ N' → is_internal_net_label δ → N' = S74 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S70_step : ∀ (δ : net_label) (N' : Network),
    net_trans S70 δ N' → is_internal_net_label δ → N' = S75 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qDetailsReview_Review] at hQ
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
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S71_step : ∀ (δ : net_label) (N' : Network),
    net_trans S71 δ N' → is_internal_net_label δ → N' = S74 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
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
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S72_step : ∀ (δ : net_label) (N' : Network),
    net_trans S72 δ N' → is_internal_net_label δ → N' = S76 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qDetailsReview_Review] at hQ
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
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI3_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S73_step : ∀ (δ : net_label) (N' : Network),
    net_trans S73 δ N' → is_internal_net_label δ → N' = S74 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BD1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BD1_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S74_step : ∀ (δ : net_label) (N' : Network),
    net_trans S74 δ N' → is_internal_net_label δ → N' = S77 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI4_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_single] at hQ
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
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S75_step : ∀ (δ : net_label) (N' : Network),
    net_trans S75 δ N' → is_internal_net_label δ → N' = S78 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI4_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_single] at hQ
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
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S76_step : ∀ (δ : net_label) (N' : Network),
    net_trans S76 δ N' → is_internal_net_label δ → N' = S79 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BI4_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRspDetail_single] at hQ
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
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BI4_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S77_step : ∀ (δ : net_label) (N' : Network),
    net_trans S77 δ N' → is_internal_net_label δ → N' = S80 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI5_out_iff hST
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S78_step : ∀ (δ : net_label) (N' : Network),
    net_trans S78 δ N' → is_internal_net_label δ → N' = S81 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI5_out_iff hST
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S79_step : ∀ (δ : net_label) (N' : Network),
    net_trans S79 δ N' → is_internal_net_label δ → N' = S82 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => have ho := BI5_out_iff hST; exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := BI5_out_iff hST
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · exact absurd rfl hne

theorem S80_step : ∀ (δ : net_label) (N' : Network),
    net_trans S80 δ N' → is_internal_net_label δ → N' = S83 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BC1_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qResp] at hQ
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
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S81_step : ∀ (δ : net_label) (N' : Network),
    net_trans S81 δ N' → is_internal_net_label δ → N' = S84 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BC1_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qResp] at hQ
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
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S82_step : ∀ (δ : net_label) (N' : Network),
    net_trans S82 δ N' → is_internal_net_label δ → N' = S85 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := BC1_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qResp] at hQ
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
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => BC1_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S83_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S83 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S84_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S84 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S85_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S85 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hmem
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
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
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
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne



theorem brReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S4 ∨ N1 = S5 ∨ N1 = S6 ∨ N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S10 ∨ N1 = S11 ∨ N1 = S12 ∨ N1 = S13 ∨ N1 = S14 ∨ N1 = S15 ∨ N1 = S16 ∨ N1 = S17 ∨ N1 = S18 ∨ N1 = S19 ∨ N1 = S20 ∨ N1 = S21 ∨ N1 = S22 ∨ N1 = S23 ∨ N1 = S24 ∨ N1 = S25 ∨ N1 = S26 ∨ N1 = S27 ∨ N1 = S28 ∨ N1 = S29 ∨ N1 = S30 ∨ N1 = S31 ∨ N1 = S32 ∨ N1 = S33 ∨ N1 = S34 ∨ N1 = S35 ∨ N1 = S36 ∨ N1 = S37 ∨ N1 = S38 ∨ N1 = S39 ∨ N1 = S40 ∨ N1 = S41 ∨ N1 = S42 ∨ N1 = S43 ∨ N1 = S44 ∨ N1 = S45 ∨ N1 = S46 ∨ N1 = S47 ∨ N1 = S48 ∨ N1 = S49 ∨ N1 = S50 ∨ N1 = S51 ∨ N1 = S52 ∨ N1 = S53 ∨ N1 = S54 ∨ N1 = S55 ∨ N1 = S56 ∨ N1 = S57 ∨ N1 = S58 ∨ N1 = S59 ∨ N1 = S60 ∨ N1 = S61 ∨ N1 = S62 ∨ N1 = S63 ∨ N1 = S64 ∨ N1 = S65 ∨ N1 = S66 ∨ N1 = S67 ∨ N1 = S68 ∨ N1 = S69 ∨ N1 = S70 ∨ N1 = S71 ∨ N1 = S72 ∨ N1 = S73 ∨ N1 = S74 ∨ N1 = S75 ∨ N1 = S76 ∨ N1 = S77 ∨ N1 = S78 ∨ N1 = S79 ∨ N1 = S80 ∨ N1 = S81 ∨ N1 = S82 ∨ N1 = S83 ∨ N1 = S84 ∨ N1 = S85) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S4 ∨ N2 = S5 ∨ N2 = S6 ∨ N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S10 ∨ N2 = S11 ∨ N2 = S12 ∨ N2 = S13 ∨ N2 = S14 ∨ N2 = S15 ∨ N2 = S16 ∨ N2 = S17 ∨ N2 = S18 ∨ N2 = S19 ∨ N2 = S20 ∨ N2 = S21 ∨ N2 = S22 ∨ N2 = S23 ∨ N2 = S24 ∨ N2 = S25 ∨ N2 = S26 ∨ N2 = S27 ∨ N2 = S28 ∨ N2 = S29 ∨ N2 = S30 ∨ N2 = S31 ∨ N2 = S32 ∨ N2 = S33 ∨ N2 = S34 ∨ N2 = S35 ∨ N2 = S36 ∨ N2 = S37 ∨ N2 = S38 ∨ N2 = S39 ∨ N2 = S40 ∨ N2 = S41 ∨ N2 = S42 ∨ N2 = S43 ∨ N2 = S44 ∨ N2 = S45 ∨ N2 = S46 ∨ N2 = S47 ∨ N2 = S48 ∨ N2 = S49 ∨ N2 = S50 ∨ N2 = S51 ∨ N2 = S52 ∨ N2 = S53 ∨ N2 = S54 ∨ N2 = S55 ∨ N2 = S56 ∨ N2 = S57 ∨ N2 = S58 ∨ N2 = S59 ∨ N2 = S60 ∨ N2 = S61 ∨ N2 = S62 ∨ N2 = S63 ∨ N2 = S64 ∨ N2 = S65 ∨ N2 = S66 ∨ N2 = S67 ∨ N2 = S68 ∨ N2 = S69 ∨ N2 = S70 ∨ N2 = S71 ∨ N2 = S72 ∨ N2 = S73 ∨ N2 = S74 ∨ N2 = S75 ∨ N2 = S76 ∨ N2 = S77 ∨ N2 = S78 ∨ N2 = S79 ∨ N2 = S80 ∨ N2 = S81 ∨ N2 = S82 ∨ N2 = S83 ∨ N2 = S84 ∨ N2 = S85) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S4_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S5_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S6_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S7_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S8_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S9_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S10_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S11_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S12_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S13_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S14_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S15_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S16_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S17_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S18_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S19_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S20_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S21_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S22_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S23_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S24_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S25_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S26_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S27_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S28_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S29_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S30_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S31_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S32_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S33_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S34_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S35_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S36_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S37_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S38_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S39_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S40_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S41_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S42_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S43_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S44_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S45_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S46_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S47_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S48_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S49_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S50_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S51_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S52_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S53_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S54_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S55_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S56_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S57_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S58_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S59_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S60_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S61_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S62_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S63_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S64_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S65_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S66_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S67_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S68_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S69_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S70_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S71_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S72_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S73_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S74_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S75_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S76_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S77_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S78_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S79_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S80_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S81_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S82_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · exact absurd (S83_no_step _ _ hTr hInt) id
    · exact absurd (S84_no_step _ _ hTr hInt) id
    · exact absurd (S85_no_step _ _ hTr hInt) id

theorem brReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S4 ∨ N' = S5 ∨ N' = S6 ∨ N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S10 ∨ N' = S11 ∨ N' = S12 ∨ N' = S13 ∨ N' = S14 ∨ N' = S15 ∨ N' = S16 ∨ N' = S17 ∨ N' = S18 ∨ N' = S19 ∨ N' = S20 ∨ N' = S21 ∨ N' = S22 ∨ N' = S23 ∨ N' = S24 ∨ N' = S25 ∨ N' = S26 ∨ N' = S27 ∨ N' = S28 ∨ N' = S29 ∨ N' = S30 ∨ N' = S31 ∨ N' = S32 ∨ N' = S33 ∨ N' = S34 ∨ N' = S35 ∨ N' = S36 ∨ N' = S37 ∨ N' = S38 ∨ N' = S39 ∨ N' = S40 ∨ N' = S41 ∨ N' = S42 ∨ N' = S43 ∨ N' = S44 ∨ N' = S45 ∨ N' = S46 ∨ N' = S47 ∨ N' = S48 ∨ N' = S49 ∨ N' = S50 ∨ N' = S51 ∨ N' = S52 ∨ N' = S53 ∨ N' = S54 ∨ N' = S55 ∨ N' = S56 ∨ N' = S57 ∨ N' = S58 ∨ N' = S59 ∨ N' = S60 ∨ N' = S61 ∨ N' = S62 ∨ N' = S63 ∨ N' = S64 ∨ N' = S65 ∨ N' = S66 ∨ N' = S67 ∨ N' = S68 ∨ N' = S69 ∨ N' = S70 ∨ N' = S71 ∨ N' = S72 ∨ N' = S73 ∨ N' = S74 ∨ N' = S75 ∨ N' = S76 ∨ N' = S77 ∨ N' = S78 ∨ N' = S79 ∨ N' = S80 ∨ N' = S81 ∨ N' = S82 ∨ N' = S83 ∨ N' = S84 ∨ N' = S85) :=
  fun N' hStar => brReach_aux Net N' hStar (Or.inl (by simp [Net, S0]))


theorem t0_1 : net_trans S0 (net_label.τ_comm "Client" "Info" "Request" "unit") S1 := by
  have h_send : sq_trans (BookClient, []) (sq_action.send "Info" "Request" "unit") (BC1, []) := by
    apply sq_trans.send
    unfold BookClient
    apply st_trans.intC
    simp [BC1]
  have h_recv : sq_trans (BookInfo, []) (sq_action.recv "Client" "Request" "unit") (BookInfo, [mReq]) :=
    sq_trans.recv
  have hmem_p : ("Client", (BookClient, [])) ∈ S0 := by simp [S0]
  have hmem_q : ("Info", (BookInfo, [])) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t1_2 : net_trans S1 (net_label.τ_dequeue "Info" "Client" "Request" "unit") S2 := by
  have hSQ : sq_trans (BookInfo, [mReq]) (sq_action.dequeue "Client" "Request" "unit") (BI1, []) := by
    apply sq_trans.dequeue
    · unfold BookInfo
      apply st_trans.extC
      simp [BI1, BI2, BI3, BI4, BI5]
    · exact qReq
  have hmem : ("Info", (BookInfo, [mReq])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem

theorem t2_3 : net_trans S2 (net_label.τ_comm "Info" "Review" "RqsReview" "unit") S3 := by
  have h_send : sq_trans (BI1, []) (sq_action.send "Review" "RqsReview" "unit") (BI2, []) := by
    apply sq_trans.send
    unfold BI1
    apply st_trans.intC
    simp [BI2, BI3, BI4, BI5]
  have h_recv : sq_trans (BookReview, []) (sq_action.recv "Info" "RqsReview" "unit") (BookReview, [mRqsReview]) :=
    sq_trans.recv
  have hmem_p : ("Info", (BI1, [])) ∈ S2 := by simp [S2]
  have hmem_q : ("Review", (BookReview, [])) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t3_4 : net_trans S3 (net_label.τ_dequeue "Review" "Info" "RqsReview" "unit") S4 := by
  have hSQ : sq_trans (BookReview, [mRqsReview]) (sq_action.dequeue "Info" "RqsReview" "unit") (BR1, []) := by
    apply sq_trans.dequeue
    · unfold BookReview
      apply st_trans.extC
      simp [BR1, BR2, BR3]
    · exact qRqsReview
  have hmem : ("Review", (BookReview, [mRqsReview])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem

theorem t4_6 : net_trans S4 (net_label.τ_comm "Review" "Ratings" "RqsRatings" "unit") S6 := by
  have h_send : sq_trans (BR1, []) (sq_action.send "Ratings" "RqsRatings" "unit") (BR2, []) := by
    apply sq_trans.send
    unfold BR1
    apply st_trans.intC
    simp [BR2, BR3]
  have h_recv : sq_trans (BookRatings, []) (sq_action.recv "Review" "RqsRatings" "unit") (BookRatings, [mRqsRatings]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR1, [])) ∈ S4 := by simp [S4]
  have hmem_q : ("Ratings", (BookRatings, [])) ∈ S4 := by simp [S4]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t5_8 : net_trans S5 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S8 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S5 := by simp [S5]
  exact net_trans.dequeue hSQ hmem

theorem t6_10 : net_trans S6 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S10 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S6 := by simp [S6]
  exact net_trans.dequeue hSQ hmem

theorem t7_12 : net_trans S7 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S12 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S7 := by simp [S7]
  exact net_trans.dequeue hSQ hmem

theorem t8_14 : net_trans S8 (net_label.τ_dequeue "Review" "Info" "RqsReview" "unit") S14 := by
  have hSQ : sq_trans (BookReview, [mRqsReview]) (sq_action.dequeue "Info" "RqsReview" "unit") (BR1, []) := by
    apply sq_trans.dequeue
    · unfold BookReview
      apply st_trans.extC
      simp [BR1, BR2, BR3]
    · exact qRqsReview
  have hmem : ("Review", (BookReview, [mRqsReview])) ∈ S8 := by simp [S8]
  exact net_trans.dequeue hSQ hmem

theorem t9_16 : net_trans S9 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S16 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S9 := by simp [S9]
  exact net_trans.dequeue hSQ hmem

theorem t10_17 : net_trans S10 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S17 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S10 := by simp [S10]
  have hmem_q : ("Review", (BR2, [])) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t11_19 : net_trans S11 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S19 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem

theorem t12_21 : net_trans S12 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S21 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S12 := by simp [S12]
  have hmem_q : ("Info", (BI3, [])) ∈ S12 := by simp [S12]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t13_23 : net_trans S13 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S23 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S13 := by simp [S13]
  exact net_trans.dequeue hSQ hmem

theorem t14_22 : net_trans S14 (net_label.τ_comm "Review" "Ratings" "RqsRatings" "unit") S22 := by
  have h_send : sq_trans (BR1, []) (sq_action.send "Ratings" "RqsRatings" "unit") (BR2, []) := by
    apply sq_trans.send
    unfold BR1
    apply st_trans.intC
    simp [BR2, BR3]
  have h_recv : sq_trans (BookRatings, []) (sq_action.recv "Review" "RqsRatings" "unit") (BookRatings, [mRqsRatings]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR1, [])) ∈ S14 := by simp [S14]
  have hmem_q : ("Ratings", (BookRatings, [])) ∈ S14 := by simp [S14]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t15_25 : net_trans S15 (net_label.τ_dequeue "Review" "Info" "RqsReview" "unit") S25 := by
  have hSQ : sq_trans (BookReview, [mRqsReview]) (sq_action.dequeue "Info" "RqsReview" "unit") (BR1, []) := by
    apply sq_trans.dequeue
    · unfold BookReview
      apply st_trans.extC
      simp [BR1, BR2, BR3]
    · exact qRqsReview
  have hmem : ("Review", (BookReview, [mRqsReview])) ∈ S15 := by simp [S15]
  exact net_trans.dequeue hSQ hmem

theorem t16_21 : net_trans S16 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S21 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S16 := by simp [S16]
  have hmem_q : ("Info", (BI3, [])) ∈ S16 := by simp [S16]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t17_26 : net_trans S17 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S26 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S17 := by simp [S17]
  exact net_trans.dequeue hSQ hmem

theorem t18_28 : net_trans S18 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S28 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S18 := by simp [S18]
  exact net_trans.dequeue hSQ hmem

theorem t19_30 : net_trans S19 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S30 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S19 := by simp [S19]
  exact net_trans.dequeue hSQ hmem

theorem t20_32 : net_trans S20 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S32 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S20 := by simp [S20]
  exact net_trans.dequeue hSQ hmem

theorem t21_33 : net_trans S21 (net_label.τ_comm "Review" "Ratings" "RqsRatings" "unit") S33 := by
  have h_send : sq_trans (BR1, []) (sq_action.send "Ratings" "RqsRatings" "unit") (BR2, []) := by
    apply sq_trans.send
    unfold BR1
    apply st_trans.intC
    simp [BR2, BR3]
  have h_recv : sq_trans (BookRatings, []) (sq_action.recv "Review" "RqsRatings" "unit") (BookRatings, [mRqsRatings]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR1, [])) ∈ S21 := by simp [S21]
  have hmem_q : ("Ratings", (BookRatings, [])) ∈ S21 := by simp [S21]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t22_34 : net_trans S22 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S34 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S22 := by simp [S22]
  exact net_trans.dequeue hSQ hmem

theorem t23_35 : net_trans S23 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S35 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S23 := by simp [S23]
  exact net_trans.dequeue hSQ hmem

theorem t24_36 : net_trans S24 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S36 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S24 := by simp [S24]
  exact net_trans.dequeue hSQ hmem

theorem t25_33 : net_trans S25 (net_label.τ_comm "Review" "Ratings" "RqsRatings" "unit") S33 := by
  have h_send : sq_trans (BR1, []) (sq_action.send "Ratings" "RqsRatings" "unit") (BR2, []) := by
    apply sq_trans.send
    unfold BR1
    apply st_trans.intC
    simp [BR2, BR3]
  have h_recv : sq_trans (BookRatings, []) (sq_action.recv "Review" "RqsRatings" "unit") (BookRatings, [mRqsRatings]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR1, [])) ∈ S25 := by simp [S25]
  have hmem_q : ("Ratings", (BookRatings, [])) ∈ S25 := by simp [S25]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t26_37 : net_trans S26 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S37 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI2, []) (sq_action.recv "Review" "RspReview" "unit") (BI2, [mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S26 := by simp [S26]
  have hmem_q : ("Info", (BI2, [])) ∈ S26 := by simp [S26]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t27_39 : net_trans S27 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S39 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S27 := by simp [S27]
  exact net_trans.dequeue hSQ hmem

theorem t28_41 : net_trans S28 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S41 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S28 := by simp [S28]
  have hmem_q : ("Info", (BI3, [])) ∈ S28 := by simp [S28]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t29_43 : net_trans S29 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S43 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S29 := by simp [S29]
  exact net_trans.dequeue hSQ hmem

theorem t30_42 : net_trans S30 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S42 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S30 := by simp [S30]
  have hmem_q : ("Review", (BR2, [])) ∈ S30 := by simp [S30]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t31_45 : net_trans S31 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S45 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S31 := by simp [S31]
  exact net_trans.dequeue hSQ hmem

theorem t32_41 : net_trans S32 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S41 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S32 := by simp [S32]
  have hmem_q : ("Info", (BI3, [])) ∈ S32 := by simp [S32]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t33_46 : net_trans S33 (net_label.τ_dequeue "Ratings" "Review" "RqsRatings" "unit") S46 := by
  have hSQ : sq_trans (BookRatings, [mRqsRatings]) (sq_action.dequeue "Review" "RqsRatings" "unit") (BRa1, []) := by
    apply sq_trans.dequeue
    · unfold BookRatings
      apply st_trans.extC
      simp [BRa1]
    · exact qRqsRatings
  have hmem : ("Ratings", (BookRatings, [mRqsRatings])) ∈ S33 := by simp [S33]
  exact net_trans.dequeue hSQ hmem

theorem t34_42 : net_trans S34 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S42 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S34 := by simp [S34]
  have hmem_q : ("Review", (BR2, [])) ∈ S34 := by simp [S34]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t35_41 : net_trans S35 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S41 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S35 := by simp [S35]
  have hmem_q : ("Info", (BI3, [])) ∈ S35 := by simp [S35]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t36_42 : net_trans S36 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S42 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S36 := by simp [S36]
  have hmem_q : ("Review", (BR2, [])) ∈ S36 := by simp [S36]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t37_47 : net_trans S37 (net_label.τ_comm "Info" "Details" "RqsDetail" "unit") S47 := by
  have h_send : sq_trans (BI2, [mRspReview]) (sq_action.send "Details" "RqsDetail" "unit") (BI3, [mRspReview]) := by
    apply sq_trans.send
    unfold BI2
    apply st_trans.intC
    simp [BI3, BI4, BI5]
  have h_recv : sq_trans (BookDetails, []) (sq_action.recv "Info" "RqsDetail" "unit") (BookDetails, [mRqsDetail]) :=
    sq_trans.recv
  have hmem_p : ("Info", (BI2, [mRspReview])) ∈ S37 := by simp [S37]
  have hmem_q : ("Details", (BookDetails, [])) ∈ S37 := by simp [S37]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t38_48 : net_trans S38 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S48 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S38 := by simp [S38]
  exact net_trans.dequeue hSQ hmem

theorem t39_50 : net_trans S39 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S50 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S39 := by simp [S39]
  exact net_trans.dequeue hSQ hmem

theorem t40_52 : net_trans S40 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S52 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S40 := by simp [S40]
  exact net_trans.dequeue hSQ hmem

theorem t41_53 : net_trans S41 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S53 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S41 := by simp [S41]
  have hmem_q : ("Review", (BR2, [])) ∈ S41 := by simp [S41]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t42_54 : net_trans S42 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S54 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S42 := by simp [S42]
  exact net_trans.dequeue hSQ hmem

theorem t43_55 : net_trans S43 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S55 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S43 := by simp [S43]
  exact net_trans.dequeue hSQ hmem

theorem t44_57 : net_trans S44 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S57 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S44 := by simp [S44]
  exact net_trans.dequeue hSQ hmem

theorem t45_53 : net_trans S45 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S53 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S45 := by simp [S45]
  have hmem_q : ("Review", (BR2, [])) ∈ S45 := by simp [S45]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t46_53 : net_trans S46 (net_label.τ_comm "Ratings" "Review" "RspRatings" "unit") S53 := by
  have h_send : sq_trans (BRa1, []) (sq_action.send "Review" "RspRatings" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BRa1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BR2, []) (sq_action.recv "Ratings" "RspRatings" "unit") (BR2, [mRspRatings]) :=
    sq_trans.recv
  have hmem_p : ("Ratings", (BRa1, [])) ∈ S46 := by simp [S46]
  have hmem_q : ("Review", (BR2, [])) ∈ S46 := by simp [S46]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t47_58 : net_trans S47 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S58 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S47 := by simp [S47]
  exact net_trans.dequeue hSQ hmem

theorem t48_60 : net_trans S48 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S60 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S48 := by simp [S48]
  have hmem_q : ("Info", (BI3, [])) ∈ S48 := by simp [S48]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t49_62 : net_trans S49 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S62 := by
  have hSQ : sq_trans (BI3, [mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, []) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qRspReview_single
  have hmem : ("Info", (BI3, [mRspReview])) ∈ S49 := by simp [S49]
  exact net_trans.dequeue hSQ hmem

theorem t50_61 : net_trans S50 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S61 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S50 := by simp [S50]
  have hmem_q : ("Info", (BI3, [])) ∈ S50 := by simp [S50]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t51_63 : net_trans S51 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S63 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S51 := by simp [S51]
  exact net_trans.dequeue hSQ hmem

theorem t52_60 : net_trans S52 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S60 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S52 := by simp [S52]
  have hmem_q : ("Info", (BI3, [])) ∈ S52 := by simp [S52]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t53_64 : net_trans S53 (net_label.τ_dequeue "Review" "Ratings" "RspRatings" "unit") S64 := by
  have hSQ : sq_trans (BR2, [mRspRatings]) (sq_action.dequeue "Ratings" "RspRatings" "unit") (BR3, []) := by
    apply sq_trans.dequeue
    · unfold BR2
      apply st_trans.extC
      simp [BR3]
    · exact qRspRatings
  have hmem : ("Review", (BR2, [mRspRatings])) ∈ S53 := by simp [S53]
  exact net_trans.dequeue hSQ hmem

theorem t54_65 : net_trans S54 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S65 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S54 := by simp [S54]
  have hmem_q : ("Info", (BI3, [])) ∈ S54 := by simp [S54]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t55_60 : net_trans S55 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S60 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Details" "RspDetail" "unit") (BI3, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S55 := by simp [S55]
  have hmem_q : ("Info", (BI3, [])) ∈ S55 := by simp [S55]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t56_66 : net_trans S56 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S66 := by
  have hSQ : sq_trans (BI3, [mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, []) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qRspReview_single
  have hmem : ("Info", (BI3, [mRspReview])) ∈ S56 := by simp [S56]
  exact net_trans.dequeue hSQ hmem

theorem t57_61 : net_trans S57 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S61 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, []) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S57 := by simp [S57]
  have hmem_q : ("Info", (BI3, [])) ∈ S57 := by simp [S57]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t58_67 : net_trans S58 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S67 := by
  have hSQ : sq_trans (BI3, [mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, []) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qRspReview_single
  have hmem : ("Info", (BI3, [mRspReview])) ∈ S58 := by simp [S58]
  exact net_trans.dequeue hSQ hmem

theorem t59_69 : net_trans S59 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S69 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S59 := by simp [S59]
  exact net_trans.dequeue hSQ hmem

theorem t60_70 : net_trans S60 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S70 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, [mRspDetail]) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspDetail, mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S60 := by simp [S60]
  have hmem_q : ("Info", (BI3, [mRspDetail])) ∈ S60 := by simp [S60]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t61_71 : net_trans S61 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S71 := by
  have hSQ : sq_trans (BI3, [mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, []) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qRspReview_single
  have hmem : ("Info", (BI3, [mRspReview])) ∈ S61 := by simp [S61]
  exact net_trans.dequeue hSQ hmem

theorem t62_69 : net_trans S62 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S69 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S62 := by simp [S62]
  exact net_trans.dequeue hSQ hmem

theorem t63_70 : net_trans S63 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S70 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, [mRspDetail]) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspDetail, mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S63 := by simp [S63]
  have hmem_q : ("Info", (BI3, [mRspDetail])) ∈ S63 := by simp [S63]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t64_72 : net_trans S64 (net_label.τ_comm "Review" "Info" "RspReview" "unit") S72 := by
  have h_send : sq_trans (BR3, []) (sq_action.send "Info" "RspReview" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BR3
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI3, [mRspDetail]) (sq_action.recv "Review" "RspReview" "unit") (BI3, [mRspDetail, mRspReview]) :=
    sq_trans.recv
  have hmem_p : ("Review", (BR3, [])) ∈ S64 := by simp [S64]
  have hmem_q : ("Info", (BI3, [mRspDetail])) ∈ S64 := by simp [S64]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t65_73 : net_trans S65 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S73 := by
  have hSQ : sq_trans (BI3, [mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, []) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qRspReview_single
  have hmem : ("Info", (BI3, [mRspReview])) ∈ S65 := by simp [S65]
  exact net_trans.dequeue hSQ hmem

theorem t66_69 : net_trans S66 (net_label.τ_dequeue "Details" "Info" "RqsDetail" "unit") S69 := by
  have hSQ : sq_trans (BookDetails, [mRqsDetail]) (sq_action.dequeue "Info" "RqsDetail" "unit") (BD1, []) := by
    apply sq_trans.dequeue
    · unfold BookDetails
      apply st_trans.extC
      simp [BD1]
    · exact qRqsDetail
  have hmem : ("Details", (BookDetails, [mRqsDetail])) ∈ S66 := by simp [S66]
  exact net_trans.dequeue hSQ hmem

theorem t67_74 : net_trans S67 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S74 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI4, []) (sq_action.recv "Details" "RspDetail" "unit") (BI4, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S67 := by simp [S67]
  have hmem_q : ("Info", (BI4, [])) ∈ S67 := by simp [S67]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t68_74 : net_trans S68 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S74 := by
  have hSQ : sq_trans (BI3, [mRspReview, mRspDetail]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, [mRspDetail]) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qReviewDetails_Review
  have hmem : ("Info", (BI3, [mRspReview, mRspDetail])) ∈ S68 := by simp [S68]
  exact net_trans.dequeue hSQ hmem

theorem t69_74 : net_trans S69 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S74 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI4, []) (sq_action.recv "Details" "RspDetail" "unit") (BI4, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S69 := by simp [S69]
  have hmem_q : ("Info", (BI4, [])) ∈ S69 := by simp [S69]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t70_75 : net_trans S70 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S75 := by
  have hSQ : sq_trans (BI3, [mRspDetail, mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, [mRspDetail]) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qDetailsReview_Review
  have hmem : ("Info", (BI3, [mRspDetail, mRspReview])) ∈ S70 := by simp [S70]
  exact net_trans.dequeue hSQ hmem

theorem t71_74 : net_trans S71 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S74 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI4, []) (sq_action.recv "Details" "RspDetail" "unit") (BI4, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S71 := by simp [S71]
  have hmem_q : ("Info", (BI4, [])) ∈ S71 := by simp [S71]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t72_76 : net_trans S72 (net_label.τ_dequeue "Info" "Review" "RspReview" "unit") S76 := by
  have hSQ : sq_trans (BI3, [mRspDetail, mRspReview]) (sq_action.dequeue "Review" "RspReview" "unit") (BI4, [mRspDetail]) := by
    apply sq_trans.dequeue
    · unfold BI3
      apply st_trans.extC
      simp [BI4, BI5]
    · exact qDetailsReview_Review
  have hmem : ("Info", (BI3, [mRspDetail, mRspReview])) ∈ S72 := by simp [S72]
  exact net_trans.dequeue hSQ hmem

theorem t73_74 : net_trans S73 (net_label.τ_comm "Details" "Info" "RspDetail" "unit") S74 := by
  have h_send : sq_trans (BD1, []) (sq_action.send "Info" "RspDetail" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BD1
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BI4, []) (sq_action.recv "Details" "RspDetail" "unit") (BI4, [mRspDetail]) :=
    sq_trans.recv
  have hmem_p : ("Details", (BD1, [])) ∈ S73 := by simp [S73]
  have hmem_q : ("Info", (BI4, [])) ∈ S73 := by simp [S73]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t74_77 : net_trans S74 (net_label.τ_dequeue "Info" "Details" "RspDetail" "unit") S77 := by
  have hSQ : sq_trans (BI4, [mRspDetail]) (sq_action.dequeue "Details" "RspDetail" "unit") (BI5, []) := by
    apply sq_trans.dequeue
    · unfold BI4
      apply st_trans.extC
      simp [BI5]
    · exact qRspDetail_single
  have hmem : ("Info", (BI4, [mRspDetail])) ∈ S74 := by simp [S74]
  exact net_trans.dequeue hSQ hmem

theorem t75_78 : net_trans S75 (net_label.τ_dequeue "Info" "Details" "RspDetail" "unit") S78 := by
  have hSQ : sq_trans (BI4, [mRspDetail]) (sq_action.dequeue "Details" "RspDetail" "unit") (BI5, []) := by
    apply sq_trans.dequeue
    · unfold BI4
      apply st_trans.extC
      simp [BI5]
    · exact qRspDetail_single
  have hmem : ("Info", (BI4, [mRspDetail])) ∈ S75 := by simp [S75]
  exact net_trans.dequeue hSQ hmem

theorem t76_79 : net_trans S76 (net_label.τ_dequeue "Info" "Details" "RspDetail" "unit") S79 := by
  have hSQ : sq_trans (BI4, [mRspDetail]) (sq_action.dequeue "Details" "RspDetail" "unit") (BI5, []) := by
    apply sq_trans.dequeue
    · unfold BI4
      apply st_trans.extC
      simp [BI5]
    · exact qRspDetail_single
  have hmem : ("Info", (BI4, [mRspDetail])) ∈ S76 := by simp [S76]
  exact net_trans.dequeue hSQ hmem

theorem t77_80 : net_trans S77 (net_label.τ_comm "Info" "Client" "Response" "unit") S80 := by
  have h_send : sq_trans (BI5, []) (sq_action.send "Client" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BI5
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BC1, []) (sq_action.recv "Info" "Response" "unit") (BC1, [mResp]) :=
    sq_trans.recv
  have hmem_p : ("Info", (BI5, [])) ∈ S77 := by simp [S77]
  have hmem_q : ("Client", (BC1, [])) ∈ S77 := by simp [S77]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t78_81 : net_trans S78 (net_label.τ_comm "Info" "Client" "Response" "unit") S81 := by
  have h_send : sq_trans (BI5, []) (sq_action.send "Client" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BI5
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BC1, []) (sq_action.recv "Info" "Response" "unit") (BC1, [mResp]) :=
    sq_trans.recv
  have hmem_p : ("Info", (BI5, [])) ∈ S78 := by simp [S78]
  have hmem_q : ("Client", (BC1, [])) ∈ S78 := by simp [S78]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t79_82 : net_trans S79 (net_label.τ_comm "Info" "Client" "Response" "unit") S82 := by
  have h_send : sq_trans (BI5, []) (sq_action.send "Client" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold BI5
    apply st_trans.intC
    simp
  have h_recv : sq_trans (BC1, []) (sq_action.recv "Info" "Response" "unit") (BC1, [mResp]) :=
    sq_trans.recv
  have hmem_p : ("Info", (BI5, [])) ∈ S79 := by simp [S79]
  have hmem_q : ("Client", (BC1, [])) ∈ S79 := by simp [S79]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t80_83 : net_trans S80 (net_label.τ_dequeue "Client" "Info" "Response" "unit") S83 := by
  have hSQ : sq_trans (BC1, [mResp]) (sq_action.dequeue "Info" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold BC1
      apply st_trans.extC
      simp
    · exact qResp
  have hmem : ("Client", (BC1, [mResp])) ∈ S80 := by simp [S80]
  exact net_trans.dequeue hSQ hmem

theorem t81_84 : net_trans S81 (net_label.τ_dequeue "Client" "Info" "Response" "unit") S84 := by
  have hSQ : sq_trans (BC1, [mResp]) (sq_action.dequeue "Info" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold BC1
      apply st_trans.extC
      simp
    · exact qResp
  have hmem : ("Client", (BC1, [mResp])) ∈ S81 := by simp [S81]
  exact net_trans.dequeue hSQ hmem

theorem t82_85 : net_trans S82 (net_label.τ_dequeue "Client" "Info" "Response" "unit") S85 := by
  have hSQ : sq_trans (BC1, [mResp]) (sq_action.dequeue "Info" "Response" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold BC1
      apply st_trans.extC
      simp
    · exact qResp
  have hmem : ("Client", (BC1, [mResp])) ∈ S82 := by simp [S82]
  exact net_trans.dequeue hSQ hmem



/-- `Net` is half-duplex: opposite queues never both fill. -/
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := brReach _ hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- S0
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S1
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S2
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S3
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S4
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S5
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S6
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S7
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S8
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S9
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S10
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S11
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S12
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S13
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S14
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S15
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S16
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S17
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S18
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S19
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S20
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S21
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S22
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S23
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S24
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S25
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S26
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S27
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S28
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S29
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S30
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S31
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S32
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S33
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S34
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S35
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S36
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S37
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S38
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S39
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S40
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S41
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S42
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S43
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S44
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S45
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S46
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S47
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S48
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S49
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S50
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S51
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S52
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S53
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S54
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S55
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S56
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S57
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S58
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S59
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S60
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S61
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S62
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S63
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S64
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
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
  · -- S65
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S66
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S67
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S68
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S69
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S70
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S71
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S72
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S73
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S74
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S75
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S76
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S77
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S78
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S79
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S80
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S81
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S82
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
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
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S83
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S84
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil
  · -- S85
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    · exact absurd hCp noContainsNil


theorem Net_NoRec : Net.NoRec := by
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact BookClient_norec
  · exact BookInfo_norec
  · exact BookReview_norec
  · exact BookDetails_norec
  · exact BookRatings_norec

theorem brOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := brReach _ hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact hStuck ⟨_, _, by trivial, t0_1⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1_2⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t2_3⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t3_4⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t4_6⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t5_8⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t6_10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t7_12⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t8_14⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t9_16⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t10_17⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t11_19⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t12_21⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t13_23⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t14_22⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t15_25⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t16_21⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t17_26⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t18_28⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t19_30⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t20_32⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t21_33⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t22_34⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t23_35⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t24_36⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t25_33⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t26_37⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t27_39⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t28_41⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t29_43⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t30_42⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t31_45⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t32_41⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t33_46⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t34_42⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t35_41⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t36_42⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t37_47⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t38_48⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t39_50⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t40_52⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t41_53⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t42_54⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t43_55⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t44_57⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t45_53⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t46_53⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t47_58⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t48_60⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t49_62⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t50_61⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t51_63⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t52_60⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t53_64⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t54_65⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t55_60⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t56_66⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t57_61⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t58_67⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t59_69⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t60_70⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t61_71⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t62_69⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t63_70⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t64_72⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t65_73⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t66_69⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t67_74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t68_74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t69_74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t70_75⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t71_74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t72_76⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t73_74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t74_77⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t75_78⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t76_79⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t77_80⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t78_81⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t79_82⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t80_83⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t81_84⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t82_85⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · intro r T Q p lab S Q' hmem hQ
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · intro r T Q p lab S Q' hmem hQ
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

/-- `Net` is output-live: fair paths drain queues, stuck states stay clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨norec_live_infinite_vacuous Net_NoRec Net_wellFormed, brOL_stuck⟩


end Bookreview
