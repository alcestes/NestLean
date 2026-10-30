import Nest.Examples.Game

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Game

-- Queue-membership characterization for decidable HD arms.
theorem QueueContainsFrom_iff_exists_mem_Game {Q : Queue} {p : Role} :
    QueueContainsFrom Q p ↔ ∃ m ∈ Q, m.1 = p := by
  constructor
  · rintro ⟨lab, S, hmem⟩
    exact ⟨_, hmem.to_mem, rfl⟩
  · rintro ⟨m, hmem, rfl⟩
    induction Q with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with h | hmem
      · subst m
        exact ⟨hd.2, hd.3, QueueMem.head⟩
      · obtain ⟨lab, S, hmemp⟩ := ih hmem
        exact ⟨lab, S, QueueMem.tail hmemp⟩

-- Half-duplex transfer over the canonical cover.
theorem gameHHD : ∀ C ∈ Cs, ∀ (p q : Role) (Qp Qq : Queue),
    NetworkHasQueue C p Qp → NetworkHasQueue C q Qq →
    QueueContainsFrom Qp q → ¬ QueueContainsFrom Qq p := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_1
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_2
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_3
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_4
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_5
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_6
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_7
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_8
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_9
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_10
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_11
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_12
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_13
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_14
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_15
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_16
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_17
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_18
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_19
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_20
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_21
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_22
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_23
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_24
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_25
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_26
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_27
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_28
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_29
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_30
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_31
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_32
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_33
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_34
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_35
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_36
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_37
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_38
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_39
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_40
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_41
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_42
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_43
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_44
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_45
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_46
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_47
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_48
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_49
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_50
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_51
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_52
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_53
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_54
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_55
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_56
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_57
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_58
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_59
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_60
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_61
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_62
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_63
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_64
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_65
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_66
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_67
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_68
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_69
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_70
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_71
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_72
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_73
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_74
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_75
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_76
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_77
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_78
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_79
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_80
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_81
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_82
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_83
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_84
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_85
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_86
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_87
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_88
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_89
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_90
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_91
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_92
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_93
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_94
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_95
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_96
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_97
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_98
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_99
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_100
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_101
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_102
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_103
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_104
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_105
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_106
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_107
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
  · -- CS_108
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem_Game]
      decide

-- Stuck-state no-orphan closure.
theorem gameHNO : ∀ C ∈ Cs, IsStuckNetwork C → NoOrphanMessages C := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0 (stuck, all queues empty)
    intro _ r T Q p lab S Q' hmem hQ
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_1 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "GameServer" "YouLost" "unit", [("Player_2", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_1).Nodup) (by decide)⟩) hStuck
  · -- CS_2 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "GameServer" "YouWon" "unit", [("Player_2", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_2).Nodup) (by decide)⟩) hStuck
  · -- CS_3 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "Coordinator" "GameFound" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_3).Nodup) (by decide)⟩) hStuck
  · -- CS_4 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "Coordinator" "GameFound" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_4).Nodup) (by decide)⟩) hStuck
  · -- CS_5 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouLost" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_5).Nodup) (by decide)⟩) hStuck
  · -- CS_6 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouLost" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_6).Nodup) (by decide)⟩) hStuck
  · -- CS_7 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouLost" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_7).Nodup) (by decide)⟩) hStuck
  · -- CS_8 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouWon" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_8).Nodup) (by decide)⟩) hStuck
  · -- CS_9 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouWon" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_9).Nodup) (by decide)⟩) hStuck
  · -- CS_10 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "YouWon" "unit", [("Player_1", (SessionType.tEnd, [])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_10).Nodup) (by decide)⟩) hStuck
  · -- CS_11 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_11).Nodup) (by decide)⟩) hStuck
  · -- CS_12 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_12).Nodup) (by decide)⟩) hStuck
  · -- CS_13 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_13).Nodup) (by decide)⟩) hStuck
  · -- CS_14 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_14).Nodup) (by decide)⟩) hStuck
  · -- CS_15 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_15).Nodup) (by decide)⟩) hStuck
  · -- CS_16 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_16).Nodup) (by decide)⟩) hStuck
  · -- CS_17 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "GameServer" "GameFound" "unit", [("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_18 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "GameServer" "GameFound" "unit", [("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_19 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "GameServer" "GameFound" "unit", [("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_20 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "GameServer" "GameFound" "unit", [("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_21 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_1" "GameFound" "unit", [("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C5, [])), ("GameServer", (GameServer, [])), ("Player_2", (PG, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_22 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_1" "Init" "unit", [("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Coordinator", (C1, [])), ("GameServer", (GameServer, [])), ("Player_2", (Player, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_23 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_2" "GameFound" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_24 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_2" "GameFound" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_25 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_2" "Init" "unit", [("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_26 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_2" "Init" "unit", [("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (PL, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_27 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Coordinator" "Player_2" "Init" "unit", [("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_28 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_28).Nodup) (by decide)⟩) hStuck
  · -- CS_29 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_29).Nodup) (by decide)⟩) hStuck
  · -- CS_30 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_30).Nodup) (by decide)⟩) hStuck
  · -- CS_31 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_31).Nodup) (by decide)⟩) hStuck
  · -- CS_32 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_32).Nodup) (by decide)⟩) hStuck
  · -- CS_33 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_33).Nodup) (by decide)⟩) hStuck
  · -- CS_34 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_34).Nodup) (by decide)⟩) hStuck
  · -- CS_35 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_35).Nodup) (by decide)⟩) hStuck
  · -- CS_36 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_36).Nodup) (by decide)⟩) hStuck
  · -- CS_37 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_37).Nodup) (by decide)⟩) hStuck
  · -- CS_38 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_38).Nodup) (by decide)⟩) hStuck
  · -- CS_39 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_39).Nodup) (by decide)⟩) hStuck
  · -- CS_40 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_40).Nodup) (by decide)⟩) hStuck
  · -- CS_41 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_41).Nodup) (by decide)⟩) hStuck
  · -- CS_42 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_42).Nodup) (by decide)⟩) hStuck
  · -- CS_43 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_43).Nodup) (by decide)⟩) hStuck
  · -- CS_44 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "GameServer" "GameOver" "unit", [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_44).Nodup) (by decide)⟩) hStuck
  · -- CS_45 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_46 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_47 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_48 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_49 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_50 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_51 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_52 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_53 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_54 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_55 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_56 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_57 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_58 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_59 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_60 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_61 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Coordinator" "GameOver" "unit", [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_62 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "TurnStart" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTAS, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_63 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "TurnStart" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTAS, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_64 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_65 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_66 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_67 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_68 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_69 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouLost" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_70 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_71 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (SessionType.tEnd, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_72 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_73 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_74 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_75 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_2" "YouWon" "unit", [("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("GameServer", (GSOver, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_76 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_1" "TurnStart" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTA1S, [])), ("Coordinator", (C7, [])), ("Player_2", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_77 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_1" "TurnStart" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTA1S, [])), ("Coordinator", (C7, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_78 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_1" "TurnStart" "unit", [("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTA1S, [])), ("Coordinator", (C7, [])), ("Player_2", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_79 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "GameServer" "Player_1" "TurnStart" "unit", [("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("GameServer", (GTA1S, [])), ("Coordinator", (C7, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_80 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Coordinator" "GameFound" "unit", [("GameServer", (GRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_80).Nodup) (by decide)⟩) hStuck
  · -- CS_81 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Coordinator" "GameFound" "unit", [("GameServer", (GRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_81).Nodup) (by decide)⟩) hStuck
  · -- CS_82 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Coordinator" "GameFound" "unit", [("GameServer", (GRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_82).Nodup) (by decide)⟩) hStuck
  · -- CS_83 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Coordinator" "GameFound" "unit", [("GameServer", (GRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_83).Nodup) (by decide)⟩) hStuck
  · -- CS_84 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Player_1" "TakeAction" "unit", [("GameServer", (GT2S, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_84).Nodup) (by decide)⟩) hStuck
  · -- CS_85 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Player_1" "TakeAction" "unit", [("GameServer", (GT2S, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_85).Nodup) (by decide)⟩) hStuck
  · -- CS_86 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_1" "GameServer" "TakeAction" "unit", [("GameServer", (GTA1S, [QueueMessage.msg "Player_1" "TakeAction" "unit"])), ("Player_1", (PRec, [])), ("Coordinator", (C7, [])), ("Player_2", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_87 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_1" "GameServer" "TakeAction" "unit", [("GameServer", (GTA1S, [QueueMessage.msg "Player_1" "TakeAction" "unit"])), ("Player_1", (PRec, [])), ("Coordinator", (C7, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_88 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "TurnStart" "unit", [("Player_1", (PTAS, [])), ("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_88).Nodup) (by decide)⟩) hStuck
  · -- CS_89 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "GameServer" "TurnStart" "unit", [("Player_1", (PTAS, [])), ("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_89).Nodup) (by decide)⟩) hStuck
  · -- CS_90 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_90).Nodup) (by decide)⟩) hStuck
  · -- CS_91 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "GameFound" "unit", [("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_91).Nodup) (by decide)⟩) hStuck
  · -- CS_92 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "GameServer" "Player_2" "TakeAction" "unit", [("GameServer", (GRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_92).Nodup) (by decide)⟩) hStuck
  · -- CS_93 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_2" "GameServer" "TakeAction" "unit", [("GameServer", (GTAS, [QueueMessage.msg "Player_2" "TakeAction" "unit"])), ("Player_2", (PRec, [])), ("Coordinator", (C7, [])), ("Player_1", (PRec, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_94 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "GameServer" "TurnStart" "unit", [("Player_2", (PTAS, [])), ("Coordinator", (C7, [])), ("GameServer", (GTAS, [])), ("Player_1", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_94).Nodup) (by decide)⟩) hStuck
  · -- CS_95 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "Coordinator" "GameFound" "unit", [("Player_2", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Coordinator", (C7, [])), ("GameServer", (GTAS, [])), ("Player_1", (PRec, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_95).Nodup) (by decide)⟩) hStuck
  · -- CS_96 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "Player_1" "LookForGame" "unit", [("Coordinator", (C3, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_96).Nodup) (by decide)⟩) hStuck
  · -- CS_97 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "Player_1" "LookForGame" "unit", [("Coordinator", (C3, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PL, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_97).Nodup) (by decide)⟩) hStuck
  · -- CS_98 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "Player_1" "LookForGame" "unit", [("Coordinator", (C3, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_98).Nodup) (by decide)⟩) hStuck
  · -- CS_99 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "Player_1" "LookForGame" "unit", [("Coordinator", (C3, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_99).Nodup) (by decide)⟩) hStuck
  · -- CS_100 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_1" "Coordinator" "LookForGame" "unit", [("Coordinator", (C2, [QueueMessage.msg "Player_2" "LookForGame" "unit", QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("Player_1", (PG, [])), ("GameServer", (GameServer, [])), ("Player_2", (PG, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_101 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "Init" "unit", [("Player_1", (PL, [])), ("Coordinator", (C2, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_2", (PG, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_101).Nodup) (by decide)⟩) hStuck
  · -- CS_102 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_1" "Coordinator" "LookForGame" "unit", [("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("Player_1", (PG, [])), ("GameServer", (GameServer, [])), ("Player_2", (PL, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_103 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_1" "Coordinator" "LookForGame" "unit", [("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("Player_1", (PG, [])), ("GameServer", (GameServer, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_104 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "Init" "unit", [("Player_1", (PL, [])), ("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_2", (PL, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_104).Nodup) (by decide)⟩) hStuck
  · -- CS_105 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_1" "Coordinator" "Init" "unit", [("Player_1", (PL, [])), ("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_105).Nodup) (by decide)⟩) hStuck
  · -- CS_106 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Coordinator" "Player_2" "LookForGame" "unit", [("Coordinator", (C4, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_106).Nodup) (by decide)⟩) hStuck
  · -- CS_107 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Player_2" "Coordinator" "LookForGame" "unit", [("Coordinator", (C3, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("Player_2", (PG, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, []))], by trivial, net_transb_comm_sound (fuel := 4) (by decide)⟩) hStuck
  · -- CS_108 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Player_2" "Coordinator" "Init" "unit", [("Player_2", (PL, [])), ("Coordinator", (C3, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, []))], by trivial, net_transb_single_sound (fuel := 4) (by decide : (List.map Prod.fst CS_108).Nodup) (by decide)⟩) hStuck

theorem Net_halfDuplex : IsHalfDuplex Net :=
  IsHalfDuplex_of_canon_cover gameCover gameHHD

theorem Net_noOrphanStuck (N' : Network) (hStar : net_trans_star Net N')
    (hStuck : IsStuckNetwork N') : NoOrphanMessages N' :=
  noOrphan_of_canon_cover_stuck gameCover gameHNO N' hStar hStuck

end Game
