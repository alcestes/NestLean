import Nest.Examples.Vpn

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Vpn

-- Half-duplex: uniform decidable per-pair goals.
theorem vpnHHD : ∀ C ∈ Cs, ∀ (p q : Role) (Qp Qq : Queue),
    NetworkHasQueue C p Qp → NetworkHasQueue C q Qq →
    QueueContainsFrom Qp q → ¬ QueueContainsFrom Qq p := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_1
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_2
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_3
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_4
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_5
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_6
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_7
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_8
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_9
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_10
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_11
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_12
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_13
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_14
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_15
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_16
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_17
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_18
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_19
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_20
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_21
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_22
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_23
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_24
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_25
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_26
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_27
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_28
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_29
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_30
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_31
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_32
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_33
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_34
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_35
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_36
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_37
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_38
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_39
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_40
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_41
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_42
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_43
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_44
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_45
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_46
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_47
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_48
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_49
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_50
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_51
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_52
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_53
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_54
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_55
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_56
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_57
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_58
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_59
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_60
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_61
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_62
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_63
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_64
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_65
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_66
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_67
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_68
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_69
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_70
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_71
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_72
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_73
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_74
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_75
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_76
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_77
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_78
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_79
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_80
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_81
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_82
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_83
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_84
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_85
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_86
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_87
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_88
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_89
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_90
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_91
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_92
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_93
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_94
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_95
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_96
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_97
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_98
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_99
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_100
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_101
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_102
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_103
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_104
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_105
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_106
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_107
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_108
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_109
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_109, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_110
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_110, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_111
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_111, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_112
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_112, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_113
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_113, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_114
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_114, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_115
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_115, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_116
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_116, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_117
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_117, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_118
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_118, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_119
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_119, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_120
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_120, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_121
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_121, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_122
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_122, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_123
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_123, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_124
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_124, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_125
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_125, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_126
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_126, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_127
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_127, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_128
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_128, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_129
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_129, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_130
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_130, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_131
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_131, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_132
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_132, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_133
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_133, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_134
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_134, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_135
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_135, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_136
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_136, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_137
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_137, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_138
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_138, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_139
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_139, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_140
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_140, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_141
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_141, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_142
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_142, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_143
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_143, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_144
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_144, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_145
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_145, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_146
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_146, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_147
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_147, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_148
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_148, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_149
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_149, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_150
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_150, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_151
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_151, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_152
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_152, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_153
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_153, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_154
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_154, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_155
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_155, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_156
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_156, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_157
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_157, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_158
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_158, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_159
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_159, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_160
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_160, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_161
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_161, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_162
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_162, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_163
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_163, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_164
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_164, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_165
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_165, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_166
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_166, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_167
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_167, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_168
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_168, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_169
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_169, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_170
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_170, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_171
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_171, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_172
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_172, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_173
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_173, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_174
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_174, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_175
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_175, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_176
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_176, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_177
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_177, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_178
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_178, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_179
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_179, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_180
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_180, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_181
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_181, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_182
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_182, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_183
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_183, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_184
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_184, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_185
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_185, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_186
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_186, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_187
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_187, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_188
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_188, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_189
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_189, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_190
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_190, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_191
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_191, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_192
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_192, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_193
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_193, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_194
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_194, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_195
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_195, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_196
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_196, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_197
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_197, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_198
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_198, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_199
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_199, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_200
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_200, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_201
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_201, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_202
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_202, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_203
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_203, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_204
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_204, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_205
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_205, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_206
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_206, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_207
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_207, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_208
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_208, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_209
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_209, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_210
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_210, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_211
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_211, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_212
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_212, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_213
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_213, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_214
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_214, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_215
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_215, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_216
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_216, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_217
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_217, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_218
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_218, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_219
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_219, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_220
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_220, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_221
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_221, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_222
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_222, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_223
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_223, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_224
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_224, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_225
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_225, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_226
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_226, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_227
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_227, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_228
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_228, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_229
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_229, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_230
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_230, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_231
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_231, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
  · -- CS_232
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_232, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide
    · simp only [QueueContainsFrom_iff_exists_mem]
      decide

-- Stuck-state no-orphan closure.
theorem vpnHNO : ∀ C ∈ Cs, IsStuckNetwork C → NoOrphanMessages C := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    exact absurd (⟨net_label.τ_dequeue "C_C" "C_A" "Term" "unit", (CS_1.replace "C_C" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_1).Nodup) (show net_transb 2 CS_1 (net_label.τ_dequeue "C_C" "C_A" "Term" "unit") (CS_1.replace "C_C" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_2 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Acc" "unit", (CS_2.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_2).Nodup) (show net_transb 1 CS_2 (net_label.τ_dequeue "C_C" "Auth" "Acc" "unit") (CS_2.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_3 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Acc" "unit", (CS_3.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_3).Nodup) (show net_transb 1 CS_3 (net_label.τ_dequeue "C_C" "Auth" "Acc" "unit") (CS_3.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_4 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_4.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_4).Nodup) (show net_transb 2 CS_4 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_4.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_5 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_5.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_5).Nodup) (show net_transb 2 CS_5 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_5.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_6 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_6.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_6).Nodup) (show net_transb 2 CS_6 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_6.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_7 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_7.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_7).Nodup) (show net_transb 2 CS_7 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_7.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_8 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_8.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_8).Nodup) (show net_transb 1 CS_8 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_8.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_9 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_9.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_9).Nodup) (show net_transb 1 CS_9 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_9.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_10 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_10.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_10).Nodup) (show net_transb 1 CS_10 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_10.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_11 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_11.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_11).Nodup) (show net_transb 1 CS_11 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_11.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_12 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_12.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_12).Nodup) (show net_transb 1 CS_12 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_12.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_13 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_13.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_13).Nodup) (show net_transb 1 CS_13 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_13.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_14 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_14.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_14).Nodup) (show net_transb 1 CS_14 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_14.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_15 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_15.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_15).Nodup) (show net_transb 1 CS_15 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_15.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_16 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_A" "Acc" "unit", ((CS_16.replace "Auth" (AA, [])).replace "C_A" (VATES, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_16 (net_label.τ_comm "Auth" "C_A" "Acc" "unit") ((CS_16.replace "Auth" (AA, [])).replace "C_A" (VATES, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_17 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_A" "Init" "unit", ((CS_17.replace "Auth" (AV1, [])).replace "C_A" (ClientA, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_17 (net_label.τ_comm "Auth" "C_A" "Init" "unit") ((CS_17.replace "Auth" (AV1, [])).replace "C_A" (ClientA, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_18 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_18.replace "Auth" (AAA, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_18 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_18.replace "Auth" (AAA, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_19 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_19.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_19 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_19.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_20 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_20.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_20 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_20.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_21 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_21.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_21 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_21.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_22 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_22.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_22 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_22.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_23 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_23.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_23 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_23.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_24 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Acc" "unit", ((CS_24.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_24 (net_label.τ_comm "Auth" "C_B" "Acc" "unit") ((CS_24.replace "Auth" (AAA, [])).replace "C_B" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_25 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Deny" "unit", ((CS_25.replace "Auth" (ADnnS, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_25 (net_label.τ_comm "Auth" "C_B" "Deny" "unit") ((CS_25.replace "Auth" (ADnnS, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_26 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Deny" "unit", ((CS_26.replace "Auth" (ADnnS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_26 (net_label.τ_comm "Auth" "C_B" "Deny" "unit") ((CS_26.replace "Auth" (ADnnS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_27 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Deny" "unit", ((CS_27.replace "Auth" (ADnnS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_27 (net_label.τ_comm "Auth" "C_B" "Deny" "unit") ((CS_27.replace "Auth" (ADnnS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_28 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Init" "unit", ((CS_28.replace "Auth" (AV2, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_28 (net_label.τ_comm "Auth" "C_B" "Init" "unit") ((CS_28.replace "Auth" (AV2, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_29 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Init" "unit", ((CS_29.replace "Auth" (AV2, [])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_29 (net_label.τ_comm "Auth" "C_B" "Init" "unit") ((CS_29.replace "Auth" (AV2, [])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_30 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_B" "Init" "unit", ((CS_30.replace "Auth" (AV2, [])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_30 (net_label.τ_comm "Auth" "C_B" "Init" "unit") ((CS_30.replace "Auth" (AV2, [])).replace "C_B" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_31 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_31.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_31 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_31.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_32 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_32.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_32 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_32.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_33 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_33.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_33 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_33.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_34 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_34.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_34 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_34.replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_35 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_35.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_35 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_35.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_36 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_36.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_36 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_36.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_37 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_37.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_37 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_37.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_38 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_38.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_38 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_38.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Term" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_39 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_39.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_39 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_39.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_40 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_40.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_40 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_40.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_41 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_41.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_41 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_41.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_42 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_42.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_42 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_42.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_43 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_43.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_43 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_43.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_44 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_44.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_44 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_44.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_45 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_45.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_45 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_45.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_46 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_46.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_46 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_46.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_47 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_47.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_47 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_47.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_48 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_48.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_48 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_48.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_49 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_49.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_49 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_49.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_50 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_50.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_50 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_50.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_51 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_51.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_51 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_51.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_52 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_52.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_52 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_52.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_53 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_53.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_53 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_53.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_54 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_54.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_54 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_54.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_55 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Acc" "unit", ((CS_55.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_55 (net_label.τ_comm "Auth" "C_C" "Acc" "unit") ((CS_55.replace "Auth" (AT, [])).replace "C_C" (BTEg, [QueueMessage.msg "C_A" "Rqs" "unit", QueueMessage.msg "Auth" "Acc" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_56 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_56.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_56 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_56.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_57 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_57.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_57 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_57.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_58 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_58.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_58 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_58.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_59 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_59.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_59 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_59.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_60 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_60.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_60 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_60.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_61 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_61.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_61 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_61.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_62 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_62.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_62 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_62.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_63 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_63.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_63 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_63.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_64 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_64.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_64 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_64.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_65 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Deny" "unit", ((CS_65.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_65 (net_label.τ_comm "Auth" "C_C" "Deny" "unit") ((CS_65.replace "Auth" (ARec, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Deny" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_66 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_66.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_66 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_66.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_67 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_67.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_67 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_67.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_68 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_68.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_68 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_68.replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_69 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_69.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_69 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_69.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_70 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_70.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_70 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_70.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_71 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_71.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_71 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_71.replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit"])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_72 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_72.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_72 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_72.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_73 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_73.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_73 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_73.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_74 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_74.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_74 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_74.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_75 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Auth" "C_C" "Init" "unit", ((CS_75.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_75 (net_label.τ_comm "Auth" "C_C" "Init" "unit") ((CS_75.replace "Auth" (ARec, [])).replace "C_C" (ClientB, [QueueMessage.msg "Auth" "Init" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_76 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_76.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_76).Nodup) (show net_transb 2 CS_76 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_76.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_77 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_77.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_77).Nodup) (show net_transb 2 CS_77 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_77.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_78 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_78.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_78).Nodup) (show net_transb 2 CS_78 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_78.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_79 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_79.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_79).Nodup) (show net_transb 2 CS_79 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_79.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_80 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_80.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_80).Nodup) (show net_transb 2 CS_80 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_80.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_81 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_81.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_81).Nodup) (show net_transb 2 CS_81 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_81.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_82 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_82.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_82).Nodup) (show net_transb 2 CS_82 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_82.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_83 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_83.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_83).Nodup) (show net_transb 2 CS_83 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_83.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_84 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_84.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_84).Nodup) (show net_transb 2 CS_84 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_84.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_85 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_85.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_85).Nodup) (show net_transb 2 CS_85 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_85.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_86 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_86.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_86).Nodup) (show net_transb 2 CS_86 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_86.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_87 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_87.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_87).Nodup) (show net_transb 2 CS_87 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_87.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_88 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_88.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_88).Nodup) (show net_transb 2 CS_88 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_88.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_89 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_89.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_89).Nodup) (show net_transb 2 CS_89 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_89.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_90 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_90.replace "Auth" (ABS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_90).Nodup) (show net_transb 2 CS_90 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_90.replace "Auth" (ABS, [])) = true from by decide)⟩) hStuck
  · -- CS_91 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_91.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_91).Nodup) (show net_transb 2 CS_91 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_91.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_92 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_92.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_92).Nodup) (show net_transb 2 CS_92 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_92.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_93 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_93.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_93).Nodup) (show net_transb 2 CS_93 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_93.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_94 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_94.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_94).Nodup) (show net_transb 2 CS_94 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_94.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_95 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_95.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_95 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_95.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_96 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_96.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_96).Nodup) (show net_transb 1 CS_96 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_96.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_97 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_97.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_97).Nodup) (show net_transb 1 CS_97 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_97.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_98 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_98.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_98).Nodup) (show net_transb 2 CS_98 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_98.replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_99 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_99.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_99 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_99.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_100 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_100.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_100 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_100.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_101 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_101.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_101 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_101.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_102 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_102.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_102).Nodup) (show net_transb 1 CS_102 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_102.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_103 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_103.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_103).Nodup) (show net_transb 1 CS_103 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_103.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_104 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_104.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_104).Nodup) (show net_transb 1 CS_104 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_104.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_105 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_105.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_105).Nodup) (show net_transb 1 CS_105 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_105.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_106 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_106.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_106).Nodup) (show net_transb 2 CS_106 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_106.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_107 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_107.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_107).Nodup) (show net_transb 2 CS_107 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_107.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_108 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_108.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_108).Nodup) (show net_transb 2 CS_108 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_108.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_109 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_109.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_109).Nodup) (show net_transb 2 CS_109 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_109.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_110 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_110.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_110 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_110.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_111 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_111.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_111).Nodup) (show net_transb 1 CS_111 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_111.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_112 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_112.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_112).Nodup) (show net_transb 1 CS_112 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_112.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_113 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit", (CS_113.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_113).Nodup) (show net_transb 2 CS_113 (net_label.τ_dequeue "Auth" "C_A" "GetAuth" "unit") (CS_113.replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_114 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_114.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_114 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_114.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_115 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_115.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_115 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_115.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_116 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_116.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_116 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_116.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_117 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_117.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_117).Nodup) (show net_transb 1 CS_117 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_117.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_118 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_118.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_118).Nodup) (show net_transb 1 CS_118 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_118.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_119 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_119.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_119).Nodup) (show net_transb 1 CS_119 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_119.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_120 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_120.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_120).Nodup) (show net_transb 1 CS_120 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_120.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_121 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_121.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_121 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_121.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_122 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_122.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_122 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_122.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_123 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_123.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_123 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_123.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_124 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_124.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_124 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_124.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_125 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_125.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_125 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_125.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_126 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_126.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_126 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_126.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_127 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "GetAuth" "unit", ((CS_127.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_127 (net_label.τ_comm "C_A" "Auth" "GetAuth" "unit") ((CS_127.replace "C_A" (VATES, [])).replace "Auth" (ARec, [QueueMessage.msg "C_A" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_128 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_128.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_128).Nodup) (show net_transb 1 CS_128 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_128.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_129 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_129.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_129).Nodup) (show net_transb 1 CS_129 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_129.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_130 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_130.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_130).Nodup) (show net_transb 1 CS_130 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_130.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_131 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Deny" "unit", (CS_131.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_131).Nodup) (show net_transb 1 CS_131 (net_label.τ_dequeue "C_A" "Auth" "Deny" "unit") (CS_131.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_132 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_132.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_132).Nodup) (show net_transb 1 CS_132 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_132.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_133 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_133.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_133).Nodup) (show net_transb 1 CS_133 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_133.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_134 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_134.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_134).Nodup) (show net_transb 1 CS_134 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_134.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_135 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Init" "unit", (CS_135.replace "C_A" (VATRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_135).Nodup) (show net_transb 1 CS_135 (net_label.τ_dequeue "C_A" "Auth" "Init" "unit") (CS_135.replace "C_A" (VATRec, [])) = true from by decide)⟩) hStuck
  · -- CS_136 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_136.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_136).Nodup) (show net_transb 1 CS_136 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_136.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_137 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_137.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_137).Nodup) (show net_transb 1 CS_137 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_137.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_138 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_138.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_138).Nodup) (show net_transb 1 CS_138 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_138.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_139 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_139.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_139).Nodup) (show net_transb 1 CS_139 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_139.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_140 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_140.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_140).Nodup) (show net_transb 1 CS_140 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_140.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_141 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_141.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_141).Nodup) (show net_transb 1 CS_141 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_141.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_142 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_142.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_142).Nodup) (show net_transb 1 CS_142 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_142.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_143 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_143.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_143).Nodup) (show net_transb 1 CS_143 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_143.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_144 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_144.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_144).Nodup) (show net_transb 1 CS_144 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_144.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_145 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_145.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_145).Nodup) (show net_transb 1 CS_145 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_145.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_146 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_146.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_146).Nodup) (show net_transb 1 CS_146 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_146.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_147 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_147.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_147).Nodup) (show net_transb 1 CS_147 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_147.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_148 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_148.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_148).Nodup) (show net_transb 1 CS_148 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_148.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_149 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_149.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_149).Nodup) (show net_transb 1 CS_149 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_149.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_150 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_150.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_150).Nodup) (show net_transb 1 CS_150 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_150.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_151 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_A" "Term" "unit", (CS_151.replace "Auth" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_151).Nodup) (show net_transb 1 CS_151 (net_label.τ_dequeue "Auth" "C_A" "Term" "unit") (CS_151.replace "Auth" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_152 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_152.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_152 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_152.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_153 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_153.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_153 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_153.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_154 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_154.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_154 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_154.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_155 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_155.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_155 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_155.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_156 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_156.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_156 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_156.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_157 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_157.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_157 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_157.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_158 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_158.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_158 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_158.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_159 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_159.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_159 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_159.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_160 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_160.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_160 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_160.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_161 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_161.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_161 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_161.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_162 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_162.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_162 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_162.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_163 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_163.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_163 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_163.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_164 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_164.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_164 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_164.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_165 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_165.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_165 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_165.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_166 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_166.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_166 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_166.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_167 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "Auth" "Term" "unit", ((CS_167.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_167 (net_label.τ_comm "C_A" "Auth" "Term" "unit") ((CS_167.replace "C_A" (SessionType.tEnd, [])).replace "Auth" (AT, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_168 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_B" "Rqs" "unit", ((CS_168.replace "C_A" (VAQRS, [])).replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_168 (net_label.τ_comm "C_A" "C_B" "Rqs" "unit") ((CS_168.replace "C_A" (VAQRS, [])).replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_169 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_B" "Rqs" "unit", ((CS_169.replace "C_A" (VAQRS, [])).replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_169 (net_label.τ_comm "C_A" "C_B" "Rqs" "unit") ((CS_169.replace "C_A" (VAQRS, [])).replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_170 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_B" "Rqs" "unit", ((CS_170.replace "C_A" (VAQRS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_170 (net_label.τ_comm "C_A" "C_B" "Rqs" "unit") ((CS_170.replace "C_A" (VAQRS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_171 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_B" "Rqs" "unit", ((CS_171.replace "C_A" (VAQRS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_171 (net_label.τ_comm "C_A" "C_B" "Rqs" "unit") ((CS_171.replace "C_A" (VAQRS, [])).replace "C_B" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_172 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_172.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_172 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_172.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_173 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_173.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_173 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_173.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_174 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_174.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_174 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_174.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_175 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_175.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_175 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_175.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_176 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_176.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_176 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_176.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_177 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_177.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_177 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_177.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_178 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_178.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_178 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_178.replace "C_A" (VAQCRS, [])).replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_179 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_A" "C_C" "Rqs" "unit", ((CS_179.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_179 (net_label.τ_comm "C_A" "C_C" "Rqs" "unit") ((CS_179.replace "C_A" (VAQCRS, [])).replace "C_C" (BTEg, [QueueMessage.msg "Auth" "Acc" "unit", QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_180 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Acc" "unit", (CS_180.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_180).Nodup) (show net_transb 1 CS_180 (net_label.τ_dequeue "C_A" "Auth" "Acc" "unit") (CS_180.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_181 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Acc" "unit", (CS_181.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_181).Nodup) (show net_transb 1 CS_181 (net_label.τ_dequeue "C_A" "Auth" "Acc" "unit") (CS_181.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_182 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Acc" "unit", (CS_182.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_182).Nodup) (show net_transb 1 CS_182 (net_label.τ_dequeue "C_A" "Auth" "Acc" "unit") (CS_182.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_183 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "Auth" "Acc" "unit", (CS_183.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_183).Nodup) (show net_transb 1 CS_183 (net_label.τ_dequeue "C_A" "Auth" "Acc" "unit") (CS_183.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_184 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_B" "Rsp" "unit", (CS_184.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_184).Nodup) (show net_transb 1 CS_184 (net_label.τ_dequeue "C_A" "C_B" "Rsp" "unit") (CS_184.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_185 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_B" "Rsp" "unit", (CS_185.replace "C_A" (VARB, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_185).Nodup) (show net_transb 1 CS_185 (net_label.τ_dequeue "C_A" "C_B" "Rsp" "unit") (CS_185.replace "C_A" (VARB, [])) = true from by decide)⟩) hStuck
  · -- CS_186 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "C_A" "Rsp" "unit", ((CS_186.replace "C_B" (BRRec, [])).replace "C_A" (VAQRS, [QueueMessage.msg "C_B" "Rsp" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_186 (net_label.τ_comm "C_B" "C_A" "Rsp" "unit") ((CS_186.replace "C_B" (BRRec, [])).replace "C_A" (VAQRS, [QueueMessage.msg "C_B" "Rsp" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_187 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "C_A" "Rsp" "unit", ((CS_187.replace "C_B" (BRRec, [])).replace "C_A" (VAQRS, [QueueMessage.msg "C_B" "Rsp" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_187 (net_label.τ_comm "C_B" "C_A" "Rsp" "unit") ((CS_187.replace "C_B" (BRRec, [])).replace "C_A" (VAQRS, [QueueMessage.msg "C_B" "Rsp" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_188 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Rqs" "unit", (CS_188.replace "C_B" (BRRg, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_188).Nodup) (show net_transb 2 CS_188 (net_label.τ_dequeue "C_B" "C_A" "Rqs" "unit") (CS_188.replace "C_B" (BRRg, [])) = true from by decide)⟩) hStuck
  · -- CS_189 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Rqs" "unit", (CS_189.replace "C_B" (BRRg, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_189).Nodup) (show net_transb 2 CS_189 (net_label.τ_dequeue "C_B" "C_A" "Rqs" "unit") (CS_189.replace "C_B" (BRRg, [])) = true from by decide)⟩) hStuck
  · -- CS_190 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_190.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_190).Nodup) (show net_transb 1 CS_190 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_190.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_191 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_191.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_191).Nodup) (show net_transb 1 CS_191 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_191.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_192 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_192.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_192).Nodup) (show net_transb 1 CS_192 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_192.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_193 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_193.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_193).Nodup) (show net_transb 1 CS_193 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_193.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_194 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit", (CS_194.replace "C_A" (VARC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_194).Nodup) (show net_transb 1 CS_194 (net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit") (CS_194.replace "C_A" (VARC, [])) = true from by decide)⟩) hStuck
  · -- CS_195 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit", (CS_195.replace "C_A" (VARC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_195).Nodup) (show net_transb 1 CS_195 (net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit") (CS_195.replace "C_A" (VARC, [])) = true from by decide)⟩) hStuck
  · -- CS_196 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit", (CS_196.replace "C_A" (VARC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_196).Nodup) (show net_transb 1 CS_196 (net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit") (CS_196.replace "C_A" (VARC, [])) = true from by decide)⟩) hStuck
  · -- CS_197 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit", (CS_197.replace "C_A" (VARC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_197).Nodup) (show net_transb 1 CS_197 (net_label.τ_dequeue "C_A" "C_C" "Rsp" "unit") (CS_197.replace "C_A" (VARC, [])) = true from by decide)⟩) hStuck
  · -- CS_198 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_C" "C_A" "Rsp" "unit", ((CS_198.replace "C_C" (BRRec, [])).replace "C_A" (VAQCRS, [QueueMessage.msg "C_C" "Rsp" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_198 (net_label.τ_comm "C_C" "C_A" "Rsp" "unit") ((CS_198.replace "C_C" (BRRec, [])).replace "C_A" (VAQCRS, [QueueMessage.msg "C_C" "Rsp" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_199 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "C_A" "Rqs" "unit", (CS_199.replace "C_C" (BRRg, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_199).Nodup) (show net_transb 2 CS_199 (net_label.τ_dequeue "C_C" "C_A" "Rqs" "unit") (CS_199.replace "C_C" (BRRg, [])) = true from by decide)⟩) hStuck
  · -- CS_200 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Acc" "unit", (CS_200.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_200).Nodup) (show net_transb 1 CS_200 (net_label.τ_dequeue "C_C" "Auth" "Acc" "unit") (CS_200.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_201 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Acc" "unit", (CS_201.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_201).Nodup) (show net_transb 1 CS_201 (net_label.τ_dequeue "C_C" "Auth" "Acc" "unit") (CS_201.replace "C_C" (BRRec, [QueueMessage.msg "C_A" "Rqs" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_202 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_202.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_202).Nodup) (show net_transb 2 CS_202 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_202.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_203 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_203.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_203).Nodup) (show net_transb 2 CS_203 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_203.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_204 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_204.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_204).Nodup) (show net_transb 2 CS_204 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_204.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_205 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "C_A" "Term" "unit", (CS_205.replace "C_B" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_205).Nodup) (show net_transb 2 CS_205 (net_label.τ_dequeue "C_B" "C_A" "Term" "unit") (CS_205.replace "C_B" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_206 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_206.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_206).Nodup) (show net_transb 1 CS_206 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_206.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_207 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_207.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_207).Nodup) (show net_transb 1 CS_207 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_207.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_208 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_208.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_208).Nodup) (show net_transb 1 CS_208 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_208.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_209 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_209.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_209).Nodup) (show net_transb 1 CS_209 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_209.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_210 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_210.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_210).Nodup) (show net_transb 1 CS_210 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_210.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_211 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_211.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_211).Nodup) (show net_transb 1 CS_211 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_211.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_212 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_212.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_212).Nodup) (show net_transb 1 CS_212 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_212.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_213 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Acc" "unit", (CS_213.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_213).Nodup) (show net_transb 1 CS_213 (net_label.τ_dequeue "C_B" "Auth" "Acc" "unit") (CS_213.replace "C_B" (BRRec, [QueueMessage.msg "C_A" "Term" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_214 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit", (CS_214.replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_214).Nodup) (show net_transb 1 CS_214 (net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit") (CS_214.replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_215 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit", (CS_215.replace "Auth" (ACS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_215).Nodup) (show net_transb 1 CS_215 (net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit") (CS_215.replace "Auth" (ACS, [])) = true from by decide)⟩) hStuck
  · -- CS_216 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit", (CS_216.replace "Auth" (ACS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_216).Nodup) (show net_transb 1 CS_216 (net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit") (CS_216.replace "Auth" (ACS, [])) = true from by decide)⟩) hStuck
  · -- CS_217 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit", (CS_217.replace "Auth" (ACS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_217).Nodup) (show net_transb 1 CS_217 (net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit") (CS_217.replace "Auth" (ACS, [])) = true from by decide)⟩) hStuck
  · -- CS_218 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit", (CS_218.replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_218).Nodup) (show net_transb 1 CS_218 (net_label.τ_dequeue "Auth" "C_B" "GetAuth" "unit") (CS_218.replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_219 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "Auth" "GetAuth" "unit", ((CS_219.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_219 (net_label.τ_comm "C_B" "Auth" "GetAuth" "unit") ((CS_219.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_C" "GetAuth" "unit", QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_220 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Deny" "unit", (CS_220.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_220).Nodup) (show net_transb 1 CS_220 (net_label.τ_dequeue "C_B" "Auth" "Deny" "unit") (CS_220.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_221 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Init" "unit", (CS_221.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_221).Nodup) (show net_transb 1 CS_221 (net_label.τ_dequeue "C_B" "Auth" "Init" "unit") (CS_221.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_222 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "Auth" "GetAuth" "unit", ((CS_222.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_222 (net_label.τ_comm "C_B" "Auth" "GetAuth" "unit") ((CS_222.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_223 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "Auth" "GetAuth" "unit", ((CS_223.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_223 (net_label.τ_comm "C_B" "Auth" "GetAuth" "unit") ((CS_223.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_224 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_B" "Auth" "GetAuth" "unit", ((CS_224.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_224 (net_label.τ_comm "C_B" "Auth" "GetAuth" "unit") ((CS_224.replace "C_B" (BTEg, [])).replace "Auth" (ABS, [QueueMessage.msg "C_B" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_225 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Deny" "unit", (CS_225.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_225).Nodup) (show net_transb 1 CS_225 (net_label.τ_dequeue "C_B" "Auth" "Deny" "unit") (CS_225.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_226 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Deny" "unit", (CS_226.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_226).Nodup) (show net_transb 1 CS_226 (net_label.τ_dequeue "C_B" "Auth" "Deny" "unit") (CS_226.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_227 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Init" "unit", (CS_227.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_227).Nodup) (show net_transb 1 CS_227 (net_label.τ_dequeue "C_B" "Auth" "Init" "unit") (CS_227.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_228 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_B" "Auth" "Init" "unit", (CS_228.replace "C_B" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_228).Nodup) (show net_transb 1 CS_228 (net_label.τ_dequeue "C_B" "Auth" "Init" "unit") (CS_228.replace "C_B" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_229 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Auth" "C_C" "GetAuth" "unit", (CS_229.replace "Auth" (ADS, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_229).Nodup) (show net_transb 1 CS_229 (net_label.τ_dequeue "Auth" "C_C" "GetAuth" "unit") (CS_229.replace "Auth" (ADS, [])) = true from by decide)⟩) hStuck
  · -- CS_230 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "C_C" "Auth" "GetAuth" "unit", ((CS_230.replace "C_C" (BTEg, [])).replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_230 (net_label.τ_comm "C_C" "Auth" "GetAuth" "unit") ((CS_230.replace "C_C" (BTEg, [])).replace "Auth" (ACS, [QueueMessage.msg "C_C" "GetAuth" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_231 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Deny" "unit", (CS_231.replace "C_C" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_231).Nodup) (show net_transb 1 CS_231 (net_label.τ_dequeue "C_C" "Auth" "Deny" "unit") (CS_231.replace "C_C" (BTRec, [])) = true from by decide)⟩) hStuck
  · -- CS_232 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "C_C" "Auth" "Init" "unit", (CS_232.replace "C_C" (BTRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_232).Nodup) (show net_transb 1 CS_232 (net_label.τ_dequeue "C_C" "Auth" "Init" "unit") (CS_232.replace "C_C" (BTRec, [])) = true from by decide)⟩) hStuck

theorem Net_halfDuplex : IsHalfDuplex Net :=
  IsHalfDuplex_of_canon_cover vpnCover vpnHHD

theorem Net_noOrphanStuck (N' : Network) (hStar : net_trans_star Net N')
    (hStuck : IsStuckNetwork N') : NoOrphanMessages N' :=
  noOrphan_of_canon_cover_stuck vpnCover vpnHNO N' hStar hStuck

end Vpn
