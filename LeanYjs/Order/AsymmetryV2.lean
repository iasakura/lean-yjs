import LeanYjs.Order.TotalityV2

variable {A : Type}

theorem YjsId_lt_asymm {id1 id2 : YjsId} :
    id1 < id2 -> Not (id2 < id1) := by
  intro hLt hLt'
  obtain ⟨ clientId1, clock1 ⟩ := id1
  obtain ⟨ clientId2, clock2 ⟩ := id2
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hLt
  · split at hLt'
    · omega
    · omega
  · split at hLt'
    · omega
    · omega

namespace YjsLtV2'

theorem not_first_first {S : ItemSetV2 A} :
    Not (YjsLtV2' S .first .first) := by
  intro hLt
  rcases yjsLtV2'_cases S .first .first hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · rcases hFirst with ⟨ _, hLast | ⟨ _, hEq, _ ⟩ ⟩
    · cases hLast
    · cases hEq
  · cases hLast.1
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

theorem not_last_last {S : ItemSetV2 A} :
    Not (YjsLtV2' S .last .last) := by
  intro hLt
  rcases yjsLtV2'_cases S .last .last hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · cases hFirst.1
  · rcases hLast with ⟨ _, hFirst | ⟨ _, hEq, _ ⟩ ⟩
    · cases hFirst
    · cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

theorem not_last_first {S : ItemSetV2 A} :
    Not (YjsLtV2' S .last .first) := by
  intro hLt
  rcases yjsLtV2'_cases S .last .first hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · cases hFirst.1
  · cases hLast.1
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

end YjsLtV2'
