import LeanYjs.Algorithm.Delete.Basic

theorem deleteItemById_deletePtrById_commutative {id1 id2 : YjsId} :
  (∀item : YjsItem A, item.size = n → deleteItemById (deleteItemById item id1) id2 = deleteItemById (deleteItemById item id2) id1) ∧
  (∀ptr : YjsPtr A, ptr.size = n → deletePtrById (deletePtrById ptr id1) id2 = deletePtrById (deletePtrById ptr id2) id1) := by
  apply Nat.strongRec' (p := fun n =>
      (∀item, item.size = n → deleteItemById (deleteItemById item id1) id2 = deleteItemById (deleteItemById item id2) id1) ∧
      (∀ptr, ptr.size = n → deletePtrById (deletePtrById ptr id1) id2 = deletePtrById (deletePtrById ptr id2) id1))
  intros n ih
  constructor
  . intros item hsize
    obtain ⟨ o, r, id, c, d ⟩ := item
    simp [YjsItem.size] at hsize
    simp [deleteItemById]
    by_cases h_id1 : (id = id1)
    . subst id; simp
      by_cases h_id2 : (id1 = id2)
      . subst id1; simp
      . split; contradiction
        simp [deleteItemById]
        have ⟨ _, h_o ⟩ := ih o.size (by omega)
        replace h_o := h_o o rfl
        have ⟨ _, h_r ⟩ := ih r.size (by omega)
        replace h_r := h_r r rfl
        constructor <;> assumption
    . by_cases h_id2 : (id = id2)
      . subst id; simp
        split; contradiction
        simp [deleteItemById]
        have ⟨ _, h_o ⟩ := ih o.size (by omega)
        replace h_o := h_o o rfl
        have ⟨ _, h_r ⟩ := ih r.size (by omega)
        replace h_r := h_r r rfl
        constructor <;> assumption
      . split; contradiction
        simp [deleteItemById]
        split; contradiction
        simp
        have ⟨ _, h_o ⟩ := ih o.size (by omega)
        replace h_o := h_o o rfl
        have ⟨ _, h_r ⟩ := ih r.size (by omega)
        replace h_r := h_r r rfl
        constructor <;> assumption
  . intros p h_size
    cases p with
    | first => simp [deletePtrById]
    | last => simp [deletePtrById]
    | itemPtr item =>
      simp [YjsPtr.size] at h_size
      simp [deletePtrById]
      have ⟨ h_item, _ ⟩ := ih item.size (by omega)
      replace h_item := h_item item rfl
      assumption

theorem deleteItemById_commutative (item : YjsItem A) (id1 id2 : YjsId) :
  deleteItemById (deleteItemById item id1) id2 = deleteItemById (deleteItemById item id2) id1 := by
  have ⟨ h_item, _ ⟩ := deleteItemById_deletePtrById_commutative (A := A) (n := item.size) (id1 := id1) (id2 := id2)
  apply h_item item rfl

theorem deletePtrById_commutative (ptr : YjsPtr A) (id1 id2 : YjsId) :
  deletePtrById (deletePtrById ptr id1) id2 = deletePtrById (deletePtrById ptr id2) id1 := by
  have ⟨ _, h_ptr ⟩ := deleteItemById_deletePtrById_commutative (A := A) (n := ptr.size) (id1 := id1) (id2 := id2)
  apply h_ptr ptr rfl

theorem deleteItemById_id (item : YjsItem A) (id : YjsId) :
  (deleteItemById item id).id = item.id := by
  obtain ⟨ o, r, iid, c, d ⟩ := item
  simp [deleteItemById]
  grind only

theorem deleteById_commutative (arr : Array (YjsItem A)) (id1 id2 : YjsId) :
  deleteById (deleteById arr id1) id2 = deleteById (deleteById arr id2) id1 := by
  apply Array.ext
  . simp [deleteById]
  . intro i hi₁ hi₂
    simp [deleteById] at hi₁ hi₂
    simp [deleteById]
    apply deleteItemById_commutative
