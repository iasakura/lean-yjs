import LeanYjs.Algorithm.Delete.Basic

theorem deleteItemById_deletePtrById_commutative {id1 id2 : YjsId} :
  (∀item : YjsItem A, item.size = n → deleteItemById (deleteItemById item id1) id2 = deleteItemById (deleteItemById item id2) id1) ∧
  (∀ptr : YjsPtr A, ptr.size = n → deletePtrById (deletePtrById ptr id1) id2 = deletePtrById (deletePtrById ptr id2) id1) := by
  constructor
  · intro item _hsize
    simp [deleteItemById]
  · intro ptr _hsize
    simp [deletePtrById]

theorem deleteItemById_commutative (item : YjsItem A) (id1 id2 : YjsId) :
  deleteItemById (deleteItemById item id1) id2 = deleteItemById (deleteItemById item id2) id1 := by
  simp [deleteItemById]

theorem deletePtrById_commutative (ptr : YjsPtr A) (id1 id2 : YjsId) :
  deletePtrById (deletePtrById ptr id1) id2 = deletePtrById (deletePtrById ptr id2) id1 := by
  simp [deletePtrById]

theorem deleteItemById_id (item : YjsItem A) (id : YjsId) :
  (deleteItemById item id).id = item.id := by
  simp [deleteItemById]

theorem deleteById_commutative (state : YjsState A) (id1 id2 : YjsId) :
  deleteById (deleteById state id1) id2 = deleteById (deleteById state id2) id1 := by
  cases state with
  | mk items deletedIds =>
    haveI : Std.LawfulEqOrd ClientId := inferInstanceAs (Std.LawfulEqOrd Nat)
    haveI : Std.LawfulEqCmp YjsIdCmp := {
      eq_of_compare := by
        intro a b h
        cases a with
        | mk aClient aClock =>
          cases b with
          | mk bClient bClock =>
            simp [YjsIdCmp, compareLex_eq_eq, compareOn] at h
            rcases h with ⟨hClient, hClock⟩
            subst hClient
            subst hClock
            rfl
    }
    simp [deleteById, deleteItemById_commutative, Array.map_map]
    apply Std.ExtTreeSet.ext_mem
    intro k
    simp [Std.ExtTreeSet.mem_insert, or_left_comm, or_assoc]
