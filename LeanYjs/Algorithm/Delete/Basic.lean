import LeanYjs.Item
import LeanYjs.Algorithm.Invariant.Basic
import LeanYjs.Algorithm.Invariant.YjsArray

def deleteById (arr : Array (YjsItem A)) (id : YjsId) : Array (YjsItem A) :=
  -- Mark the item with the given id as deleted
  arr.map (fun item =>
    if item.id = id then
      YjsItem.mk item.origin item.rightOrigin item.id item.content true
    else
      item)

theorem deleteById_mem_iff (arr : Array (YjsItem A)) (id : YjsId) x :
  x ∈ deleteById arr id ↔
    (x.id = id ∧ x.deleted = true ∧ ∃d, {x with deleted := d } ∈ arr) ∨
    (x.id ≠ id ∧ x ∈ arr) := by
  constructor
  . intro hmem
    simp [deleteById] at hmem
    obtain ⟨ a, ha, heq ⟩ := hmem
    split at heq
    . left
      obtain ⟨ _, _, _, _, d ⟩ := a
      simp at *
      subst x; simp
      constructor
      . assumption
      . cases d with
        | true => right; assumption
        | false => left; assumption
    . right
      subst heq
      constructor <;> assumption
  . intros hor
    simp [deleteById]
    cases hor with
    | inl h =>
      obtain ⟨ hid, hdeleted, d, hmem ⟩ := h
      use { origin := x.origin, rightOrigin := x.rightOrigin, id := x.id, content := x.content, deleted := d }
      constructor; assumption
      simp
      subst id; simp
      obtain ⟨ _, _, _, _, _ ⟩ := x
      simp at *
      assumption
    | inr h =>
      obtain ⟨ hid, hx ⟩ := h
      use x
      constructor; assumption
      simp
      intros; contradiction

-- theorem YjsArrInvariant_deleteById (arr : Array (YjsItem A)) (id : YjsId) :
--   YjsArrInvariant arr.toList ->
--   YjsArrInvariant (deleteById arr id).toList := by
--   intro hinv
--   constructor
--   . constructor
--     . simp [ArrSet]
--     . simp [ArrSet]
--     . intros o r cid c d ha
--       simp [ArrSet] at ha
--       rw [deleteById_mem_iff] at ha; simp at ha
--       obtain ⟨ hcid, hd, ha ⟩ := ha
--       cases ha with
--       | inl h =>
--         have h : ArrSet arr.toList <| YjsPtr.itemPtr { origin := o, rightOrigin := r, id := cid, content := c, deleted := false } := by
--           simp [ArrSet]; assumption
--         apply hinv.closed.closedLeft at h
--         rcases o with ⟨ o ⟩ | _ | _ <;> simp [ArrSet] at *
--         rw [deleteById_mem_iff]
--       replace ⟨ a, hmem, ha ⟩ := ha
--       obtain ⟨ ao, ar, aid, ac, ad ⟩ := a; simp at *
--       have ha' := hinv.closed.closedLeft o r id c (a.id = id)
--       split at ha <;> simp [ArrSet] at *
--       rcases o with ⟨ o ⟩ | _ | _ <;> simp at *
--       use { o with deleted := o.id = id }; simp

theorem deleteById_commutative (arr : Array (YjsItem A)) (id1 id2 : YjsId) :
  deleteById (deleteById arr id1) id2 = deleteById (deleteById arr id2) id1 := by
  grind only [deleteById, = Array.size_map, = Array.getElem_map]
