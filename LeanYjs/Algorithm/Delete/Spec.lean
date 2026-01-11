import LeanYjs.Algorithm.Delete.Basic

private theorem deleteItem_deletePtr_idempotent n (id : YjsId) :
  (∀item : YjsItem A, item.size = n → deleteItemById (deleteItemById item id) id = deleteItemById item id) ∧
  (∀ptr : YjsPtr A, ptr.size = n → deletePtrById (deletePtrById ptr id) id = deletePtrById ptr id) := by
  apply Nat.strongRec' (p := fun n =>
      (∀item, item.size = n → deleteItemById (deleteItemById item id) id = deleteItemById  item id) ∧
      (∀ptr, ptr.size = n → deletePtrById (deletePtrById ptr id) id = deletePtrById ptr id))
  intros n ih

  constructor
  . intros item hsize
    obtain ⟨ o, r, id, c, d ⟩ := item
    simp [YjsItem.size] at hsize
    have ⟨ _, h_o ⟩ := ih o.size (by omega)
    replace h_o := h_o o rfl
    have ⟨ _, h_r ⟩ := ih r.size (by omega)
    replace h_r := h_r r rfl
    simp [deleteItemById]
    split
    . simp [deleteItemById]
      constructor <;> assumption
    . simp [deleteItemById]
      split; contradiction
      simp; constructor <;> assumption
  . intros ptr hsize
    cases ptr with
    | itemPtr item =>
      simp [YjsPtr.size] at hsize
      have ⟨ h_item, _ ⟩ := ih item.size (by omega)
      replace h_item := h_item item rfl
      simp [deletePtrById]
      assumption
    | first =>
      simp [deletePtrById]
    | last =>
      simp [deletePtrById]

theorem deleteItem_idempotent (item : YjsItem A) (id : YjsId) :
  deleteItemById (deleteItemById item id) id = deleteItemById item id := by
  have ⟨ h_item, _ ⟩ := deleteItem_deletePtr_idempotent (A := A) item.size id
  apply h_item item rfl

theorem deletePtr_idempotent (ptr : YjsPtr A) (id : YjsId) :
  deletePtrById (deletePtrById ptr id) id = deletePtrById ptr id := by
  have ⟨ _, h_ptr ⟩ := deleteItem_deletePtr_idempotent (A := A) ptr.size id
  apply h_ptr ptr rfl

theorem IsClosedItemSet_deleteById {A} (arr : Array (YjsItem A)) (id : YjsId) :
  IsClosedItemSet (ArrSet arr.toList) → IsClosedItemSet (ArrSet (deleteById arr id).toList) := by
  intros hclosed
  constructor
  . simp [ArrSet]
  . simp [ArrSet]
  . intros o r cid c d ha
    rcases o with  ⟨ o ⟩ | _ | _ <;> simp [ArrSet]
    simp [ArrSet] at ha
    simp [deleteById] at ha |-
    obtain ⟨ a, hmem, ha ⟩ := ha
    obtain ⟨ ao, ar, aid, ac, ad ⟩ := a
    simp [deleteItemById] at ha
    split at ha
    . simp at ha
      obtain ⟨ h_ao_o ⟩ := ha
      have h := hclosed.closedLeft ao ar aid ac ad (by simp [ArrSet]; assumption)
      rcases ao with ⟨ ao ⟩ | _ | _ <;> simp [deletePtrById] at h_ao_o
      simp [ArrSet] at h
      use ao
    . simp at ha
      obtain ⟨ h_ao_o ⟩ := ha
      have h := hclosed.closedLeft ao ar aid ac ad (by simp [ArrSet]; assumption)
      rcases ao with ⟨ ao ⟩ | _ | _ <;> simp [deletePtrById] at h_ao_o
      simp [ArrSet] at h
      use ao
  . intros o r cid c d ha
    rcases r with  ⟨ r ⟩ | _ | _ <;> simp [ArrSet]
    simp [ArrSet] at ha
    simp [deleteById] at ha |-
    obtain ⟨ a, hmem, ha ⟩ := ha
    obtain ⟨ ao, ar, aid, ac, ad ⟩ := a
    simp [deleteItemById] at ha
    split at ha
    . simp at ha
      obtain ⟨ _, h_ar_r, _ ⟩ := ha
      have h := hclosed.closedRight ao ar aid ac ad (by simp [ArrSet]; assumption)
      rcases ar with ⟨ ar ⟩ | _ | _ <;> simp [deletePtrById] at h_ar_r
      simp [ArrSet] at h
      use ar
    . simp at ha
      obtain ⟨ _, h_ar_r, _ ⟩ := ha
      have h := hclosed.closedRight ao ar aid ac ad (by simp [ArrSet]; assumption)
      rcases ar with ⟨ ar ⟩ | _ | _ <;> simp [deletePtrById] at h_ar_r
      simp [ArrSet] at h
      use ar

theorem deletePtrById_deleteItemById_YjsLt {A} (x y : YjsPtr A) (id : YjsId) :
  (YjsLt h x y → YjsLt h (deletePtrById x id) (deletePtrById y id)) ∧
  (YjsLeq h x y → YjsLeq h (deletePtrById x id) (deletePtrById y id)) ∧
  (ConflictLt h x y → ConflictLt h (deletePtrById x id) (deletePtrById y id)) := by
  apply Nat.strongRec' (p := fun h => ∀ (x y : YjsPtr A),
    (YjsLt h x y → YjsLt h (deletePtrById x id) (deletePtrById y id)) ∧
    (YjsLeq h x y → YjsLeq h (deletePtrById x id) (deletePtrById y id)) ∧
    (ConflictLt h x y → ConflictLt h (deletePtrById x id) (deletePtrById y id)))
  intros n ih x y
  constructor
  . intro hlt
    cases hlt with
    | ltOriginOrder o _ hlt =>
      apply YjsLt.ltOriginOrder
      cases hlt with
      | lt_first =>
        apply OriginLt.lt_first
      | lt_last =>
        apply OriginLt.lt_last
      | lt_first_last =>
        apply OriginLt.lt_first_last
    | ltConflict h =>
      apply YjsLt.ltConflict
      grind only
    | ltOrigin h =>
      simp [deletePtrById, deleteItemById]
      split <;> apply YjsLt.ltOrigin <;> grind only
    | ltRightOrigin h =>
      simp [deletePtrById, deleteItemById]
      split <;> apply YjsLt.ltRightOrigin <;> grind only
  constructor
  . intros hleq
    cases hleq with
    | leqSame =>
      apply YjsLeq.leqSame
    | leqLt hlt =>
      apply YjsLeq.leqLt
      grind only
  . intro hconflict
    cases hconflict with
    | ltOriginDiff h1 h2 h3 h4 l1 l2 l3 l4 id1 id2 c1 c2 d1 d2 =>
      simp [deletePtrById, deleteItemById]
      have ⟨ h_lt1, _ ⟩ := ih h1 (by simp [max4]; omega) l2 l1
      replace h_lt1 := h_lt1 (by assumption)
      have ⟨ h_lt2, _ ⟩ := ih h2 (by simp [max4]; omega) (YjsPtr.itemPtr { origin := l1, rightOrigin := l3, id := id1, content := c1, deleted := d1 }) l4
      replace h_lt2 := h_lt2 (by assumption)
      have ⟨ h_lt3, _ ⟩ := ih h3 (by simp [max4]; omega) l1 (YjsPtr.itemPtr { origin := l2, rightOrigin := l4, id := id2, content := c2, deleted := d2 })
      replace h_lt3 := h_lt3 (by assumption)
      have ⟨ h_lt4, _ ⟩ := ih h4 (by simp [max4]; omega) (YjsPtr.itemPtr { origin := l2, rightOrigin := l4, id := id2, content := c2, deleted := d2 }) l3
      replace h_lt4 := h_lt4 (by assumption)
      simp [deletePtrById, deleteItemById] at h_lt1 h_lt2 h_lt3 h_lt4
      grind only [ConflictLt.ltOriginDiff]
    | ltOriginSame h1 h2 l1 r1 r2 id1 id2 c1 c2 d1 d2 =>
      simp [deletePtrById, deleteItemById]
      have ⟨ h_lt1, _ ⟩ := ih h1 (by omega) (YjsPtr.itemPtr { origin := l1, rightOrigin := r1, id := id1, content := c1, deleted := d1 }) r2
      replace h_lt1 := h_lt1 (by assumption)
      have ⟨ h_lt2, _ ⟩ := ih h2 (by omega) (YjsPtr.itemPtr { origin := l1, rightOrigin := r2, id := id2, content := c2,  deleted := d2 }) r1
      replace h_lt2 := h_lt2 (by assumption)
      simp [deletePtrById, deleteItemById] at h_lt1 h_lt2
      grind only [ConflictLt.ltOriginSame]

theorem deletePtrById_YjsLt' (x y : YjsPtr A) (id : YjsId) :
  YjsLt' x y → YjsLt' (deletePtrById x id) (deletePtrById y id) := by
  intro hlt
  obtain ⟨ h, hlt ⟩ := hlt
  have ⟨ hlt, _ , _ ⟩ := deletePtrById_deleteItemById_YjsLt (h := h) x y id
  constructor; apply hlt; assumption

theorem deletePtrById_YjsLeq' (x y : YjsPtr A) (id : YjsId) :
  YjsLeq' x y → YjsLeq' (deletePtrById x id) (deletePtrById y id) := by
  intro hlt
  obtain ⟨ h, hlt ⟩ := hlt
  have ⟨ _, hleq , _ ⟩ := deletePtrById_deleteItemById_YjsLt (h := h) x y id
  constructor; apply hleq; assumption

theorem deletePtrById_OriginReachableStep {A} {x y : YjsPtr A} {id : YjsId} :
  OriginReachableStep (A := A) (deletePtrById x id) y → ∃z, OriginReachableStep (A := A) x z ∧ deletePtrById z id = y := by
  intros hstep
  generalize h_x'_def : deletePtrById x id = x' at hstep
  cases hstep with
  | reachable o r iid c d =>
    rcases x with ⟨ x ⟩ | _ | _ <;> simp [deletePtrById] at h_x'_def
    obtain ⟨ o, r, id', c, d ⟩ := x
    simp [deleteItemById] at h_x'_def
    grind only [OriginReachableStep.reachable]
  | reachable_right o r iid c d =>
    rcases x with ⟨ x ⟩ | _ | _ <;> simp [deletePtrById] at h_x'_def
    obtain ⟨ o, r, id', c, d ⟩ := x
    simp [deleteItemById] at h_x'_def
    grind only [OriginReachableStep.reachable_right]

theorem deletePtrById_OriginReachable {A} (x y : YjsPtr A) (id : YjsId) :
  OriginReachable (A := A) (deletePtrById x id) y → ∃z, OriginReachable (A := A) x z ∧ deletePtrById z id = y := by
  intros hreachable
  generalize h_x'_def : deletePtrById x id = x' at hreachable
  induction hreachable generalizing x with
  | reachable_single _ _ h_step =>
    rw [<-h_x'_def] at h_step
    have ⟨ z, h_step_orig, h_z_def ⟩ := deletePtrById_OriginReachableStep h_step
    grind only [OriginReachable.reachable_single]
  | reachable_head x y z h_step h ih =>
    rw [<-h_x'_def] at h_step
    have ⟨ y_orig, h_step_orig, h_y_def ⟩ := deletePtrById_OriginReachableStep h_step
    have ⟨ z_orig, h_reach_orig, h_z_def ⟩ := ih _ h_y_def
    grind only [OriginReachable.reachable_head]

theorem deleteItemById_id_eq {A} (item : YjsItem A) (id : YjsId) :
  (deleteItemById item id).id = item.id := by
  obtain ⟨ o, r, iid, c, d ⟩ := item
  simp [deleteItemById]
  grind only

theorem ItemSetInvariant_deleteById {A} (arr : Array (YjsItem A)) (id : YjsId) :
  ItemSetInvariant (ArrSet arr.toList) →
  ItemSetInvariant (ArrSet (deleteById arr id).toList) := by
  intros hinv
  constructor
  . intros o r cid c d hmem
    simp [ArrSet] at hmem
    simp [deleteById] at hmem
    obtain ⟨ a, hmem, ha ⟩ := hmem
    obtain ⟨ ao, ar, aid, ac, ad ⟩ := a
    simp [deleteItemById] at ha
    split at ha
    . simp at ha
      obtain ⟨ h_ao_o, h_ar_r, _ ⟩ := ha
      subst o r
      apply deletePtrById_YjsLt'
      apply hinv.origin_not_leq _ _ _ _ _ (by simp [ArrSet]; apply hmem)
    . simp at ha
      obtain ⟨ h_ao_o, h_ar_r, _ ⟩ := ha
      subst o r
      apply deletePtrById_YjsLt'
      apply hinv.origin_not_leq _ _ _ _ _ (by simp [ArrSet]; apply hmem)
  . intros o r c id' d x hmem hreachable
    simp [ArrSet, deleteById] at hmem
    obtain ⟨ a, hmem, ha ⟩ := hmem
    rw [<-ha] at hreachable
    apply deletePtrById_OriginReachable (YjsPtr.itemPtr a) at hreachable
    obtain ⟨ x_orig, h_reach_orig, h_x_def ⟩ := hreachable
    obtain ⟨ ao, ar, aid, ac, ad ⟩ := a
    apply hinv.origin_nearest_reachable _ _ _ _ _ _ (by simp [ArrSet]; assumption) at h_reach_orig
    simp [deleteItemById] at ha
    by_cases hid : (aid = id)
    . subst aid; simp at ha
      grind [deletePtrById_YjsLeq']
    . split at ha; contradiction
      simp at ha
      grind [deletePtrById_YjsLeq']
  . intros x y h_id_eq h_mem_x h_mem_y
    simp [ArrSet, deleteById] at h_mem_x h_mem_y
    obtain ⟨ a_x, h_mem_x, ha_x ⟩ := h_mem_x
    obtain ⟨ a_y, h_mem_y, ha_y ⟩ := h_mem_y
    have h_id_eq : a_x.id = a_y.id := by
      rw [<-ha_x, <-ha_y] at h_id_eq
      rw [deleteItemById_id_eq] at h_id_eq
      rw [deleteItemById_id_eq] at h_id_eq
      assumption
    have a_eq : a_x = a_y := by
      apply hinv.id_unique _ _ h_id_eq (by simp [ArrSet]; assumption) (by simp [ArrSet]; assumption)
    grind only

theorem YjsArrInvariant_deleteById (arr : Array (YjsItem A)) (id : YjsId) :
  YjsArrInvariant arr.toList ->
  YjsArrInvariant (deleteById arr id).toList := by
  intro hinv
  constructor
  . apply IsClosedItemSet_deleteById _ _ hinv.closed
  . apply ItemSetInvariant_deleteById _ _ hinv.item_set_inv
  . have h := hinv.sorted
    rw [List.pairwise_iff_getElem] at *
    intros i j hi hj hij
    simp [deleteById] at hi hj
    simp [deleteById]
    apply deletePtrById_YjsLt' (x := YjsPtr.itemPtr arr[i]) (y := YjsPtr.itemPtr arr[j]) id
    grind
  . have h := hinv.unique
    simp [uniqueId] at *
    rw [List.pairwise_iff_getElem] at *
    intros i j hi hj hij
    simp [deleteById]
    rw [deleteItemById_id_eq]
    rw [deleteItemById_id_eq]
    simp at h
    apply h; assumption
