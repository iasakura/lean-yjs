import LeanYjs.ItemSetV2

variable {A : Type}

namespace YjsPtr

def toRefV2 : YjsPtr A -> ItemRef
  | .first => .first
  | .last => .last
  | .itemPtr item => .idRef item.id

@[simp] theorem toRefV2_first :
    YjsPtr.toRefV2 (.first : YjsPtr A) = .first := rfl

@[simp] theorem toRefV2_last :
    YjsPtr.toRefV2 (.last : YjsPtr A) = .last := rfl

@[simp] theorem toRefV2_itemPtr (item : YjsItem A) :
    YjsPtr.toRefV2 (.itemPtr item) = .idRef item.id := rfl

end YjsPtr

namespace YjsItem

def toV2 (item : YjsItem A) : YjsItemV2 A where
  origin := item.origin.toRefV2
  rightOrigin := item.rightOrigin.toRefV2
  id := item.id
  content := item.content

@[simp] theorem toV2_origin (item : YjsItem A) :
    item.toV2.origin = item.origin.toRefV2 := rfl

@[simp] theorem toV2_rightOrigin (item : YjsItem A) :
    item.toV2.rightOrigin = item.rightOrigin.toRefV2 := rfl

@[simp] theorem toV2_id (item : YjsItem A) :
    item.toV2.id = item.id := rfl

@[simp] theorem toV2_content (item : YjsItem A) :
    item.toV2.content = item.content := rfl

@[simp] theorem toV2_toRef (item : YjsItem A) :
    item.toV2.toRef = .idRef item.id := rfl

end YjsItem

namespace ItemSetV2

private def lookupOldItems : List (YjsItem A) -> YjsId -> Option (YjsItemV2 A)
  | [], _ => none
  | item :: items, id =>
      if item.id = id then
        some item.toV2
      else
        lookupOldItems items id

def ofOldItems (items : List (YjsItem A)) : ItemSetV2 A where
  lookup := lookupOldItems items
  lookup_sound := by
    intro id item
    induction items with
    | nil =>
        simp [lookupOldItems]
    | cons head tail ih =>
        simp [lookupOldItems]
        split
        · rename_i hEq
          intro hLookup
          injection hLookup with hItem
          subst hItem
          simpa using hEq
        · rename_i hNe
          exact ih

theorem lookup_eq_some_of_mem_of_pairwise
    {items : List (YjsItem A)} {item : YjsItem A} :
    List.Pairwise (fun x y : YjsItem A => x.id ≠ y.id) items ->
    item ∈ items ->
    (ItemSetV2.ofOldItems items).lookup item.id = some item.toV2 := by
  intro hPair hMem
  induction items with
  | nil =>
      cases hMem
  | cons head tail ih =>
      simp at hMem
      simp [ItemSetV2.ofOldItems, lookupOldItems]
      cases hMem with
      | inl hEq =>
          subst hEq
          simp
      | inr hMemTail =>
          rw [List.pairwise_cons] at hPair
          rcases hPair with ⟨ hHead, hTail ⟩
          have hNe : head.id ≠ item.id := by
            intro hEq
            exact hHead item hMemTail hEq
          simp [hNe]
          exact ih hTail hMemTail

theorem itemIn_toV2_of_mem_of_pairwise
    {items : List (YjsItem A)} {item : YjsItem A} :
    List.Pairwise (fun x y : YjsItem A => x.id ≠ y.id) items ->
    item ∈ items ->
    (ItemSetV2.ofOldItems items).ItemIn item.toV2 := by
  intro hPair hMem
  simpa [ItemSetV2.ItemIn, YjsItem.toV2_id] using
    lookup_eq_some_of_mem_of_pairwise (items := items) (item := item) hPair hMem

theorem refIn_toRef_of_mem_of_pairwise
    {items : List (YjsItem A)} {item : YjsItem A} :
    List.Pairwise (fun x y : YjsItem A => x.id ≠ y.id) items ->
    item ∈ items ->
    (ItemSetV2.ofOldItems items).RefIn item.toV2.toRef := by
  intro hPair hMem
  exact ItemSetV2.refIn_of_itemIn <|
    itemIn_toV2_of_mem_of_pairwise (items := items) (item := item) hPair hMem

end ItemSetV2
