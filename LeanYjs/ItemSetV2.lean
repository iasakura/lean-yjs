import LeanYjs.ItemV2

variable {A : Type}

structure ItemSetV2 (A : Type) where
  lookup : YjsId -> Option (YjsItemV2 A)
  lookup_sound : ∀ {id item}, lookup id = some item -> item.id = id

namespace ItemSetV2

def withItem (S : ItemSetV2 A) (item : YjsItemV2 A) : ItemSetV2 A where
  lookup id :=
    if h : id = item.id then
      some item
    else
      S.lookup id
  lookup_sound := by
    intro id item' hLookup
    dsimp at hLookup
    by_cases hEq : id = item.id
    · simp [hEq] at hLookup
      cases hLookup
      exact hEq.symm
    · simp [hEq] at hLookup
      exact S.lookup_sound hLookup

def IdIn (S : ItemSetV2 A) (id : YjsId) : Prop :=
  ∃ item, S.lookup id = some item

def ItemIn (S : ItemSetV2 A) (item : YjsItemV2 A) : Prop :=
  S.lookup item.id = some item

def RefIn (S : ItemSetV2 A) : ItemRef -> Prop
  | .first => True
  | .last => True
  | .idRef id => S.IdIn id

def lookupRef (S : ItemSetV2 A) : ItemRef -> Option (YjsItemV2 A)
  | .first => none
  | .last => none
  | .idRef id => S.lookup id

def DependsOnId (S : ItemSetV2 A) (dep current : YjsId) : Prop :=
  ∃ item, S.lookup current = some item ∧
    (item.origin = .idRef dep ∨ item.rightOrigin = .idRef dep)

def DependsOnItem (dep current : YjsItemV2 A) : Prop :=
  current.origin = dep.toRef ∨ current.rightOrigin = dep.toRef

structure IsClosedItemSetV2 (S : ItemSetV2 A) : Prop where
  closedLeft : ∀ {item}, S.ItemIn item -> S.RefIn item.origin
  closedRight : ∀ {item}, S.ItemIn item -> S.RefIn item.rightOrigin

structure WellFoundedItemSetV2 (S : ItemSetV2 A) : Prop where
  closed : IsClosedItemSetV2 S
  wfDependsOnId : WellFounded S.DependsOnId

@[simp] theorem itemIn_def {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item ↔ S.lookup item.id = some item := Iff.rfl

theorem idIn_of_itemIn {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item -> S.IdIn item.id := by
  intro hItem
  exact ⟨ item, hItem ⟩

theorem itemIn_of_idIn {S : ItemSetV2 A} {id : YjsId} :
    S.IdIn id -> Exists fun item => S.ItemIn item ∧ item.id = id := by
  intro hId
  rcases hId with ⟨ item, hLookup ⟩
  refine ⟨ item, ?_, S.lookup_sound hLookup ⟩
  simpa [S.lookup_sound hLookup] using hLookup

theorem itemIn_of_refIn_idRef {S : ItemSetV2 A} {id : YjsId} :
    S.RefIn (.idRef id) -> Exists fun item => S.ItemIn item ∧ item.id = id := by
  exact itemIn_of_idIn

theorem refIn_of_itemIn {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item -> S.RefIn item.toRef := by
  intro hItem
  exact ⟨ item, hItem ⟩

theorem item_eq_of_itemIn_of_id_eq {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    S.ItemIn x -> S.ItemIn y -> x.id = y.id -> x = y := by
  intro hx hy hId
  have hy' : S.lookup x.id = some y := by
    simpa [hId] using hy
  rw [hx] at hy'
  simp at hy'
  exact hy'

@[simp] theorem lookupRef_first {S : ItemSetV2 A} :
    S.lookupRef .first = none := rfl

@[simp] theorem lookupRef_last {S : ItemSetV2 A} :
    S.lookupRef .last = none := rfl

@[simp] theorem lookupRef_idRef {S : ItemSetV2 A} {id : YjsId} :
    S.lookupRef (.idRef id) = S.lookup id := rfl

@[simp] theorem refIn_first {S : ItemSetV2 A} :
    S.RefIn .first := trivial

@[simp] theorem refIn_last {S : ItemSetV2 A} :
    S.RefIn .last := trivial

theorem refIn_of_lookupRef_eq_some {S : ItemSetV2 A} {ref : ItemRef} {item : YjsItemV2 A} :
    S.lookupRef ref = some item -> S.RefIn ref := by
  intro hLookup
  cases ref with
  | first =>
    simp at hLookup
  | last =>
    simp at hLookup
  | idRef id =>
    exact ⟨ item, hLookup ⟩

theorem dependsOnId_of_origin {S : ItemSetV2 A} {item : YjsItemV2 A} {dep : YjsId} :
    S.ItemIn item ->
    item.origin = .idRef dep ->
    S.DependsOnId dep item.id := by
  intro hItem hOrigin
  exact ⟨ item, hItem, Or.inl hOrigin ⟩

theorem dependsOnId_of_rightOrigin {S : ItemSetV2 A} {item : YjsItemV2 A} {dep : YjsId} :
    S.ItemIn item ->
    item.rightOrigin = .idRef dep ->
    S.DependsOnId dep item.id := by
  intro hItem hRight
  exact ⟨ item, hItem, Or.inr hRight ⟩

theorem WellFoundedItemSetV2.induction
    {S : ItemSetV2 A} (hS : WellFoundedItemSetV2 S)
    {motive : YjsItemV2 A -> Prop}
    (step : ∀ item, S.ItemIn item ->
      (∀ depId depItem,
        S.DependsOnId depId item.id ->
        S.lookup depId = some depItem ->
        motive depItem) ->
      motive item) :
    ∀ item, S.ItemIn item -> motive item := by
  let P : YjsId -> Prop := fun id => ∀ item, S.lookup id = some item -> motive item
  have hP : ∀ id, P id := by
    intro id
    refine hS.wfDependsOnId.induction id ?_
    intro current ih item hLookup
    have hItemId : item.id = current := S.lookup_sound hLookup
    apply step item
    · simpa [hItemId] using hLookup
    · intro depId depItem hDep hDepLookup
      have hPred : P depId := ih depId (by simpa [hItemId] using hDep)
      exact hPred depItem hDepLookup
  intro item hItem
  exact hP item.id item hItem

@[simp] theorem lookup_withItem_self {S : ItemSetV2 A} {item : YjsItemV2 A} :
    (S.withItem item).lookup item.id = some item := by
  simp [withItem]

@[simp] theorem lookup_withItem_of_ne {S : ItemSetV2 A} {item : YjsItemV2 A} {id : YjsId} :
    id ≠ item.id ->
    (S.withItem item).lookup id = S.lookup id := by
  intro hNe
  simp [withItem, hNe]

theorem itemIn_withItem {S : ItemSetV2 A} {item : YjsItemV2 A} :
    (S.withItem item).ItemIn item := by
  simp [ItemIn]

theorem itemIn_withItem_of_itemIn {S : ItemSetV2 A} {item newItem : YjsItemV2 A} :
    item.id ≠ newItem.id ->
    S.ItemIn item ->
    (S.withItem newItem).ItemIn item := by
  intro hNe hItem
  change (S.withItem newItem).lookup item.id = some item
  rw [lookup_withItem_of_ne hNe]
  exact hItem

theorem idIn_withItem_self {S : ItemSetV2 A} {item : YjsItemV2 A} :
    (S.withItem item).IdIn item.id := by
  exact ⟨ item, lookup_withItem_self (S := S) (item := item) ⟩

theorem refIn_withItem_of_refIn {S : ItemSetV2 A} {item : YjsItemV2 A} {ref : ItemRef} :
    S.RefIn ref ->
    (S.withItem item).RefIn ref := by
  intro hRef
  cases ref with
  | first =>
      trivial
  | last =>
      trivial
  | idRef id =>
      rcases hRef with ⟨ found, hFound ⟩
      by_cases hEq : id = item.id
      · subst hEq
        exact idIn_withItem_self (S := S) (item := item)
      · exact ⟨ found, by simpa [withItem, hEq] using hFound ⟩

theorem isClosed_withItem {S : ItemSetV2 A} (hClosed : IsClosedItemSetV2 S)
    {newItem : YjsItemV2 A} :
    S.RefIn newItem.origin ->
    S.RefIn newItem.rightOrigin ->
    IsClosedItemSetV2 (S.withItem newItem) := by
  intro hOrigin hRight
  refine ⟨ ?_, ?_ ⟩
  · intro x hItem
    by_cases hEq : x.id = newItem.id
    · have hx : x = newItem := by
        apply item_eq_of_itemIn_of_id_eq (S := S.withItem newItem) hItem (itemIn_withItem (S := S) (item := newItem)) hEq
      subst x
      exact refIn_withItem_of_refIn (S := S) (item := newItem) hOrigin
    · have hOld : S.ItemIn x := by
        have hLookup : (S.withItem newItem).lookup x.id = S.lookup x.id := by
          exact lookup_withItem_of_ne (S := S) (item := newItem) (id := x.id) hEq
        rw [ItemIn] at hItem ⊢
        rwa [hLookup] at hItem
      exact refIn_withItem_of_refIn (S := S) (item := newItem) (hClosed.closedLeft hOld)
  · intro x hItem
    by_cases hEq : x.id = newItem.id
    · have hx : x = newItem := by
        apply item_eq_of_itemIn_of_id_eq (S := S.withItem newItem) hItem (itemIn_withItem (S := S) (item := newItem)) hEq
      subst x
      exact refIn_withItem_of_refIn (S := S) (item := newItem) hRight
    · have hOld : S.ItemIn x := by
        have hLookup : (S.withItem newItem).lookup x.id = S.lookup x.id := by
          exact lookup_withItem_of_ne (S := S) (item := newItem) (id := x.id) hEq
        rw [ItemIn] at hItem ⊢
        rwa [hLookup] at hItem
      exact refIn_withItem_of_refIn (S := S) (item := newItem) (hClosed.closedRight hOld)

end ItemSetV2
