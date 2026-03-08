import LeanYjs.ItemV2

variable {A : Type}

structure ItemSetV2 (A : Type) where
  lookup : YjsId -> Option (YjsItemV2 A)
  lookup_sound : ∀ {id item}, lookup id = some item -> item.id = id

namespace ItemSetV2

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

end ItemSetV2
