import LeanYjs.Order.ItemSetInvariantV2

variable {A : Type}

namespace YjsItemSetInvariantV2

private def refSizeOf (size : YjsId -> Nat) : ItemRef -> Nat
  | .first => 0
  | .last => 0
  | .idRef id => size id

private def idSizeOfItem (size : YjsId -> Nat) (item : YjsItemV2 A) : Nat :=
  refSizeOf size item.origin + refSizeOf size item.rightOrigin + 1

noncomputable def idSize {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) : YjsId -> Nat :=
  inv.structural.wfDependsOnId.fix fun current rec =>
    match hLookup : S.lookup current with
    | none => 0
    | some item =>
        idSizeOfItem
          (fun dep =>
            if hOrigin : item.origin = .idRef dep then
              rec dep (by
                have hItem : S.ItemIn item := by
                  simpa [S.lookup_sound hLookup] using hLookup
                have hDep : S.DependsOnId dep item.id :=
                  ItemSetV2.dependsOnId_of_origin (S := S) hItem hOrigin
                simpa [S.lookup_sound hLookup] using hDep)
            else if hRight : item.rightOrigin = .idRef dep then
              rec dep (by
                have hItem : S.ItemIn item := by
                  simpa [S.lookup_sound hLookup] using hLookup
                have hDep : S.DependsOnId dep item.id :=
                  ItemSetV2.dependsOnId_of_rightOrigin (S := S) hItem hRight
                simpa [S.lookup_sound hLookup] using hDep)
            else 0)
          item

noncomputable def refSize {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) : ItemRef -> Nat :=
  refSizeOf inv.idSize

noncomputable def pairSize {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) (x y : ItemRef) : Nat :=
  inv.refSize x + inv.refSize y

noncomputable def tripleSize {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) (x y z : ItemRef) : Nat :=
  inv.refSize x + inv.refSize y + inv.refSize z

@[simp] theorem refSize_first {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    inv.refSize .first = 0 := rfl

@[simp] theorem refSize_last {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    inv.refSize .last = 0 := rfl

@[simp] theorem refSize_toRef {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    (item : YjsItemV2 A) :
    inv.refSize item.toRef = inv.idSize item.id := rfl

theorem idSize_eq_of_itemIn {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.idSize item.id =
      inv.refSize item.origin + inv.refSize item.rightOrigin + 1 := by
  intro hItem
  rw [idSize, WellFounded.fix_eq]
  split
  · simp [ItemSetV2.ItemIn] at hItem
    cases hItem.symm.trans ‹S.lookup item.id = none›
  · rename_i item' hLookup
    have hEq : item' = item := by
      rw [hItem] at hLookup
      simp at hLookup
      exact hLookup.symm
    subst item'
    change idSizeOfItem
        (fun dep =>
          if item.origin = .idRef dep then
            inv.idSize dep
          else if item.rightOrigin = .idRef dep then
            inv.idSize dep
          else
            0)
        item =
      inv.refSize item.origin + inv.refSize item.rightOrigin + 1
    let size : YjsId -> Nat := fun dep =>
      if item.origin = .idRef dep then
        inv.idSize dep
      else if item.rightOrigin = .idRef dep then
        inv.idSize dep
      else
        0
    have hLeft : refSizeOf size item.origin = inv.refSize item.origin := by
      cases hOrigin : item.origin <;> cases hRight : item.rightOrigin <;>
        simp [size, refSize, refSizeOf, hOrigin, hRight]
    have hRight : refSizeOf size item.rightOrigin = inv.refSize item.rightOrigin := by
      cases hOrigin : item.origin <;> cases hRight : item.rightOrigin <;>
        simp [size, refSize, refSizeOf, hOrigin, hRight]
    unfold idSizeOfItem
    rw [hLeft, hRight]

theorem toRef_size_eq {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refSize item.toRef =
      inv.refSize item.origin + inv.refSize item.rightOrigin + 1 := by
  intro hItem
  simpa [refSize] using inv.idSize_eq_of_itemIn hItem

theorem origin_size_lt_toRef_size {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refSize item.origin < inv.refSize item.toRef := by
  intro hItem
  rw [inv.toRef_size_eq hItem]
  omega

theorem rightOrigin_size_lt_toRef_size {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refSize item.rightOrigin < inv.refSize item.toRef := by
  intro hItem
  rw [inv.toRef_size_eq hItem]
  omega

theorem idSize_lt_of_dependsOnId {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {dep current : YjsId} :
    S.DependsOnId dep current ->
    inv.idSize dep < inv.idSize current := by
  intro hDep
  rcases hDep with ⟨ item, hItem, hOrigin | hRight ⟩
  · have hId : item.id = current := S.lookup_sound hItem
    subst hId
    simpa [refSize, hOrigin] using inv.origin_size_lt_toRef_size (item := item) hItem
  · have hId : item.id = current := S.lookup_sound hItem
    subst hId
    simpa [refSize, hRight] using inv.rightOrigin_size_lt_toRef_size (item := item) hItem

theorem refSize_lt_of_step {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y : ItemRef} :
    OriginReachableStepV2 S x y ->
    inv.refSize y < inv.refSize x := by
  intro hStep
  cases hStep with
  | left hItem =>
      rename_i item
      simpa [refSize] using inv.origin_size_lt_toRef_size (item := item) hItem
  | right hItem =>
      rename_i item
      simpa [refSize] using inv.rightOrigin_size_lt_toRef_size (item := item) hItem

theorem refSize_lt_of_reachable {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y : ItemRef} :
    OriginReachableV2 S x y ->
    inv.refSize y < inv.refSize x := by
  intro hReach
  induction hReach with
  | single hStep =>
      exact inv.refSize_lt_of_step hStep
  | tail hStep hReach ih =>
      exact Nat.lt_trans ih (inv.refSize_lt_of_step hStep)

theorem pairSize_lt_of_left_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y z : ItemRef} :
    inv.refSize x < inv.refSize y ->
    inv.pairSize x z < inv.pairSize y z := by
  intro hLt
  exact Nat.add_lt_add_right hLt _

theorem pairSize_lt_of_right_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y z : ItemRef} :
    inv.refSize x < inv.refSize y ->
    inv.pairSize z x < inv.pairSize z y := by
  intro hLt
  exact Nat.add_lt_add_left hLt _

theorem pairSize_lt_of_both_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x1 x2 y1 y2 : ItemRef} :
    inv.refSize x1 < inv.refSize x2 ->
    inv.refSize y1 < inv.refSize y2 ->
    inv.pairSize x1 y1 < inv.pairSize x2 y2 := by
  intro hLeft hRight
  exact Nat.add_lt_add hLeft hRight

theorem tripleSize_lt_of_left_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refSize w < inv.refSize x ->
    inv.tripleSize w y z < inv.tripleSize x y z := by
  intro hLt
  exact Nat.add_lt_add_right (Nat.add_lt_add_right hLt _) _

theorem tripleSize_lt_of_middle_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refSize x < inv.refSize y ->
    inv.tripleSize w x z < inv.tripleSize w y z := by
  intro hLt
  exact Nat.add_lt_add_right (Nat.add_lt_add_left hLt _) _

theorem tripleSize_lt_of_right_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refSize y < inv.refSize z ->
    inv.tripleSize w x y < inv.tripleSize w x z := by
  intro hLt
  exact Nat.add_lt_add_left hLt _

theorem pairSize_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> Prop}
    (step : forall x y,
      (forall x' y', inv.pairSize x' y' < inv.pairSize x y -> motive x' y') ->
      motive x y) :
    forall x y, motive x y := by
  let P : Nat -> Prop := fun n => forall x y, inv.pairSize x y = n -> motive x y
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y hEq
    apply step x y
    intro x' y' hLt
    have hLt' : inv.pairSize x' y' < n := by
      simpa [hEq] using hLt
    exact ih (inv.pairSize x' y') hLt' x' y' rfl
  intro x y
  exact hP (inv.pairSize x y) x y rfl

theorem tripleSize_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> ItemRef -> Prop}
    (step : forall x y z,
      (forall x' y' z', inv.tripleSize x' y' z' < inv.tripleSize x y z -> motive x' y' z') ->
      motive x y z) :
    forall x y z, motive x y z := by
  let P : Nat -> Prop := fun n => forall x y z, inv.tripleSize x y z = n -> motive x y z
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y z hEq
    apply step x y z
    intro x' y' z' hLt
    have hLt' : inv.tripleSize x' y' z' < n := by
      simpa [hEq] using hLt
    exact ih (inv.tripleSize x' y' z') hLt' x' y' z' rfl
  intro x y z
  exact hP (inv.tripleSize x y z) x y z rfl

end YjsItemSetInvariantV2
