import LeanYjs.Order.ItemSetInvariantV2

variable {A : Type}

namespace YjsItemSetInvariantV2

private def refDepthOf (depth : YjsId -> Nat) : ItemRef -> Nat
  | .first => 0
  | .last => 0
  | .idRef id => depth id

private def idDepthOfItem (depth : YjsId -> Nat) (item : YjsItemV2 A) : Nat :=
  Nat.max (refDepthOf depth item.origin) (refDepthOf depth item.rightOrigin) + 1

noncomputable def idDepth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) : YjsId -> Nat :=
  inv.structural.wfDependsOnId.fix fun current rec =>
    match hLookup : S.lookup current with
    | none => 0
    | some item =>
        idDepthOfItem
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

noncomputable def refDepth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) : ItemRef -> Nat
  := refDepthOf inv.idDepth

noncomputable def pairDepth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) (x y : ItemRef) : Nat :=
  inv.refDepth x + inv.refDepth y

noncomputable def tripleDepth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) (x y z : ItemRef) : Nat :=
  inv.refDepth x + inv.refDepth y + inv.refDepth z

@[simp] theorem refDepth_first {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    inv.refDepth .first = 0 := rfl

@[simp] theorem refDepth_last {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    inv.refDepth .last = 0 := rfl

@[simp] theorem refDepth_toRef {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    (item : YjsItemV2 A) :
    inv.refDepth item.toRef = inv.idDepth item.id := rfl

theorem idDepth_eq_of_itemIn {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.idDepth item.id =
      Nat.max (inv.refDepth item.origin) (inv.refDepth item.rightOrigin) + 1 := by
  intro hItem
  rw [idDepth, WellFounded.fix_eq]
  split
  · simp [ItemSetV2.ItemIn] at hItem
    cases hItem.symm.trans ‹S.lookup item.id = none›
  · rename_i item' hLookup
    have hEq : item' = item := by
      rw [hItem] at hLookup
      simp at hLookup
      exact hLookup.symm
    subst item'
    let depth : YjsId -> Nat := fun dep =>
      if item.origin = .idRef dep then
        inv.idDepth dep
      else if item.rightOrigin = .idRef dep then
        inv.idDepth dep
      else
        0
    have hLeft : refDepthOf depth item.origin = inv.refDepth item.origin := by
      cases hOrigin : item.origin <;> cases hRight : item.rightOrigin <;>
        simp [depth, refDepth, refDepthOf, hOrigin, hRight]
    have hRight : refDepthOf depth item.rightOrigin = inv.refDepth item.rightOrigin := by
      cases hOrigin : item.origin <;> cases hRight : item.rightOrigin <;>
        simp [depth, refDepth, refDepthOf, hOrigin, hRight]
    unfold idDepthOfItem
    have hMax :
        Nat.max (refDepthOf depth item.origin) (refDepthOf depth item.rightOrigin) =
          Nat.max (inv.refDepth item.origin) (inv.refDepth item.rightOrigin) := by
      rw [hLeft, hRight]
    exact congrArg (fun n => n + 1) hMax

theorem toRef_depth_eq {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refDepth item.toRef =
      Nat.max (inv.refDepth item.origin) (inv.refDepth item.rightOrigin) + 1 := by
  intro hItem
  simpa [refDepth] using inv.idDepth_eq_of_itemIn hItem

theorem origin_depth_lt_toRef_depth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refDepth item.origin < inv.refDepth item.toRef := by
  intro hItem
  rw [inv.toRef_depth_eq hItem]
  exact Nat.lt_succ_of_le (Nat.le_max_left _ _)

theorem rightOrigin_depth_lt_toRef_depth {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {item : YjsItemV2 A} :
    S.ItemIn item ->
    inv.refDepth item.rightOrigin < inv.refDepth item.toRef := by
  intro hItem
  rw [inv.toRef_depth_eq hItem]
  exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

theorem idDepth_lt_of_dependsOnId {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {dep current : YjsId} :
    S.DependsOnId dep current ->
    inv.idDepth dep < inv.idDepth current := by
  intro hDep
  rcases hDep with ⟨ item, hItem, hOrigin | hRight ⟩
  · have hId : item.id = current := S.lookup_sound hItem
    subst hId
    simpa [refDepth, hOrigin] using inv.origin_depth_lt_toRef_depth (item := item) hItem
  · have hId : item.id = current := S.lookup_sound hItem
    subst hId
    simpa [refDepth, hRight] using inv.rightOrigin_depth_lt_toRef_depth (item := item) hItem

theorem refDepth_lt_of_step {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y : ItemRef} :
    OriginReachableStepV2 S x y ->
    inv.refDepth y < inv.refDepth x := by
  intro hStep
  cases hStep with
  | left hItem =>
      rename_i item
      simpa [refDepth] using inv.origin_depth_lt_toRef_depth (item := item) hItem
  | right hItem =>
      rename_i item
      simpa [refDepth] using inv.rightOrigin_depth_lt_toRef_depth (item := item) hItem

theorem refDepth_lt_of_reachable {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y : ItemRef} :
    OriginReachableV2 S x y ->
    inv.refDepth y < inv.refDepth x := by
  intro hReach
  induction hReach with
  | single hStep =>
      exact inv.refDepth_lt_of_step hStep
  | tail hStep hReach ih =>
      exact Nat.lt_trans ih (inv.refDepth_lt_of_step hStep)

theorem pairDepth_lt_of_left_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y z : ItemRef} :
    inv.refDepth x < inv.refDepth y ->
    inv.pairDepth x z < inv.pairDepth y z := by
  intro hLt
  exact Nat.add_lt_add_right hLt _

theorem pairDepth_lt_of_right_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y z : ItemRef} :
    inv.refDepth x < inv.refDepth y ->
    inv.pairDepth z x < inv.pairDepth z y := by
  intro hLt
  exact Nat.add_lt_add_left hLt _

theorem tripleDepth_lt_of_left_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refDepth w < inv.refDepth x ->
    inv.tripleDepth w y z < inv.tripleDepth x y z := by
  intro hLt
  exact Nat.add_lt_add_right (Nat.add_lt_add_right hLt _) _

theorem tripleDepth_lt_of_middle_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refDepth x < inv.refDepth y ->
    inv.tripleDepth w x z < inv.tripleDepth w y z := by
  intro hLt
  exact Nat.add_lt_add_right (Nat.add_lt_add_left hLt _) _

theorem tripleDepth_lt_of_right_lt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {w x y z : ItemRef} :
    inv.refDepth y < inv.refDepth z ->
    inv.tripleDepth w x y < inv.tripleDepth w x z := by
  intro hLt
  exact Nat.add_lt_add_left hLt _

end YjsItemSetInvariantV2
