import LeanYjs.ItemSetV2

variable {A : Type}

inductive OriginReachableStepV2 (S : ItemSetV2 A) : ItemRef -> ItemRef -> Prop where
  | left {item : YjsItemV2 A} :
      S.ItemIn item ->
      OriginReachableStepV2 S item.toRef item.origin
  | right {item : YjsItemV2 A} :
      S.ItemIn item ->
      OriginReachableStepV2 S item.toRef item.rightOrigin

inductive OriginReachableV2 (S : ItemSetV2 A) : ItemRef -> ItemRef -> Prop where
  | single {x y : ItemRef} :
      OriginReachableStepV2 S x y ->
      OriginReachableV2 S x y
  | tail {x y z : ItemRef} :
      OriginReachableStepV2 S x y ->
      OriginReachableV2 S y z ->
      OriginReachableV2 S x z

namespace OriginReachableV2

theorem of_origin {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item ->
    OriginReachableV2 S item.toRef item.origin := by
  intro hItem
  exact .single (.left hItem)

theorem of_rightOrigin {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item ->
    OriginReachableV2 S item.toRef item.rightOrigin := by
  intro hItem
  exact .single (.right hItem)

theorem target_refIn_of_step {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) :
    ∀ {x y : ItemRef}, OriginReachableStepV2 S x y -> S.RefIn y := by
  intro x y hStep
  cases hStep with
  | left hItem =>
      exact hClosed.closedLeft hItem
  | right hItem =>
      exact hClosed.closedRight hItem

theorem target_refIn {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) :
    ∀ {x y : ItemRef}, OriginReachableV2 S x y -> S.RefIn y := by
  intro x y hReach
  induction hReach with
  | single hStep =>
      exact target_refIn_of_step hClosed hStep
  | tail hStep hReach ih =>
      exact ih

end OriginReachableV2
