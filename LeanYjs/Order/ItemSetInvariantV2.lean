import LeanYjs.Order.ItemOrderV2

variable {A : Type}

structure YjsItemSetInvariantV2 (S : ItemSetV2 A) : Prop where
  structural : ItemSetV2.WellFoundedItemSetV2 S
  origin_lt_rightOrigin :
    forall {item : YjsItemV2 A},
      S.ItemIn item ->
      Exists fun h => YjsLtV2 S h item.origin item.rightOrigin
  origin_nearest_reachable :
    forall {item : YjsItemV2 A} {x : ItemRef},
      S.ItemIn item ->
      OriginReachableV2 S item.toRef x ->
      Or
        (Exists fun h => YjsLeqV2 S h x item.origin)
        (Exists fun h => YjsLeqV2 S h item.rightOrigin x)

namespace YjsItemSetInvariantV2

theorem closed {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ItemSetV2.IsClosedItemSetV2 S :=
  inv.structural.closed

theorem origin_refIn {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) {item : YjsItemV2 A} :
    S.ItemIn item -> S.RefIn item.origin := by
  intro hItem
  exact inv.structural.closed.closedLeft hItem

theorem rightOrigin_refIn {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) {item : YjsItemV2 A} :
    S.ItemIn item -> S.RefIn item.rightOrigin := by
  intro hItem
  exact inv.structural.closed.closedRight hItem

theorem toRef_refIn {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item -> S.RefIn item.toRef := by
  intro hItem
  exact ItemSetV2.refIn_of_itemIn hItem

theorem item_eq_of_id_eq {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    S.ItemIn x -> S.ItemIn y -> x.id = y.id -> x = y := by
  exact ItemSetV2.item_eq_of_itemIn_of_id_eq

theorem reachable_target_refIn {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    forall {x y : ItemRef}, OriginReachableV2 S x y -> S.RefIn y := by
  intro x y hReach
  exact OriginReachableV2.target_refIn inv.structural.closed hReach

theorem induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : YjsItemV2 A -> Prop}
    (step : forall item, S.ItemIn item ->
      (forall depId depItem,
        S.DependsOnId depId item.id ->
        S.lookup depId = some depItem ->
        motive depItem) ->
      motive item) :
    forall item, S.ItemIn item -> motive item := by
  exact ItemSetV2.WellFoundedItemSetV2.induction inv.structural step

end YjsItemSetInvariantV2
