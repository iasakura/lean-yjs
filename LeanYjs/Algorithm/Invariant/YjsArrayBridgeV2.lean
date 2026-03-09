import LeanYjs.Algorithm.Invariant.StructuralBridgeV2
import LeanYjs.Algorithm.Invariant.YjsArray

variable {A : Type}
variable [DecidableEq A]

omit [DecidableEq A] in theorem YjsArrInvariant.uniqueIdOld {arr : List (YjsItem A)} (hArr : YjsArrInvariant arr) :
    OldToV2.UniqueIdOld arr := by
  simpa [OldToV2.UniqueIdOld, uniqueId] using hArr.unique

theorem YjsArrInvariant.itemSetInvariantV2 {arr : List (YjsItem A)} (hArr : YjsArrInvariant arr) :
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems arr) := by
  exact OldToV2.ofOldItems_invariant_v2 hArr.closed hArr.uniqueIdOld hArr.item_set_inv

theorem YjsStateInvariant.itemSetInvariantV2 {state : YjsState A}
    (hState : YjsStateInvariant state) :
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems state.items.toList) := by
  exact YjsArrInvariant.itemSetInvariantV2 hState

theorem YjsArrInvariant.yjsLeq_or_yjsLtV2 {arr : List (YjsItem A)} (hArr : YjsArrInvariant arr) :
    forall x y,
      (ItemSetV2.ofOldItems arr).RefIn x ->
      (ItemSetV2.ofOldItems arr).RefIn y ->
      YjsLeqV2' (ItemSetV2.ofOldItems arr) x y ∨
      YjsLtV2' (ItemSetV2.ofOldItems arr) y x := by
  exact hArr.itemSetInvariantV2.yjsLeq_or_yjsLt

theorem YjsStateInvariant.yjsLeq_or_yjsLtV2 {state : YjsState A} (hState : YjsStateInvariant state) :
    forall x y,
      (ItemSetV2.ofOldItems state.items.toList).RefIn x ->
      (ItemSetV2.ofOldItems state.items.toList).RefIn y ->
      YjsLeqV2' (ItemSetV2.ofOldItems state.items.toList) x y ∨
      YjsLtV2' (ItemSetV2.ofOldItems state.items.toList) y x := by
  exact hState.itemSetInvariantV2.yjsLeq_or_yjsLt
