import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Invariant.YjsArrayBridgeV2

variable {A : Type}
variable [DecidableEq A]

theorem YjsArrInvariant_integrate_itemSetInvariantV2
    (input : IntegrateInput A) (arr newArr : Array (YjsItem A)) :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.isValid ->
    maximalId newItem arr ->
    integrate input arr = Except.ok newArr ->
    ∃ i ≤ arr.size,
      newArr = arr.insertIdxIfInBounds i newItem ∧
      YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.toList) := by
  intro hArr hToItem hValid hMaxId hIntegrate
  rcases YjsArrInvariant_integrate input arr newArr hArr hToItem hValid hMaxId hIntegrate with
    ⟨ i, hi, hEq, hNewArrInv ⟩
  exact ⟨ i, hi, hEq, hNewArrInv.itemSetInvariantV2 ⟩

theorem YjsArrInvariant_integrateSafe_itemSetInvariantV2
    (input : IntegrateInput A) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.isValid ->
    integrateSafe input arr = Except.ok newArr ->
    ∃ i ≤ arr.size,
      newArr = arr.insertIdxIfInBounds i newItem ∧
      YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.toList) := by
  intro hArr hToItem hValid hIntegrate
  rcases YjsArrInvariant_integrateSafe input newItem arr newArr hArr hToItem hValid hIntegrate with
    ⟨ i, hi, hEq, hNewArrInv ⟩
  exact ⟨ i, hi, hEq, hNewArrInv.itemSetInvariantV2 ⟩

theorem YjsStateInvariant_insert_itemSetInvariantV2
    (arr newArr : YjsState A) (input : IntegrateInput A) :
    YjsStateInvariant arr ->
    input.toItem arr.items = Except.ok newItem ->
    newItem.isValid ->
    arr.insert input = Except.ok newArr ->
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.items.toList) := by
  intro hState hToItem hValid hInsert
  exact (YjsStateInvariant_insert arr newArr input hState hToItem hValid hInsert).itemSetInvariantV2
