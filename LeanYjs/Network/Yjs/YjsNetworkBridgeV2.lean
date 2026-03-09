import LeanYjs.Network.Yjs.YjsNetwork
import LeanYjs.Algorithm.Insert.SpecBridgeV2

variable {A : Type}
variable [DecidableEq A]

theorem IsValidMessage_insert_itemSetInvariantV2
    (state newState : YjsState A) (input : IntegrateInput A) :
    YjsStateInvariant state ->
    IsValidMessage state.items (YjsOperation.insert input) ->
    state.insert input = Except.ok newState ->
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newState.items.toList) := by
  intro hState hValid hInsert
  simp [IsValidMessage] at hValid
  obtain ⟨ item, hToItem, hItemValid ⟩ := hValid
  exact YjsStateInvariant_insert_itemSetInvariantV2 state newState input hState hToItem hItemValid hInsert
