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

theorem IsValidMessage_insert_itemValidV2Against
    (state : YjsState A) (input : IntegrateInput A) :
    YjsStateInvariant state ->
    IsValidMessage state.items (YjsOperation.insert input) ->
    ∃ item,
      input.toItem state.items = Except.ok item ∧
      IsItemValidV2Against (ItemSetV2.ofOldItems state.items.toList) item := by
  intro hState hValid
  simp [IsValidMessage] at hValid
  obtain ⟨ item, hToItem, hItemValid ⟩ := hValid
  exact ⟨ item, hToItem, YjsItem.isValid_toV2AgainstOldItems hState hToItem hItemValid ⟩

theorem effect_list_itemSetInvariantV2 {hb : CausalOrder (YjsOperation A)}
    (StateSource : YjsOperation A → Prop)
    (h_valid_mono : IsValidStateMonotone (A := YjsOperation A) (S := YjsId) (hb := hb) StateSource)
    {ops : List (YjsOperation A)} {s : YjsState A} :
    (∀ op, op ∈ ops → StateSource op) ->
    hb_consistent hb ops ->
    hbClosed hb ops ->
    IdNoDup ops ->
    effect_list ops Operation.init = Except.ok s ->
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems s.items.toList) := by
  intro hSource hConsistent hClosed hNoDup hEffect
  have hStateInv : YjsStateInvariant s := by
    simpa [Operation.StateInv] using
      (effect_list_stateInv (A := YjsOperation A) (S := YjsId) (hb := hb)
        (StateSource := StateSource) h_valid_mono hSource hConsistent hClosed hNoDup hEffect)
  exact hStateInv.itemSetInvariantV2
