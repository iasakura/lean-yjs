import LeanYjs.Indirect.Algorithm.Equivalence
import LeanYjs.Network.Yjs.YjsNetwork

namespace Indirect

open NetworkModels

variable {A : Type} [DecidableEq A]

def effect (op : _root_.YjsOperation A) (state : YjsState A) :
    Except IntegrateError (YjsState A) :=
  match op with
  | _root_.YjsOperation.insert input =>
      YjsState.insert state input
  | _root_.YjsOperation.delete _ deletedId =>
      Except.ok (deleteById state deletedId)

def interpOps (ops : List (_root_.YjsOperation A)) (init : YjsState A) :
    Except IntegrateError (YjsState A) :=
  ops.foldlM (fun state op => effect op state) init

omit [DecidableEq A] in
theorem empty_stateEquivalent :
    StateEquivalent (_root_.YjsEmptyArray (A := A)) YjsEmptyState := by
  simp [StateEquivalent, _root_.YjsEmptyArray, YjsEmptyState, YjsState.empty, ofDirectState]

theorem effect_ofDirectState (op : _root_.YjsOperation A) (state : _root_.YjsState A)
    (h_inv : _root_.YjsStateInvariant state) :
    effect op (ofDirectState state) =
      Except.map ofDirectState (_root_.Operation.effect op state) := by
  cases op with
  | insert input =>
      simpa [effect, _root_.Operation.effect] using insert_ofDirectState state input h_inv
  | delete id deletedId =>
      simp [Except.map, effect, _root_.deleteValid, deleteById_ofDirectState]

theorem effect_preserves_stateEquivalent {op : _root_.YjsOperation A}
    {direct direct' : _root_.YjsState A} {indirect indirect' : YjsState A}
    (h_eq : StateEquivalent direct indirect)
    (h_inv : _root_.YjsStateInvariant direct)
    (h_direct : _root_.Operation.effect op direct = Except.ok direct')
    (h_indirect : effect op indirect = Except.ok indirect') :
    StateEquivalent direct' indirect' := by
  cases op with
  | insert input =>
      simpa [effect, _root_.Operation.effect] using
        insert_preserves_stateEquivalent (input := input) h_eq h_inv h_direct h_indirect
  | delete id deletedId =>
      have h_direct' : _root_.deleteById direct deletedId = direct' := by
        simpa [_root_.Operation.effect, _root_.deleteValid] using h_direct
      have h_indirect' : deleteById indirect deletedId = indirect' := by
        simpa [effect] using h_indirect
      simpa [effect, _root_.Operation.effect, _root_.deleteValid] using
        delete_preserves_stateEquivalent (id := deletedId) h_eq h_direct' h_indirect'

private theorem stateInv_of_prefix
    {hb : CausalOrder (_root_.YjsOperation A)}
    (StateSource : _root_.YjsOperation A → Prop)
    [OperationReplayValidity (A := _root_.YjsOperation A) (S := YjsId) (hb := hb) StateSource]
    (preOps restOps : List (_root_.YjsOperation A))
    {direct : _root_.YjsState A}
    (h_source : ∀ x, x ∈ preOps ++ restOps → StateSource x)
    (h_consistent : hb_consistent hb (preOps ++ restOps))
    (h_closed : hbClosed hb (preOps ++ restOps))
    (h_nodup : IdNoDup (preOps ++ restOps))
    (h_preOps_direct : _root_.interpOps preOps _root_.Operation.init = Except.ok direct) :
    _root_.YjsStateInvariant direct := by
  have h_source_prefix : ∀ x, x ∈ preOps → StateSource x := by
    intro x hx
    exact h_source x (by simp [hx])
  have h_consistent_prefix : hb_consistent hb preOps := by
    exact hb_consistent_sublist (hb := hb) h_consistent (List.sublist_append_left preOps restOps)
  have h_closed_prefix : hbClosed hb preOps := by
    exact hbClosed_prefix (hb := hb) (ops₀ := preOps) (ops₁ := restOps) h_closed
  have h_nodup_prefix : IdNoDup preOps := by
    exact List.Pairwise.sublist (List.sublist_append_left preOps restOps) h_nodup
  exact effect_list_stateInv
    (A := _root_.YjsOperation A) (S := YjsId) (hb := hb)
    (StateSource := StateSource)
    (ops := preOps) h_source_prefix h_consistent_prefix h_closed_prefix h_nodup_prefix h_preOps_direct

private theorem direct_of_indirect_suffix
    {hb : CausalOrder (_root_.YjsOperation A)}
    (StateSource : _root_.YjsOperation A → Prop)
    [OperationReplayValidity (A := _root_.YjsOperation A) (S := YjsId) (hb := hb) StateSource]
    (preOps restOps : List (_root_.YjsOperation A))
    {direct : _root_.YjsState A} {indirect indirect' : YjsState A}
    (h_source : ∀ x, x ∈ preOps ++ restOps → StateSource x)
    (h_consistent : hb_consistent hb (preOps ++ restOps))
    (h_closed : hbClosed hb (preOps ++ restOps))
    (h_nodup : IdNoDup (preOps ++ restOps))
    (h_preOps_direct : _root_.interpOps preOps _root_.Operation.init = Except.ok direct)
    (h_eq : StateEquivalent direct indirect)
    (h_rest_indirect : interpOps restOps indirect = Except.ok indirect') :
    ∃ direct', _root_.interpOps restOps direct = Except.ok direct' ∧ StateEquivalent direct' indirect' := by
  induction restOps generalizing preOps direct indirect with
  | nil =>
      simp [interpOps] at h_rest_indirect
      cases h_rest_indirect
      exact ⟨ direct, by simp [_root_.interpOps], h_eq ⟩
  | cons op restOps ih =>
      have h_direct_inv :
          _root_.YjsStateInvariant direct :=
        stateInv_of_prefix StateSource preOps (op :: restOps)
          h_source h_consistent h_closed h_nodup h_preOps_direct
      have h_source_op : StateSource op := by
        exact h_source op (by simp)
      have h_consistent_prefix : hb_consistent hb preOps := by
        exact hb_consistent_sublist (hb := hb) h_consistent
          (List.sublist_append_left preOps (op :: restOps))
      have h_closed_prefix : hbClosed hb preOps := by
        exact hbClosed_prefix (hb := hb) (ops₀ := preOps) (ops₁ := op :: restOps) h_closed
      have h_nodup_prefix : IdNoDup preOps := by
        exact List.Pairwise.sublist (List.sublist_append_left preOps (op :: restOps)) h_nodup
      have h_valid_op : OperationValidity.isValidState op direct := by
        refine OperationReplayValidity.isValidState_of_history
          (A := _root_.YjsOperation A) (S := YjsId) (hb := hb) (StateSource := StateSource)
          (a := op) (s := direct) (l := preOps) ?_ ?_ h_consistent_prefix h_closed_prefix
          h_preOps_direct h_nodup_prefix
        · exact h_source_op
        · intro x hx_lt
          simpa using h_closed op x preOps restOps rfl hx_lt
      have h_rest_indirect' :
          effect op indirect >>= interpOps restOps = Except.ok indirect' := by
        simpa [interpOps] using h_rest_indirect
      obtain ⟨ indirect1, h_effect_indirect, h_tail_indirect ⟩ :=
        _root_.Except.bind_eq_ok_exist h_rest_indirect'
      subst h_eq
      rw [effect_ofDirectState op direct h_direct_inv] at h_effect_indirect
      cases h_effect_direct : _root_.Operation.effect op direct with
      | error err =>
          simp [Except.map, h_effect_direct] at h_effect_indirect
      | ok direct1 =>
          have h_eq1 : StateEquivalent direct1 indirect1 := by
            have h_map_eq : ofDirectState direct1 = indirect1 := by
              simpa [Except.map, h_effect_direct] using h_effect_indirect
            simpa [StateEquivalent] using h_map_eq
          have h_preOps_effect_list :
              effect_list preOps _root_.Operation.init = Except.ok direct := by
            simpa [_root_.interpOps] using h_preOps_direct
          have h_preOps_direct' :
              _root_.interpOps (preOps ++ [op]) _root_.Operation.init = Except.ok direct1 := by
            rw [_root_.interpOps, effect_list_append]
            rw [h_preOps_effect_list]
            simp [effect_list_cons, bind, Except.bind, h_effect_direct]
          have h_source' : ∀ x, x ∈ (preOps ++ [op]) ++ restOps → StateSource x := by
            intro x hx
            exact h_source x (by simpa [List.append_assoc] using hx)
          have h_consistent' : hb_consistent hb ((preOps ++ [op]) ++ restOps) := by
            simpa [List.append_assoc] using h_consistent
          have h_closed' : hbClosed hb ((preOps ++ [op]) ++ restOps) := by
            simpa [List.append_assoc] using h_closed
          have h_nodup' : IdNoDup ((preOps ++ [op]) ++ restOps) := by
            simpa [List.append_assoc] using h_nodup
          obtain ⟨ direct', h_tail_direct, h_eq' ⟩ :=
            ih (preOps := preOps ++ [op])
              h_source' h_consistent' h_closed' h_nodup'
              h_preOps_direct' h_eq1 h_tail_indirect
          refine ⟨ direct', ?_, h_eq' ⟩
          simpa [_root_.interpOps, effect_list_cons, h_effect_direct] using h_tail_direct

private theorem direct_of_indirect_from_source
    {hb : CausalOrder (_root_.YjsOperation A)}
    (StateSource : _root_.YjsOperation A → Prop)
    [OperationReplayValidity (A := _root_.YjsOperation A) (S := YjsId) (hb := hb) StateSource]
    (ops : List (_root_.YjsOperation A))
    {indirect' : YjsState A}
    (h_source : ∀ x, x ∈ ops → StateSource x)
    (h_consistent : hb_consistent hb ops)
    (h_closed : hbClosed hb ops)
    (h_nodup : IdNoDup ops)
    (h_indirect : interpOps ops YjsEmptyState = Except.ok indirect') :
    ∃ direct', _root_.interpOps ops _root_.Operation.init = Except.ok direct' ∧
      StateEquivalent direct' indirect' := by
  simpa using
    (direct_of_indirect_suffix (StateSource := StateSource)
      (preOps := []) (restOps := ops)
      (direct := _root_.YjsEmptyArray) (indirect := YjsEmptyState)
      (h_source := by
        intro x hx
        simpa using h_source x hx)
      (h_consistent := by simpa using h_consistent)
      (h_closed := by simpa using h_closed)
      (h_nodup := by simpa using h_nodup)
      (h_preOps_direct := by rfl)
      (h_eq := empty_stateEquivalent)
      (h_rest_indirect := h_indirect))

theorem YjsOperationNetwork_converge {A} [DecidableEq A]
    (network : _root_.YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsState A) :
    let hist_i := network.toCausalNetwork.toDeliverMessages i
    let hist_j := network.toCausalNetwork.toDeliverMessages j
    interpOps hist_i YjsEmptyState = Except.ok res₀ →
    interpOps hist_j YjsEmptyState = Except.ok res₁ →
    (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
    res₀ = res₁ := by
  intros hist_i hist_j h_res₀ h_res₁ h_hist_mem
  subst hist_i hist_j
  let hb : CausalOrder (_root_.YjsOperation A) :=
    instCausalNetworkElemCausalOrder network.toCausalNetwork
  have h_consistent_i : hb_consistent hb (network.toCausalNetwork.toDeliverMessages i) := by
    simpa [hb] using
      (hb_consistent_local_history (network := network.toCausalNetwork) (i := i))
  have h_consistent_j : hb_consistent hb (network.toCausalNetwork.toDeliverMessages j) := by
    simpa [hb] using
      (hb_consistent_local_history (network := network.toCausalNetwork) (i := j))
  have h_closed_i : hbClosed hb (network.toCausalNetwork.toDeliverMessages i) := by
    simpa [hb] using toDeliverMessages_hbClosed (network := network) (i := i)
  have h_closed_j : hbClosed hb (network.toCausalNetwork.toDeliverMessages j) := by
    simpa [hb] using toDeliverMessages_hbClosed (network := network) (i := j)
  have h_nodup_i : IdNoDup (network.toCausalNetwork.toDeliverMessages i) := by
    exact toDeliverMessages_IdNoDup (network := network) (i := i)
  have h_nodup_j : IdNoDup (network.toCausalNetwork.toDeliverMessages j) := by
    exact toDeliverMessages_IdNoDup (network := network) (i := j)
  have h_deliver_mem_of_toDeliver_mem :
      ∀ {k : ClientId} {m : _root_.YjsOperation A},
        m ∈ network.toCausalNetwork.toDeliverMessages k →
          Event.Deliver m ∈ network.toCausalNetwork.histories k := by
    intro k m h_mem
    simp [CausalNetwork.toDeliverMessages] at h_mem
    obtain ⟨ ev, h_ev_mem, h_ev_eq ⟩ := h_mem
    cases ev with
    | Broadcast _ =>
        simp at h_ev_eq
    | Deliver m' =>
        simp at h_ev_eq
        subst h_ev_eq
        simpa using h_ev_mem
  let StateSource : _root_.YjsOperation A → Prop :=
    fun a => ∃ i, Event.Broadcast a ∈ network.toCausalNetwork.histories i
  haveI :
      OperationReplayValidity (A := _root_.YjsOperation A) (S := YjsId) (hb := hb) StateSource := {
    isValidState_of_history := by
      intro a s l h_source h_lt h_consistent h_closed h_effect h_nodup
      cases a with
      | delete _ _ =>
          simp [OperationValidity.isValidState, IsValidMessage]
      | insert input =>
          simpa [OperationValidity.isValidState, IsValidMessage] using
            (isValidState_insert_from_source (network := network) (input := input) (s := s) (l := l)
              h_source h_lt h_consistent h_closed h_effect h_nodup)
  }
  have h_source_i :
      ∀ x, x ∈ network.toCausalNetwork.toDeliverMessages i → StateSource x := by
    intro x hx
    have h_deliver_x_mem : Event.Deliver x ∈ network.toCausalNetwork.histories i := by
      exact h_deliver_mem_of_toDeliver_mem hx
    obtain ⟨ c, h_broadcast_x_mem ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_x_mem
    exact ⟨ c, h_broadcast_x_mem ⟩
  have h_source_j :
      ∀ x, x ∈ network.toCausalNetwork.toDeliverMessages j → StateSource x := by
    intro x hx
    have h_deliver_x_mem : Event.Deliver x ∈ network.toCausalNetwork.histories j := by
      exact h_deliver_mem_of_toDeliver_mem hx
    obtain ⟨ c, h_broadcast_x_mem ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_x_mem
    exact ⟨ c, h_broadcast_x_mem ⟩
  obtain ⟨ direct₀, h_direct₀, h_eq₀ ⟩ :=
    direct_of_indirect_from_source StateSource
      (network.toCausalNetwork.toDeliverMessages i)
      h_source_i h_consistent_i h_closed_i h_nodup_i h_res₀
  obtain ⟨ direct₁, h_direct₁, h_eq₁ ⟩ :=
    direct_of_indirect_from_source StateSource
      (network.toCausalNetwork.toDeliverMessages j)
      h_source_j h_consistent_j h_closed_j h_nodup_j h_res₁
  have h_direct_eq : direct₀ = direct₁ := by
    exact _root_.YjsOperationNetwork_converge' network i j direct₀ direct₁
      h_direct₀ h_direct₁ h_hist_mem
  have h_res₀_eq : ofDirectState direct₀ = res₀ := by
    simpa [StateEquivalent] using h_eq₀
  have h_res₁_eq : ofDirectState direct₁ = res₁ := by
    simpa [StateEquivalent] using h_eq₁
  calc
    res₀ = ofDirectState direct₀ := by simpa using h_res₀_eq.symm
    _ = ofDirectState direct₁ := by simp [h_direct_eq]
    _ = res₁ := by simpa using h_res₁_eq

end Indirect
