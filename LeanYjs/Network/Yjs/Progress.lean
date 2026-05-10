import LeanYjs.Network.Yjs.YjsNetwork

/-!
# Progress for the Yjs network model

This file proves the analogue of Gomes et al. (OOPSLA 2017) `sec-progress`
theorem (`apply-operations-never-fails` for the RGA instantiation): for any
`YjsOperationNetwork` and any client `i`, replaying the messages delivered to
`i` from `Operation.init` succeeds — there exists `res` with
`interpOps (network.toDeliverMessages i) Operation.init = Except.ok res`.

The proof has three layers:

1. Algorithm-level progress (`integrate_progress`, `integrateSafe_progress`,
   `YjsState.insert_progress`): under `YjsArrInvariant`/`YjsStateInvariant`
   together with `IsValidMessage` (origins/right-origins exist in the array)
   and `YjsOperation.UniqueId` (the new id has a strictly larger clock than
   any existing item from the same client), the executable `integrate` /
   `YjsState.insert` cannot fail.
2. Network-level uniqueness at delivery time (`uniqueId_at_delivery`): when
   an operation is about to be delivered at client `j`, the items already
   present in `j`'s state from the same client must have been inserted by
   earlier broadcasts of that client, hence — by `histories_clock_mono` —
   have strictly smaller clocks.
3. Inductive lift to whole histories (`YjsOperationNetwork_progress`): combine
   the previous two layers with `effect_list_stateInv` to walk along the
   delivered prefix, showing each step succeeds.
-/

open NetworkModels

variable {A : Type} [DecidableEq A]

namespace LeanYjs.Progress

section AlgorithmLevel

/-- `findLeftIdx` succeeds whenever `input.toItem` succeeds, returning a value in
`[-1, arr.size)`. -/
theorem findLeftIdx_progress {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {newItem : YjsItem A} :
    uniqueId arr.toList →
    input.toItem arr = Except.ok newItem →
    ∃ leftIdx : Int,
      findLeftIdx input.originId arr = Except.ok leftIdx ∧
        (-1 : Int) ≤ leftIdx ∧ leftIdx < arr.size := by
  intros h_unique h_toItem
  cases h_originId : input.originId with
  | none =>
    refine ⟨ -1, ?_, ?_, ?_ ⟩
    · simp [findLeftIdx, h_originId, pure, Except.pure]
    · omega
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast Nat.zero_le _
      omega
  | some oid =>
    rw [IntegrateInput.toItem_ok_iff _ _ _ h_unique] at h_toItem
    obtain ⟨ _o, _r, _id, _c, _, h_origin, _ ⟩ := h_toItem
    simp [isLeftIdPtr, h_originId] at h_origin
    obtain ⟨ originItem, _, h_find ⟩ := h_origin
    have h_findIdx :
        arr.findIdx? (fun item => item.id = oid) =
          some (arr.findIdx (fun item => item.id = oid)) := by
      apply Array.findIdx?_eq_some_of_exists
      have h_mem : originItem ∈ arr := Array.mem_of_find?_eq_some h_find
      rw [Array.find?_eq_some_iff_getElem] at h_find
      exact ⟨ originItem, h_mem, by simpa using h_find.1 ⟩
    refine ⟨ arr.findIdx (fun item => item.id = oid), ?_, ?_, ?_ ⟩
    · simp [findLeftIdx, h_originId, h_findIdx, pure, Except.pure]
    · have : (0 : Int) ≤ (arr.findIdx (fun item => item.id = oid) : Int) := by
        exact_mod_cast Nat.zero_le _
      omega
    · rw [Array.findIdx?_eq_some_iff_getElem] at h_findIdx
      obtain ⟨ h_lt, _, _ ⟩ := h_findIdx
      exact_mod_cast h_lt

/-- `findRightIdx` succeeds whenever `input.toItem` succeeds, returning a value in
`[-1, arr.size]`. -/
theorem findRightIdx_progress {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {newItem : YjsItem A} :
    uniqueId arr.toList →
    input.toItem arr = Except.ok newItem →
    ∃ rightIdx : Int,
      findRightIdx input.rightOriginId arr = Except.ok rightIdx ∧
        (-1 : Int) ≤ rightIdx ∧ rightIdx ≤ arr.size := by
  intros h_unique h_toItem
  cases h_rightOriginId : input.rightOriginId with
  | none =>
    refine ⟨ arr.size, ?_, ?_, ?_ ⟩
    · simp [findRightIdx, h_rightOriginId, pure, Except.pure]
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast Nat.zero_le _
      omega
    · omega
  | some rid =>
    rw [IntegrateInput.toItem_ok_iff _ _ _ h_unique] at h_toItem
    obtain ⟨ _o, _r, _id, _c, _, _, h_rightOrigin, _ ⟩ := h_toItem
    simp [isRightIdPtr, h_rightOriginId] at h_rightOrigin
    obtain ⟨ rightItem, _, h_find ⟩ := h_rightOrigin
    have h_findIdx :
        arr.findIdx? (fun item => item.id = rid) =
          some (arr.findIdx (fun item => item.id = rid)) := by
      apply Array.findIdx?_eq_some_of_exists
      have h_mem : rightItem ∈ arr := Array.mem_of_find?_eq_some h_find
      rw [Array.find?_eq_some_iff_getElem] at h_find
      exact ⟨ rightItem, h_mem, by simpa using h_find.1 ⟩
    refine ⟨ arr.findIdx (fun item => item.id = rid), ?_, ?_, ?_ ⟩
    · simp [findRightIdx, h_rightOriginId, h_findIdx, pure, Except.pure]
    · have : (0 : Int) ≤ (arr.findIdx (fun item => item.id = rid) : Int) := by
        exact_mod_cast Nat.zero_le _
      omega
    · rw [Array.findIdx?_eq_some_iff_getElem] at h_findIdx
      obtain ⟨ h_lt, _, _ ⟩ := h_findIdx
      exact_mod_cast (Nat.le_of_lt h_lt)

/-- `mkItemByIndex` succeeds when both indices are within the legal range. -/
theorem mkItemByIndex_progress {leftIdx rightIdx : Int} (input : IntegrateInput A)
    {arr : Array (YjsItem A)} :
    (-1 : Int) ≤ leftIdx → leftIdx ≤ arr.size →
    (-1 : Int) ≤ rightIdx → rightIdx ≤ arr.size →
    ∃ item : YjsItem A, mkItemByIndex leftIdx rightIdx input arr = Except.ok item := by
  intros h_left_ge h_left_le h_right_ge h_right_le
  have getPtr_progress : ∀ (idx : Int), -1 ≤ idx → idx ≤ arr.size →
      ∃ ptr, getPtrExcept arr idx = Except.ok ptr := by
    intro idx h_ge h_le
    unfold getPtrExcept
    by_cases h_neg : idx = -1
    · exact ⟨ YjsPtr.first, by simp [h_neg] ⟩
    · by_cases h_size : idx = arr.size
      · exact ⟨ YjsPtr.last, by simp [h_size] ⟩
      · have h_in : 0 ≤ idx ∧ idx < arr.size := by omega
        have h_nat_lt : idx.toNat < arr.size := by
          rcases h_in with ⟨ h_low, h_high ⟩
          exact (Int.toNat_lt h_low).2 h_high
        have h_some : arr[idx.toNat]? = some arr[idx.toNat] := by
          exact Array.getElem?_eq_some_iff.mpr ⟨ h_nat_lt, rfl ⟩
        refine ⟨ YjsPtr.itemPtr arr[idx.toNat], ?_ ⟩
        simp [h_neg, h_size, h_some]
  obtain ⟨ leftPtr, h_leftPtr ⟩ := getPtr_progress leftIdx h_left_ge h_left_le
  obtain ⟨ rightPtr, h_rightPtr ⟩ := getPtr_progress rightIdx h_right_ge h_right_le
  refine ⟨ YjsItem.mk leftPtr rightPtr input.id input.content, ?_ ⟩
  simp [mkItemByIndex, h_leftPtr, h_rightPtr, bind, Except.bind, pure, Except.pure]

/-- Algorithm-level progress for `integrate`: under the array invariant and a
successful `input.toItem`, the executable `integrate` cannot fail. -/
theorem integrate_progress {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {newItem : YjsItem A} :
    YjsArrInvariant arr.toList →
    input.toItem arr = Except.ok newItem →
    ∃ arr', integrate input arr = Except.ok arr' := by
  intros harrinv h_toItem
  obtain ⟨ leftIdx, h_left, h_left_ge, h_left_lt ⟩ :=
    findLeftIdx_progress (input := input) (arr := arr) harrinv.unique h_toItem
  obtain ⟨ rightIdx, h_right, h_right_ge, h_right_le ⟩ :=
    findRightIdx_progress (input := input) (arr := arr) harrinv.unique h_toItem
  have h_left_le : leftIdx ≤ arr.size := le_of_lt h_left_lt
  obtain ⟨ destIdx, h_dest ⟩ :=
    findIntegratedIndex_safe (leftIdx := leftIdx) (rightIdx := rightIdx)
      (arr := arr) (input := input) (newItem := newItem)
      harrinv h_toItem h_left_ge h_left_le h_right_ge h_right_le
  obtain ⟨ item, h_item ⟩ :=
    mkItemByIndex_progress (leftIdx := leftIdx) (rightIdx := rightIdx) (arr := arr)
      input h_left_ge h_left_le h_right_ge h_right_le
  refine ⟨ arr.insertIdxIfInBounds destIdx item, ?_ ⟩
  simp [integrate, h_left, h_right, h_dest, h_item, bind, Except.bind, pure, Except.pure]

/-- Algorithm-level progress for `integrateSafe`: adds the `isClockSafe` precondition.
We phrase this in terms of `YjsOperation.UniqueId`, which is the proposition
`isClockSafe` decides. -/
theorem integrateSafe_progress {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {newItem : YjsItem A} :
    YjsArrInvariant arr.toList →
    input.toItem arr = Except.ok newItem →
    YjsOperation.UniqueId (YjsOperation.insert input) arr →
    ∃ arr', integrateSafe input arr = Except.ok arr' := by
  intros harrinv h_toItem h_uniqueId
  have h_uniqueId' : ∀ x ∈ arr, x.id.clientId = input.id.clientId → x.id.clock < input.id.clock := by
    intro x h_mem h_client
    have h := h_uniqueId x h_mem
    simp [YjsOperation.id] at h
    exact h h_client
  have h_safe : isClockSafe input.id arr = true := by
    simp only [isClockSafe, Array.all_eq_true]
    intro i h_lt
    have h_mem : arr[i] ∈ arr := Array.getElem_mem h_lt
    by_cases h_client : arr[i].id.clientId = input.id.clientId
    · have h_lt_clock := h_uniqueId' arr[i] h_mem h_client
      simp [h_client]
      omega
    · simp [h_client]
  obtain ⟨ arr', h_arr' ⟩ := integrate_progress (input := input) (arr := arr) (newItem := newItem)
    harrinv h_toItem
  refine ⟨ arr', ?_ ⟩
  simp [integrateSafe, h_safe, h_arr']

/-- Progress for `YjsState.insert`. -/
theorem YjsState_insert_progress {s : YjsState A} {input : IntegrateInput A}
    {newItem : YjsItem A} :
    YjsStateInvariant s →
    input.toItem s.items = Except.ok newItem →
    YjsOperation.UniqueIdState (YjsOperation.insert input) s →
    ∃ s', s.insert input = Except.ok s' := by
  intros h_inv h_toItem h_uniqueId
  obtain ⟨ arr', h_arr' ⟩ :=
    integrateSafe_progress (input := input) (arr := s.items) (newItem := newItem)
      h_inv h_toItem h_uniqueId
  refine ⟨ ⟨ arr', s.deletedIds ⟩, ?_ ⟩
  simp [YjsState.insert, h_arr', bind, Except.bind, pure, Except.pure]

end AlgorithmLevel

section NetworkLevel

/-- Single-step progress for `Operation.effect` on `YjsOperation`. The `delete`
case is unconditional; the `insert` case demands `IsValidMessage` and
`YjsOperation.UniqueId`. -/
theorem Operation_effect_progress (op : YjsOperation A) (s : YjsState A) :
    YjsStateInvariant s →
    IsValidMessage s.items op →
    YjsOperation.UniqueId op s.items →
    ∃ s', Operation.effect op s = Except.ok s' := by
  intro h_inv h_valid h_uniqueId
  cases op with
  | insert input =>
    simp [IsValidMessage] at h_valid
    obtain ⟨ item, h_toItem, _ ⟩ := h_valid
    obtain ⟨ s', h_s' ⟩ :=
      YjsState_insert_progress (s := s) (input := input) (newItem := item)
        h_inv h_toItem h_uniqueId
    exact ⟨ s', by simpa [Operation.effect] using h_s' ⟩
  | delete _ deletedId =>
    exact ⟨ deleteValid deletedId s, by simp [Operation.effect] ⟩

end NetworkLevel

section LocalOrdering

/--
If `toDeliverMessages j = pre ++ [op] ++ rest` and `op_x ∈ pre`, then in `j`'s
underlying history `Event.Deliver op_x` precedes `Event.Deliver op`. This is the
order-preserving consequence of `filterMap eventDeliver`.
-/
theorem locallyOrdered_deliver_of_split
    {network : CausalNetwork (YjsOperation A)} {j : ClientId}
    {pre : List (YjsOperation A)} {op : YjsOperation A} {rest : List (YjsOperation A)}
    (h_split : network.toDeliverMessages j = pre ++ [op] ++ rest)
    (op_x : YjsOperation A) (h_op_x_pre : op_x ∈ pre) :
    locallyOrdered network.toNodeHistories j (Event.Deliver op_x) (Event.Deliver op) := by
  -- Decompose `histories j` along the filterMap.
  have h_eq : (network.histories j).filterMap eventDeliver = pre ++ ([op] ++ rest) := by
    simpa [CausalNetwork.toDeliverMessages, List.append_assoc] using h_split
  obtain ⟨ l1, lrest, h_hist_eq, h_pre_filt, h_tail_filt ⟩ :=
    List.filterMap_eq_append_iff.mp h_eq
  obtain ⟨ l_op, l_rest, h_lrest_eq, h_op_filt, _h_rest_filt ⟩ :=
    List.filterMap_eq_append_iff.mp h_tail_filt
  -- `Event.Deliver op_x ∈ l1`.
  have h_op_x_in_filt : op_x ∈ pre := h_op_x_pre
  have h_op_x_in_l1 : Event.Deliver op_x ∈ l1 := by
    rw [← h_pre_filt] at h_op_x_in_filt
    rcases List.mem_filterMap.mp h_op_x_in_filt with ⟨ ev, h_ev_mem, h_ev_eq ⟩
    cases ev with
    | Broadcast _ => simp [eventDeliver] at h_ev_eq
    | Deliver m =>
      simp [eventDeliver] at h_ev_eq
      cases h_ev_eq
      exact h_ev_mem
  -- `Event.Deliver op ∈ l_op`.
  have h_op_in_l_op : Event.Deliver op ∈ l_op := by
    have h_op_mem : op ∈ ([op] : List (YjsOperation A)) := by simp
    rw [← h_op_filt] at h_op_mem
    rcases List.mem_filterMap.mp h_op_mem with ⟨ ev, h_ev_mem, h_ev_eq ⟩
    cases ev with
    | Broadcast _ => simp [eventDeliver] at h_ev_eq
    | Deliver m =>
      simp [eventDeliver] at h_ev_eq
      cases h_ev_eq
      exact h_ev_mem
  -- Extract surrounding lists.
  rcases List.mem_iff_append.mp h_op_x_in_l1 with ⟨ p1, p2, h_l1_eq ⟩
  rcases List.mem_iff_append.mp h_op_in_l_op with ⟨ q1, q2, h_l_op_eq ⟩
  refine ⟨ p1, p2 ++ q1, q2 ++ l_rest, ?_ ⟩
  rw [h_hist_eq, h_lrest_eq, h_l1_eq, h_l_op_eq]
  simp [List.append_assoc]

/--
At the source of an operation `op` (i.e., the client that broadcasts it),
two ordering possibilities for any other operation `op_x` broadcast at the
same source: either `Broadcast op_x` precedes `Broadcast op` in the source's
history, or vice versa.
-/
private lemma broadcast_dichotomy
    {network : NetworkBase (YjsOperation A)} {c : ClientId}
    (a b : YjsOperation A)
    (h_a : Event.Broadcast a ∈ network.histories c)
    (h_b : Event.Broadcast b ∈ network.histories c)
    (h_ne : a ≠ b) :
    locallyOrdered network.toNodeHistories c (Event.Broadcast a) (Event.Broadcast b) ∨
    locallyOrdered network.toNodeHistories c (Event.Broadcast b) (Event.Broadcast a) := by
  rcases List.mem_iff_append.mp h_a with ⟨ pa, qa, h_a_eq ⟩
  rcases List.mem_iff_append.mp h_b with ⟨ pb, qb, h_b_eq ⟩
  have h_eq : pa ++ Event.Broadcast a :: qa = pb ++ Event.Broadcast b :: qb := by
    rw [← h_a_eq, ← h_b_eq]
  rw [List.append_eq_append_iff] at h_eq
  rcases h_eq with ⟨ as, h_pb_eq, h_xs_eq ⟩ | ⟨ bs, h_pa_eq, h_zs_eq ⟩
  · -- inl: pb = pa ++ as, Broadcast a :: qa = as ++ Broadcast b :: qb
    -- So pa is shorter ⇒ Broadcast a precedes Broadcast b ⇒ left
    cases as with
    | nil =>
      simp at h_xs_eq
      exact absurd h_xs_eq.1 h_ne
    | cons hd tl =>
      simp at h_xs_eq
      obtain ⟨ h_hd, h_qa_eq ⟩ := h_xs_eq
      left
      refine ⟨ pa, tl, qb, ?_ ⟩
      rw [h_a_eq, h_qa_eq]
      simp
  · -- inr: pa = pb ++ bs, Broadcast b :: qb = bs ++ Broadcast a :: qa
    -- So pb is shorter ⇒ Broadcast b precedes Broadcast a ⇒ right
    cases bs with
    | nil =>
      simp at h_zs_eq
      exact absurd h_zs_eq.1 h_ne.symm
    | cons hd tl =>
      simp at h_zs_eq
      obtain ⟨ h_hd, h_qb_eq ⟩ := h_zs_eq
      right
      refine ⟨ pb, tl, qa, ?_ ⟩
      rw [h_b_eq, h_qb_eq]
      simp

end LocalOrdering

section UniqueIdAtDelivery

/--
At delivery time, the next operation's id is unique with respect to the items
already in the local state. This is the central invariant that makes the
`isClockSafe` check inside `integrateSafe` always succeed.

Proof sketch: any item `x` in the state at delivery time came from an earlier
delivered insert `op_x`. Since `x.id.clientId = op.id.clientId =: c`,
`op_x.id.clientId = c` too, so by `histories_client_id` both `op_x` and `op`
were broadcast by client `c`. Causal delivery and the order in which they were
delivered at `j` force `Broadcast op_x` to come before `Broadcast op` in `c`'s
history; `histories_clock_mono` then yields `op_x.id.clock < op.id.clock`.
-/
theorem uniqueId_at_delivery (network : YjsOperationNetwork A) (j : ClientId)
    (pre : List (YjsOperation A)) (op : YjsOperation A) (rest : List (YjsOperation A))
    (s : YjsState A) :
    network.toCausalNetwork.toDeliverMessages j = pre ++ [op] ++ rest →
    effect_list pre Operation.init = Except.ok s →
    YjsStateInvariant s →
    YjsOperation.UniqueId op s.items := by
  intros h_split h_eff h_inv x h_mem h_client
  -- Step 1: x in s.items, by uniqueId, find x via state.find?
  have h_unique_s : uniqueId s.toList := h_inv.unique
  have h_pairwise : List.Pairwise (fun a b : YjsItem A => a.id ≠ b.id) s.items.toList :=
    h_unique_s
  have h_find_x : s.find? (fun i => i.id = x.id) = some x := by
    show s.items.find? (fun i => i.id = x.id) = some x
    rcases (Array.mem_iff_getElem).mp h_mem with ⟨ idx, h_lt, h_get ⟩
    rw [Array.find?_eq_some_iff_getElem]
    refine ⟨ ?_, idx, h_lt, by simp [h_get], ?_ ⟩
    · simp [← h_get]
    · intro k h_k_lt
      have h_k_lt_list : k < s.items.toList.length := by
        simpa [Array.length_toList] using lt_trans h_k_lt h_lt
      have h_idx_lt_list : idx < s.items.toList.length := by
        simpa [Array.length_toList] using h_lt
      rw [List.pairwise_iff_getElem] at h_pairwise
      have h_neq := h_pairwise k idx h_k_lt_list h_idx_lt_list h_k_lt
      have : s.items[k].id ≠ s.items[idx].id := by
        simpa [Array.getElem_toList] using h_neq
      have h_neq' : s.items[k].id ≠ x.id := by
        intro h_eq
        apply this
        rw [h_eq, ← h_get]
      simp; exact h_neq'
  -- Step 2: x came from an insert op_x in pre
  obtain ⟨ op_x_input, h_op_x_pre, h_op_x_id ⟩ :=
    effect_list_find?_exists_insert_id (ops := pre) (state := s) (id := x.id) (item := x)
      h_eff h_find_x
  set op_x := YjsOperation.insert op_x_input with h_op_x_def
  -- Step 3: op_x is delivered at j (op_x ∈ pre ⊆ toDeliverMessages j)
  have h_op_x_in_deliver : op_x ∈ network.toCausalNetwork.toDeliverMessages j := by
    rw [h_split]
    exact List.mem_append_left _ (List.mem_append_left _ h_op_x_pre)
  have h_deliver_op_x : Event.Deliver op_x ∈ network.toCausalNetwork.histories j := by
    exact deliver_mem_of_toDeliver_mem network.toCausalNetwork j op_x h_op_x_in_deliver
  -- Step 4: op_x is broadcast at some client c_x; by histories_client_id, c_x = op_x.id.clientId
  obtain ⟨ c_x, h_broadcast_op_x ⟩ :=
    network.toCausalNetwork.deliver_has_a_cause h_deliver_op_x
  have h_c_x_eq : c_x = op_x.id.clientId := by
    have := network.histories_client_id h_broadcast_op_x
    exact this.symm
  -- op_x.id = op_x_input.id (definition); op_x_input.id = x.id (h_op_x_id)
  have h_op_x_id_clientId : op_x.id.clientId = x.id.clientId := by
    rw [h_op_x_def]; show op_x_input.id.clientId = _; rw [h_op_x_id]
  have h_c_x_eq_client : c_x = x.id.clientId := by rw [h_c_x_eq, h_op_x_id_clientId]
  -- Step 5: op also delivered at j, broadcast at some client c
  have h_op_in_deliver : op ∈ network.toCausalNetwork.toDeliverMessages j := by
    rw [h_split]; simp
  have h_deliver_op : Event.Deliver op ∈ network.toCausalNetwork.histories j :=
    deliver_mem_of_toDeliver_mem network.toCausalNetwork j op h_op_in_deliver
  obtain ⟨ c, h_broadcast_op ⟩ :=
    network.toCausalNetwork.deliver_has_a_cause h_deliver_op
  have h_c_eq : c = op.id.clientId := (network.histories_client_id h_broadcast_op).symm
  -- Both broadcast by the same client (since x.id.clientId = op.id.clientId)
  have h_c_x_eq_c : c_x = c := by rw [h_c_x_eq_client, h_client, ← h_c_eq]
  rw [h_c_x_eq_c] at h_broadcast_op_x
  -- Step 6: op_x ≠ op by IdNoDup at j
  have h_id_no_dup : IdNoDup (network.toCausalNetwork.toDeliverMessages j) := by
    exact toDeliverMessages_IdNoDup (network := network) (i := j)
  have h_op_x_ne_op : op_x ≠ op := by
    intro h_eq
    -- op_x ∈ pre, op ∈ {op}, but pre ++ [op] ++ rest is IdNoDup
    rw [h_split] at h_id_no_dup
    have h_op_x_id_eq_op : WithId.id op_x = WithId.id op := by rw [h_eq]
    have h_pairwise_split : List.Pairwise (fun a b : YjsOperation A => WithId.id a ≠ WithId.id b)
        (pre ++ [op] ++ rest) := h_id_no_dup
    rw [List.append_assoc] at h_pairwise_split
    rw [List.pairwise_append] at h_pairwise_split
    rcases h_pairwise_split with ⟨ _, _, h_inter ⟩
    apply h_inter op_x h_op_x_pre op (by simp) h_op_x_id_eq_op
  -- Step 7: Local broadcast order at c → either op_x before op or op before op_x in c
  rcases broadcast_dichotomy (network := network.toCausalNetwork.toNetworkBase) op_x op
      h_broadcast_op_x h_broadcast_op h_op_x_ne_op with h_order | h_order
  · -- Broadcast op_x precedes Broadcast op at c.
    -- Apply histories_clock_mono.
    rcases h_order with ⟨ l1, l2, l3, h_c_hist ⟩
    have h_clock_lt : op_x.id.clock < op.id.clock :=
      network.histories_clock_mono (a := op_x) (b := op) (i := c)
        (pre := l1) (mid := l2) (post := l3) h_c_hist
    have h_x_clock_lt : x.id.clock < op.id.clock := by
      have h_eq_clock : op_x.id.clock = x.id.clock := by
        rw [h_op_x_def]; show op_x_input.id.clock = _; rw [h_op_x_id]
      rw [← h_eq_clock]; exact h_clock_lt
    exact h_x_clock_lt
  · -- Broadcast op precedes Broadcast op_x at c.
    -- Then op < op_x (in hb), so by causal delivery Deliver op precedes Deliver op_x at j.
    -- But Deliver op_x precedes Deliver op at j (since op_x ∈ pre, op = next).
    -- Contradiction via locallyOrdered_asymm.
    exfalso
    have h_hb : HappensBefore network.toCausalNetwork.toNetworkBase op op_x :=
      HappensBefore.broadcast_broadcast_local h_order
    have h_local_op_op_x : locallyOrdered network.toCausalNetwork.toNodeHistories j
        (Event.Deliver op) (Event.Deliver op_x) := by
      exact network.toCausalNetwork.causal_delivery h_deliver_op_x h_hb
    have h_local_op_x_op : locallyOrdered network.toCausalNetwork.toNodeHistories j
        (Event.Deliver op_x) (Event.Deliver op) :=
      locallyOrdered_deliver_of_split (network := network.toCausalNetwork) (j := j)
        (pre := pre) (op := op) (rest := rest) h_split op_x h_op_x_pre
    exact locallyOrdered_asymm h_local_op_x_op h_local_op_op_x

end UniqueIdAtDelivery

section MainTheorem

/--
**Progress** (network level): for any `YjsOperationNetwork` and any client
`i`, replaying the messages delivered to `i` from `Operation.init` succeeds.
This is the Yjs analogue of Gomes et al.'s `apply-operations-never-fails`
/ `sec-progress`. Together with `YjsOperationNetwork_converge'`, it shows
that the Yjs convergence theorem is non-vacuous.
-/
theorem YjsOperationNetwork_progress (network : YjsOperationNetwork A) (i : ClientId) :
    ∃ res, interpOps (network.toCausalNetwork.toDeliverMessages i) Operation.init = Except.ok res := by
  -- Inductive lift: every prefix of the delivered messages successfully replays.
  suffices h : ∀ (pre rest : List (YjsOperation A)),
      network.toCausalNetwork.toDeliverMessages i = pre ++ rest →
      ∃ s, effect_list pre Operation.init = Except.ok s ∧ YjsStateInvariant s by
    obtain ⟨ s, h_eff, _ ⟩ := h (network.toCausalNetwork.toDeliverMessages i) [] (by simp)
    exact ⟨ s, by simpa [interpOps] using h_eff ⟩
  -- Use right-fold induction so we can extend the prefix one operation at a time.
  intro pre rest h_split
  induction pre using List.reverseRecOn generalizing rest with
  | nil =>
    refine ⟨ Operation.init, ?_, ?_ ⟩
    · simp [effect_list, pure, Except.pure]
    · -- StateInv at init
      exact YjsArrayInvariant_empty
  | append_singleton pre' op ih =>
    -- Need a smaller prefix decomposition for ih.
    have h_split' : network.toCausalNetwork.toDeliverMessages i = pre' ++ (op :: rest) := by
      simpa [List.append_assoc] using h_split
    obtain ⟨ s_pre, h_eff_pre, h_inv_pre ⟩ := ih (op :: rest) h_split'
    -- Show op succeeds.
    have h_op_split : network.toCausalNetwork.toDeliverMessages i = pre' ++ [op] ++ rest := by
      simpa [List.append_assoc] using h_split
    have h_uniqueId : YjsOperation.UniqueId op s_pre.items :=
      uniqueId_at_delivery network i pre' op rest s_pre h_op_split h_eff_pre h_inv_pre
    -- IsValidMessage at delivery: derive from isValidState_insert_from_source.
    have h_valid : IsValidMessage s_pre.items op := by
      cases op with
      | delete _ _ => simp [IsValidMessage]
      | insert input =>
        let hb : CausalOrder (YjsOperation A) :=
          instCausalNetworkElemCausalOrder network.toCausalNetwork
        -- pre' is a prefix of toDeliverMessages i; build the ingredients for
        -- `isValidState_insert_from_source`.
        have h_op_in_deliver : YjsOperation.insert input ∈ network.toCausalNetwork.toDeliverMessages i := by
          rw [h_op_split]; simp
        have h_deliver_op : Event.Deliver (YjsOperation.insert input) ∈
            network.toCausalNetwork.histories i :=
          deliver_mem_of_toDeliver_mem network.toCausalNetwork i (YjsOperation.insert input)
            h_op_in_deliver
        obtain ⟨ srcClient, h_src ⟩ :=
          network.toCausalNetwork.deliver_has_a_cause h_deliver_op
        -- pre' is hb-consistent
        have h_consistent_full : hb_consistent hb (network.toCausalNetwork.toDeliverMessages i) := by
          simpa [hb] using
            (hb_consistent_local_history (network := network.toCausalNetwork) (i := i))
        have h_pre'_sublist :
            pre'.Sublist (network.toCausalNetwork.toDeliverMessages i) := by
          rw [h_op_split]
          have h1 : pre'.Sublist (pre' ++ [YjsOperation.insert input]) :=
            List.sublist_append_left _ _
          have h2 : (pre' ++ [YjsOperation.insert input]).Sublist
              (pre' ++ [YjsOperation.insert input] ++ rest) := List.sublist_append_left _ _
          exact h1.trans h2
        have h_consistent_pre : hb_consistent hb pre' :=
          hb_consistent_sublist (hb := hb) h_consistent_full h_pre'_sublist
        have h_closed_full : hbClosed hb (network.toCausalNetwork.toDeliverMessages i) := by
          intro a b l₁ l₂ h_eq h_b_lt
          have h_a_mem : a ∈ network.toCausalNetwork.toDeliverMessages i := by
            rw [h_eq]; simp
          have h_deliver_a_mem : Event.Deliver a ∈ network.toCausalNetwork.histories i :=
            deliver_mem_of_toDeliver_mem _ _ _ h_a_mem
          have h_local : locallyOrdered network.toCausalNetwork.toNodeHistories i
              (Event.Deliver b) (Event.Deliver a) :=
            network.toCausalNetwork.causal_delivery h_deliver_a_mem h_b_lt
          have h_deliver_b_mem : Event.Deliver b ∈ network.toCausalNetwork.histories i := by
            obtain ⟨ pre_e, mid_e, post_e, h_hist_eq ⟩ := h_local
            rw [h_hist_eq]; simp
          have h_b_mem : b ∈ network.toCausalNetwork.toDeliverMessages i :=
            toDeliver_mem_of_deliver_mem _ _ _ h_deliver_b_mem
          have h_cons_suffix : hb_consistent hb (a :: l₂) := by
            apply hb_consistent_sublist (hb := hb) h_consistent_full
            rw [h_eq]
            simpa using (List.sublist_append_right (l₁ := a :: l₂) (l₂ := l₁))
          have h_not_b_in_l₂ : b ∉ l₂ := by
            intro h_b_in_l₂
            cases h_cons_suffix with
            | cons _ _ _ h_no_lt =>
              exact h_no_lt b h_b_in_l₂ (le_of_lt h_b_lt)
          rw [h_eq] at h_b_mem
          simp [List.mem_append] at h_b_mem
          rcases h_b_mem with h_b_in_l₁ | h_b_eq_a | h_b_in_l₂
          · exact h_b_in_l₁
          · subst h_b_eq_a; exact (lt_irrefl _ h_b_lt).elim
          · exact (h_not_b_in_l₂ h_b_in_l₂).elim
        have h_closed_pre : hbClosed hb pre' := by
          intro a b l₁ l₂ h_eq h_b_lt
          have h_eq_full :
              network.toCausalNetwork.toDeliverMessages i =
                l₁ ++ a :: l₂ ++ ([YjsOperation.insert input] ++ rest) := by
            rw [h_op_split, ← h_eq]
            simp [List.append_assoc]
          have h_b_mem :=
            h_closed_full a b l₁ (l₂ ++ ([YjsOperation.insert input] ++ rest))
              (by simpa [List.append_assoc] using h_eq_full) h_b_lt
          exact h_b_mem
        have h_id_nodup_pre : IdNoDup pre' := by
          have h_id_nodup_full : IdNoDup (network.toCausalNetwork.toDeliverMessages i) :=
            toDeliverMessages_IdNoDup (network := network) (i := i)
          exact List.Pairwise.sublist h_pre'_sublist h_id_nodup_full
        have h_lt_in_pre' :
            ∀ x, (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt x
              (YjsOperation.insert input) → x ∈ pre' := by
          intro x h_x_lt
          have h_x_in :=
            h_closed_full (YjsOperation.insert input) x pre' rest
              (by simpa [List.append_assoc] using h_op_split) h_x_lt
          exact h_x_in
        have h_valid_extracted :
            ∃ item, input.toItem s_pre.items = Except.ok item ∧ item.isValid :=
          isValidState_insert_causally (input := input) (s := s_pre) (l := pre')
            ⟨ srcClient, h_src ⟩ h_lt_in_pre' h_consistent_pre h_closed_pre h_eff_pre h_id_nodup_pre
        simpa [IsValidMessage] using h_valid_extracted
    -- Algorithm-level progress for one step.
    obtain ⟨ s', h_step ⟩ := Operation_effect_progress op s_pre h_inv_pre h_valid h_uniqueId
    refine ⟨ s', ?_, ?_ ⟩
    · have h_append : effect_list (pre' ++ [op]) Operation.init = Except.ok s' := by
        rw [effect_list_append]
        rw [h_eff_pre]
        simp [effect_list, h_step, bind, Except.bind, pure, Except.pure]
      exact h_append
    · -- Preserves YjsStateInvariant
      have := ValidatableOperation.stateInv_effect (A := YjsOperation A)
        op s_pre s' h_inv_pre h_valid h_step
      simpa using this

end MainTheorem

end LeanYjs.Progress
