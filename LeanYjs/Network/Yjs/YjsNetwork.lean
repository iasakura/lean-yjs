import LeanYjs.Item
import LeanYjs.Algorithm.Delete.Basic
import LeanYjs.Algorithm.Delete.Spec
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Commutativity.InsertInsert
import LeanYjs.Algorithm.Commutativity.InsertDelete
import LeanYjs.Algorithm.Commutativity.DeleteDelete
import LeanYjs.Network.CausalNetwork
import LeanYjs.Network.StrongCausalOrder
import LeanYjs.Network.OperationNetwork

section YjsNetwork

open NetworkModels

inductive YjsOperation A where
| insert (item : IntegrateInput A) : YjsOperation A
| delete (id deletedId : YjsId) : YjsOperation A
deriving Repr, DecidableEq

def YjsOperation.id {A} (op : YjsOperation A) : YjsId :=
  match op with
  | YjsOperation.insert item => item.id
  | YjsOperation.delete id _ => id

theorem YjsArrayInvariant_empty {A} : YjsArrInvariant ([] : List (YjsItem A)) := by
  constructor
  . constructor <;> simp [ArrSet]
  . constructor <;> simp [ArrSet]
  . constructor
  . constructor

def YjsEmptyArray {A} : YjsState A := ⟨ #[], ∅ ⟩

def deleteValid {A} [DecidableEq A] (id : YjsId) (state : YjsState A) : YjsState A :=
  deleteById state id

def integrateValidState {A} [DecidableEq A] (input : IntegrateInput A) (state : YjsState A) :
    Except IntegrateError (YjsState A) := do
  integrateSafe input state

def deleteValidState {A} [DecidableEq A] (id : YjsId) (state : YjsState A) : YjsState A :=
  deleteById state id

instance : Message (YjsOperation A) YjsId where
  messageId item := match item with
  | YjsOperation.insert item => item.id
  | YjsOperation.delete id _ => id

instance [DecidableEq A] : WithId (YjsOperation A) YjsId where
  id := YjsOperation.id

def IsValidMessage (state : Array (YjsItem A)) (op : YjsOperation A) : Prop :=
  match op with
  | YjsOperation.insert input =>
    ∃item,
      input.toItem state = Except.ok item ∧
      item.isValid
  | YjsOperation.delete _ _ =>
    True

def IsValidMessageState (state : YjsState A) (op : YjsOperation A) : Prop :=
  IsValidMessage state.items op

instance [DecidableEq A] : Operation (YjsOperation A) where
  State := YjsState A
  Error := IntegrateError
  init := YjsEmptyArray
  effect item state := match item with
  | YjsOperation.insert item => state.insert item
  | YjsOperation.delete _id deletedId =>
    Except.ok <| deleteValid deletedId state

instance [DecidableEq A] : ValidatableOperation (YjsOperation A) where
  isValidState op state := IsValidMessage state op
  StateInv state := YjsStateInvariant state
  stateInv_init := by
    exact YjsArrayInvariant_empty
  stateInv_effect := by
    intro op s s' h_inv h_valid h_effect
    cases op with
    | insert input =>
      simp [IsValidMessage] at h_effect h_valid
      obtain ⟨ item, hitem, hitem_valid ⟩ := h_valid
      apply YjsStateInvariant_insert s s' input h_inv hitem hitem_valid h_effect
    | delete _ deletedId =>
      have hs' : deleteById s deletedId = s' := by
        simpa [Operation.effect, deleteValid] using h_effect
      subst hs'
      simpa [deleteById] using h_inv

instance [DecidableEq A] : ValidMessage (YjsOperation A) where
  isValidMessage state item := IsValidMessage state item

def YjsOperation.UniqueId {A} (op : YjsOperation A) (state : Array (YjsItem A)) : Prop :=
    ∀x ∈ state, x.id.clientId = op.id.clientId → x.id.clock < op.id.clock

def YjsOperation.UniqueIdState {A} (op : YjsOperation A) (state : YjsState A) : Prop :=
  YjsOperation.UniqueId op state.items

structure YjsOperationNetwork A [DecidableEq A] extends OperationNetwork (YjsOperation A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.id.clientId = i
  histories_UniqueId : forall {e i} {array : YjsState A}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 Operation.init = Except.ok array → YjsOperation.UniqueId e array
  /--
  Clocks of operations broadcast by the same client are strictly monotonic:
  if `Broadcast a` precedes `Broadcast b` in client `i`'s history, then `a.id.clock < b.id.clock`.
  Together with `histories_client_id`, this captures the standard Yjs assumption that each
  client uses a strictly increasing local clock for the operations it issues.
  -/
  histories_clock_mono : forall {a b i} {pre mid post : List (Event (YjsOperation A))},
    histories i = pre ++ [Event.Broadcast a] ++ mid ++ [Event.Broadcast b] ++ post →
    a.id.clock < b.id.clock

theorem same_history_not_hb_concurrent {A} [DecidableEq A] {network : CausalNetwork (YjsOperation A)} {i : ClientId} {a b : YjsOperation A} :
  Event.Broadcast a ∈ network.histories i →
  Event.Broadcast b ∈ network.histories i →
  ¬hb_concurrent (hb := instCausalNetworkElemCausalOrder network) a b := by
  intros h_a_mem h_b_mem h_not_hb
  have h_local :
    locallyOrdered network.toNodeHistories i (Event.Broadcast a) (Event.Broadcast b) ∨
    locallyOrdered network.toNodeHistories i (Event.Broadcast b) (Event.Broadcast a) ∨
    a = b := by
    simp [locallyOrdered]
    rw [List.mem_iff_append] at h_a_mem h_b_mem
    have ⟨ s_a, t_a, h_a ⟩ := h_a_mem
    have ⟨ s_b, t_b, h_b ⟩ := h_b_mem
    have h_eq : s_a ++ Event.Broadcast a :: t_a = s_b ++ Event.Broadcast b :: t_b := by
      rw [<-h_a, <-h_b]
    rw [List.append_eq_append_iff] at h_eq
    cases h_eq with
    | inl h_eq =>
      obtain ⟨ as, h_prefix, h_suffix ⟩ := h_eq
      cases as with
      | nil =>
        simp at h_suffix
        grind only [cases eager Subtype]
      | cons hd tl =>
        grind only [=_ List.cons_append, = List.append_assoc, = List.cons_append, →
          List.eq_nil_of_append_eq_nil, cases eager Subtype]
    | inr h_eq =>
      obtain ⟨ as, h_prefix, h_suffix ⟩ := h_eq
      cases as with
      | nil =>
        simp at h_suffix
        grind only [cases eager Subtype]
      | cons hd tl =>
        grind only [=_ List.cons_append, = List.append_assoc, = List.cons_append, →
          List.eq_nil_of_append_eq_nil, cases eager Subtype]
  cases h_local with
  | inl h_ordered =>
    apply HappensBefore.broadcast_broadcast_local at h_ordered
    simp [hb_concurrent, LE.le] at h_not_hb
    grind
  | inr h_ordered =>
    cases h_ordered with
    | inl h_ordered =>
      apply HappensBefore.broadcast_broadcast_local at h_ordered
      simp [hb_concurrent, LE.le] at h_not_hb
      grind
    | inr h_eq =>
      simp [hb_concurrent, LE.le] at h_not_hb
      grind

/-- A successful insert step: the new state is the old one with `input.toItem` inserted at
some position; the deleted set is unchanged. -/
theorem integrateValid_exists_insertIdxIfBounds {A : Type} [inst : DecidableEq A]
  {init : YjsState A} {input : IntegrateInput A}
  {state' : YjsState A} :
  (h_effect : init.insert input = Except.ok state') →
  ∃ i item, item.id = input.id ∧ input.toItem init.items = Except.ok item ∧
    item ∈ state'.items ∧
    state' = { init with items := init.items.insertIdxIfInBounds i item } := by
  intro h_effect
  unfold YjsState.insert integrateSafe at h_effect
  obtain ⟨ newArr, h_safe, h_pure ⟩ := Except.bind_eq_ok_iff.1 h_effect
  split at h_safe
  swap
  · cases h_safe
  unfold integrate at h_safe
  obtain ⟨ leftIdx, h_left, h_safe ⟩ := Except.bind_eq_ok_iff.1 h_safe
  obtain ⟨ rightIdx, h_right, h_safe ⟩ := Except.bind_eq_ok_iff.1 h_safe
  obtain ⟨ destIdx, h_dest, h_safe ⟩ := Except.bind_eq_ok_iff.1 h_safe
  obtain ⟨ item, h_item, h_safe ⟩ := Except.bind_eq_ok_iff.1 h_safe
  simp only [pure, Except.pure, Except.ok.injEq] at h_safe h_pure
  subst h_safe h_pure
  obtain ⟨ leftPtr, h_leftPtr, h_leftIdPtr ⟩ := findLeftIdx_getElemExcept h_left
  obtain ⟨ rightPtr, h_rightPtr, h_rightIdPtr ⟩ := findRightIdx_getElemExcept h_right
  have h_item_def : item = YjsItem.mk leftPtr rightPtr input.id input.content := by
    simp only [mkItemByIndex, h_leftPtr, h_rightPtr, Except.ok_bind, pure, Except.pure,
      Except.ok.injEq] at h_item
    exact h_item.symm
  have h_toItem : input.toItem init.items = Except.ok item :=
    IntegrateInput.toItem_eq_ok_iff.2 ⟨ leftPtr, rightPtr, h_item_def, h_leftIdPtr, h_rightIdPtr ⟩
  have h_dest_le : destIdx ≤ init.items.size :=
    findIntegratedIndex_ok_le_size_from_eq leftIdx rightIdx input init.items destIdx
      (findLeftIdx_bounds h_left).1 (findLeftIdx_bounds h_left).2 (findRightIdx_bounds h_right).2
      h_dest
  refine ⟨ destIdx, item, by rw [h_item_def], h_toItem, ?_, rfl ⟩
  simp [Array.insertIdxIfInBounds, h_dest_le, Array.mem_insertIdx]

def deliverOps {A : Type} (pre : List (Event (YjsOperation A))) : List (YjsOperation A) :=
  pre.filterMap eventDeliver

theorem interpHistory_eq_effect_deliverOps {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))} {state : YjsState A} :
  interpHistory pre Operation.init = Except.ok state →
  effect_list (deliverOps pre) Operation.init = Except.ok state := by
  intro h_interp
  simpa [interpHistory, interpOps, deliverOps] using h_interp

theorem exists_find?_eq_some_of_exists_mem_id {A : Type} [DecidableEq A]
  (arr : Array (YjsItem A)) (targetId : YjsId) (item : YjsItem A) :
  item ∈ arr →
  item.id = targetId →
  uniqueId arr.toList →
  arr.find? (fun i => i.id = targetId) = some item := by
  intro h_mem h_id h_unique
  rw [Array.mem_iff_getElem] at h_mem
  obtain ⟨ i, hi, heq ⟩ := h_mem
  rw [Array.find?_eq_some_iff_getElem]
  refine ⟨ ?_ , ?_ ⟩
  . simp; assumption
  . refine ⟨ i, hi, heq, ?_ ⟩
    simp [uniqueId] at h_unique
    rw [List.pairwise_iff_getElem] at h_unique
    grind

theorem interpOps_ArrSet {A} [DecidableEq A] {items : List (Event (YjsOperation A))} {state init : Operation.State (YjsOperation A)} {x : YjsItem A}:
  interpHistory items init = Except.ok state →
  ArrSet state.toList x →
  (∃y, ArrSet init.toList (YjsPtr.itemPtr y) ∧ y.id = x.id) ∨
  (∃y, y.id = x.id ∧ Event.Deliver (YjsOperation.insert y) ∈ items) := by
  intros h_interp h_in_state
  induction items generalizing init state x with
  | nil =>
    simp [interpHistory, interpOps] at h_interp
    cases h_interp
    simp [ArrSet] at h_in_state |-
    use x
  | cons e items ih =>
    simp [interpHistory, interpOps] at h_interp
    cases e with
    | Broadcast _ =>
      simp [eventDeliver] at h_interp
      apply ih h_interp at h_in_state
      cases h_in_state with
      | inl h_init_mem =>
        left; assumption
      | inr h_in_state =>
        obtain ⟨ y, h_y_val, h_y_mem ⟩ := h_in_state
        right
        use y
        constructor; assumption
        simp; assumption
    | Deliver op =>
      cases op with
      | delete _ deletedId =>
        simp [eventDeliver] at h_interp
        apply ih (x := x) h_interp at h_in_state
        cases h_in_state with
        | inl h =>
          left
          exact h
        | inr h =>
          obtain ⟨ y, h_y_val, h_y_mem ⟩ := h
          right; use y
          simp; constructor; assumption
          assumption
      | insert input =>
        simp [eventDeliver] at h_interp
        generalize h_effect : Operation.effect (YjsOperation.insert input) init = state' at *
        cases state' with
        | error err =>
          cases h_interp
        | ok state' =>
          rw [Except.ok_bind] at h_interp
          apply ih h_interp at h_in_state
          cases h_in_state with
          | inl h_init_mem =>
            simp [Operation.effect] at h_effect
            have ⟨ _, item, h_item_id, _h_toItem, _h_item_mem, h_insert ⟩ :
                ∃ i item, item.id = input.id ∧ input.toItem init.items = Except.ok item ∧
                  item ∈ state'.items ∧
                  state' = { init with items := init.items.insertIdxIfInBounds i item } := by
              apply integrateValid_exists_insertIdxIfBounds h_effect
            rw [h_insert] at h_init_mem
            simp [Array.insertIdxIfInBounds] at h_init_mem
            split at h_init_mem
            . simp [ArrSet] at h_init_mem
              obtain ⟨ y, h_y_mem, h_y_id ⟩ := h_init_mem
              simp [YjsState.toList] at h_y_mem;
              rw [List.mem_insertIdx (by assumption)] at h_y_mem
              cases h_y_mem with
              | inl h_mem =>
                right
                use input
                constructor
                . subst h_mem
                  calc
                    input.id = y.id := by simpa using h_item_id.symm
                    _ = x.id := by simpa using h_y_id
                . simp
                -- grind only
                -- simp
              | inr h_eq =>
                left; use y; constructor; simp [ArrSet, YjsState.toList] at *; assumption
                assumption
            . left; assumption
          | inr h_in_state =>
            obtain ⟨ y, h_y_val, h_y_mem ⟩ := h_in_state
            right; use y
            simp; constructor; assumption
            right; assumption

/-! ## Origin reachability and happens-before

`OriginReachable_HappensBefore` is not needed for the convergence theorem; it records that
an item reachable through origin pointers from a resolved insert was delivered at that
insert's source before its broadcast, hence happens-before it. -/

def IsStateAt {A M} [DecidableEq A] [Operation A] [DecidableEq M] [Message A M] [ValidMessage A] {network : OperationNetwork A} (a : A) (arr : Operation.State A) : Prop :=
  ∃i hist1 hist2, network.histories i = hist1 ++ [Event.Broadcast a] ++ hist2 ∧
    interpHistory hist1 Operation.init = Except.ok arr ∧
    ValidMessage.isValidMessage arr a

theorem OriginReachable_HappensBefore {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {a b : YjsOperation A} {inputA inputB : IntegrateInput A} {itemA itemB : YjsItem A} {state_a state_b : YjsState A}:
  YjsArrInvariant state_a.toList →
  IsStateAt (network := network.toOperationNetwork) a state_a →
  IsStateAt (network := network.toOperationNetwork) b state_b →
  a = YjsOperation.insert inputA →
  b = YjsOperation.insert inputB →
  inputA.toItem state_a = Except.ok itemA →
  inputB.toItem state_b = Except.ok itemB →
  OriginReachable (YjsPtr.itemPtr itemA) (YjsPtr.itemPtr itemB) →
  (instCausalNetworkElemCausalOrder network.toCausalNetwork).le b a := by
  intros h_state_a_inv hstateAtA hstateAtB h_item_a h_item_b htoItemA htoItemB h_reachable
  -- simp [CausalNetwork.toDeliverMessages] at h_b_mem h_a_mem
  -- replace ⟨ a, h_a_mem, h_a_eq ⟩ := h_a_mem
  -- have ⟨ a', h_a_eq ⟩ : ∃ a', Event.Deliver a' = a := by
  --   cases a with
  --   | Deliver it =>
  --     use it
  --   | Broadcast e =>
  --     simp at h_a_eq
  -- subst h_a_eq
  -- replace ⟨ b, h_b_mem, h_b_eq ⟩ := h_b_mem
  -- have ⟨ b', h_b_eq ⟩ : ∃ b', Event.Deliver b' = b := by
  --   cases b with
  --   | Deliver it =>
  --     use it
  --   | Broadcast e =>
  --     simp at h_b_eq
  -- subst h_b_eq
  -- have ⟨ j_a, h_a_mem_history_j_a ⟩ := network.deliver_has_a_cause h_a_mem
  -- have ⟨ j_b, h_b_mem_history_j_b  ⟩ := network.deliver_has_a_cause h_b_mem

  -- rw [List.mem_iff_append] at h_a_mem_history_j_a h_b_mem_history_j_b

  -- obtain ⟨ pre_a, post_a, h_a_history ⟩ := h_a_mem_history_j_a
  -- obtain ⟨ pre_b, post_b, h_b_history ⟩ := h_b_mem_history_j_b

  -- have ⟨ state_a, h_state_a, h_valid_message_a ⟩ : ∃state, interpHistory pre_a Operation.init = Except.ok state ∧ ValidMessage.isValidMessage state a' := by
  --   apply network.broadcast_only_valid_messages (pre := pre_a) (post := post_a) j_a
  --   rw [h_a_history]; simp

  -- have ⟨ state_b, h_state_b, h_valid_message_b ⟩ : ∃state, interpHistory pre_b Operation.init = Except.ok state ∧ ValidMessage.isValidMessage state b' := by
  --   apply network.broadcast_only_valid_messages (pre := pre_b) (post := post_b) j_b
  --   rw [h_b_history]; simp

  obtain ⟨ j_a, pre_a, post_a, h_a_history, h_state_a, h_valid_message_a ⟩ := hstateAtA
  obtain ⟨ j_b, pre_b, post_b, h_b_history, h_state_b, h_valid_message_b ⟩ := hstateAtB

  -- simp at h_a_eq h_b_eq
  -- subst h_a_eq h_b_eq

  -- simp at h_item_a h_item_b
  -- subst a' b'
  simp [ValidMessage.isValidMessage] at h_valid_message_a
  rw [h_item_a] at h_a_history h_valid_message_a
  rw [h_item_b] at h_b_history h_valid_message_b
  obtain ⟨ aItem, haItemDef, haItemValid ⟩ := h_valid_message_a

  generalize h_a_ptr_def : YjsPtr.itemPtr itemA = a_ptr at *

  have h_OriginReachableStep_ArrSet : ∀ x,
    OriginReachableStep a_ptr x → ArrSet state_a.toList x := by
    intros x h_step
    cases h_step with
    | reachable o r id c =>
      simp at h_a_ptr_def
      have h_to_item := (IntegrateInput.toItem_ok_iff inputA state_a itemA h_state_a_inv.unique).1 htoItemA
      obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
      rw [h_a_ptr_def] at hdef
      cases hdef
      cases h_originId : inputA.originId with
      | none =>
        simp [isLeftIdPtr, h_originId] at horigin
        subst horigin
        simp [ArrSet]
      | some pid =>
        simp [isLeftIdPtr, h_originId] at horigin
        obtain ⟨ item, h_eq, h_find ⟩ := horigin
        subst h_eq
        simp [ArrSet]
        simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find
    | reachable_right o r id c =>
      simp at h_a_ptr_def
      have h_to_item := (IntegrateInput.toItem_ok_iff inputA state_a itemA h_state_a_inv.unique).1 htoItemA
      obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
      rw [h_a_ptr_def] at hdef
      cases hdef
      cases h_rightOriginId : inputA.rightOriginId with
      | none =>
        simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
        subst hrightOrigin
        simp [ArrSet]
      | some pid =>
        simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
        obtain ⟨ item, h_eq, h_find ⟩ := hrightOrigin
        subst h_eq
        simp [ArrSet]
        simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find

  have h_b_in_state_a : ArrSet (state_a.toList) itemB := by
    cases h_reachable with
    | reachable_single _ _ h_step =>
      apply h_OriginReachableStep_ArrSet _ h_step
    | reachable_head _ y _ h_step h_reach_tail =>
      apply h_OriginReachableStep_ArrSet at h_step
      have h_closed : IsClosedItemSet (ArrSet state_a.toList) := by
        exact h_state_a_inv.closed
      apply reachable_in _ _ h_closed _ h_reach_tail h_step

  apply interpOps_ArrSet h_state_a at h_b_in_state_a
  cases h_b_in_state_a with
  | inl h_b_in_init =>
    obtain ⟨ y, h_y_init, h_y_id ⟩ := h_b_in_init
    have h_y_nil : y ∈ ([] : List (YjsItem A)) := by
      simp [ArrSet, Operation.init, YjsEmptyArray, YjsState.toList] at h_y_init
    cases h_y_nil
  | inr h_b_in_items =>
    obtain ⟨ item_b', h_b_id_eq,  h_b_in_items_eq ⟩ := h_b_in_items

    rw [List.mem_iff_append] at h_b_in_items_eq
    obtain ⟨ pre_b'', post_b'', h_b_in_items_history ⟩ := h_b_in_items_eq

    right
    apply HappensBefore.broadcast_deliver_local (i := j_a)

    use pre_b'', post_b'', post_a

    rw [h_a_history, h_b_in_items_history]
    simp at *
    have h_b_msg_id_eq : Message.messageId (YjsOperation.insert item_b') = Message.messageId (YjsOperation.insert inputB) := by
      have h_itemB_id : itemB.id = inputB.id :=
        IntegrateInput.toItem_id_eq inputB state_b itemB htoItemB
      calc
        Message.messageId (YjsOperation.insert item_b') = item_b'.id := by rfl
        _ = itemB.id := h_b_id_eq
        _ = inputB.id := h_itemB_id
        _ = Message.messageId (YjsOperation.insert inputB) := by rfl
    have h_item_b'_in_ja : Event.Deliver (YjsOperation.insert item_b') ∈ network.histories j_a := by
      rw [h_a_history, h_b_in_items_history]; simp
    apply network.deliver_has_a_cause at h_item_b'_in_ja
    obtain ⟨ j_b', h_item_b'_in_ja_history ⟩ := h_item_b'_in_ja
    apply network.msg_id_unique (i := j_b') (j := j_b) at h_b_msg_id_eq
    . obtain ⟨ _, h_eq ⟩ := h_b_msg_id_eq
      simp at h_eq
      subst item_b'
      grind only
    . assumption
    . rw [h_b_history]; simp

theorem hb_concurrent_diff_id {A : Type} [inst : DecidableEq A]
  (network : YjsOperationNetwork A) (i : ClientId)
  (a : YjsOperation A)
  (h_a_mem : a ∈ network.toDeliverMessages i)
  (b : YjsOperation A)
  (h_b_mem : b ∈ network.toDeliverMessages i)
  (h_a_b_happens_before : hb_concurrent (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) a b) :
  a.id.clientId ≠ b.id.clientId := by
  intros h_eq
  simp [CausalNetwork.toDeliverMessages] at h_a_mem h_b_mem
  obtain ⟨ a', h_a'_mem, h_a'_pos ⟩ := h_a_mem
  obtain ⟨ b', h_b'_mem, h_b'_pos ⟩ := h_b_mem

  have ⟨ a', h_a ⟩ : ∃ a'', Event.Deliver a'' = a' := by
    cases a' with
    | Deliver it =>
      use it
    | Broadcast e =>
      simp at h_a'_pos

  have ⟨ b', h_b ⟩ : ∃ b'', Event.Deliver b'' = b' := by
    cases b' with
    | Deliver it =>
      use it
    | Broadcast e =>
      simp at h_b'_pos

  subst h_a h_b

  apply network.deliver_has_a_cause at h_a'_mem
  obtain ⟨ i_a, h_a'_mem_hist ⟩ := h_a'_mem
  apply network.deliver_has_a_cause at h_b'_mem
  obtain ⟨ i_b, h_b'_mem_hist ⟩ := h_b'_mem

  have h_i_a_eq_i_b : i_a = i_b := by
    apply network.histories_client_id at h_a'_mem_hist
    apply network.histories_client_id at h_b'_mem_hist
    simp at *
    subst a b
    subst i_a i_b
    assumption

  subst i_a
  simp at *
  subst a b
  apply same_history_not_hb_concurrent h_a'_mem_hist h_b'_mem_hist h_a_b_happens_before

/-- If `input.toItem arr = ok item`, then any origin/rightOrigin step from `item`
    lands in `ArrSet arr.toList`. In other words, both pointers of a freshly resolved
    item refer to elements already present in the array. -/
private theorem toItem_originStep_in_arrSet [DecidableEq A]
    {input : IntegrateInput A} {arr : YjsState A} {item : YjsItem A}
    (h_unique : uniqueId arr.items.toList)
    (h_toItem : input.toItem arr.items = Except.ok item)
    (x : YjsPtr A) (h_step : OriginReachableStep (YjsPtr.itemPtr item) x) :
    ArrSet arr.toList x := by
  have h_to_item := (IntegrateInput.toItem_ok_iff input arr.items item h_unique).1 h_toItem
  obtain ⟨ origin, rightOrigin, id, content, hdef, horigin, hrightOrigin, -, - ⟩ := h_to_item
  cases h_step with
  | reachable o r id' c =>
    cases hdef
    cases h_originId : input.originId with
    | none =>
      simp [isLeftIdPtr, h_originId] at horigin; subst horigin; simp [ArrSet]
    | some pid =>
      simp [isLeftIdPtr, h_originId] at horigin
      obtain ⟨ item', h_eq, h_find ⟩ := horigin; subst h_eq
      simp [ArrSet]; simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find
  | reachable_right o r id' c =>
    cases hdef
    cases h_rightOriginId : input.rightOriginId with
    | none =>
      simp [isRightIdPtr, h_rightOriginId] at hrightOrigin; subst hrightOrigin; simp [ArrSet]
    | some pid =>
      simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
      obtain ⟨ item', h_eq, h_find ⟩ := hrightOrigin; subst h_eq
      simp [ArrSet]; simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find

/-- An item resolved via `toItem` that is origin-reachable from the pre-state
    must already be a member of that pre-state's array. -/
private theorem toItem_reachable_mem [DecidableEq A]
    {input : IntegrateInput A} {arr : YjsState A} {item other : YjsItem A}
    (h_inv : YjsArrInvariant arr.toList)
    (h_toItem : input.toItem arr.items = Except.ok item)
    (h_reach : OriginReachable (YjsPtr.itemPtr item) (YjsPtr.itemPtr other)) :
    other ∈ (show Array (YjsItem A) from arr) := by
  have h_arrset : ArrSet arr.toList (YjsPtr.itemPtr other) := by
    cases h_reach with
    | reachable_single _ _ h_step =>
      exact toItem_originStep_in_arrSet h_inv.unique h_toItem _ h_step
    | reachable_head _ y _ h_step h_reach_tail =>
      have hy := toItem_originStep_in_arrSet h_inv.unique h_toItem _ h_step
      exact reachable_in _ _ h_inv.closed _ h_reach_tail hy
  simpa [ArrSet, YjsState.toList] using h_arrset

/-- If an item is already present in an array, clock safety fails for its id. -/
private theorem isClockSafe_false_of_mem
    {input_id : YjsId} {arr : Array (YjsItem A)} {item : YjsItem A}
    (h_mem : item ∈ arr) (h_id : item.id = input_id) :
    isClockSafe input_id arr = false := by
  unfold isClockSafe; simp
  rw [Array.mem_iff_getElem] at h_mem
  obtain ⟨ i, hi, hget ⟩ := h_mem
  exact ⟨ i, hi, by simp [hget, h_id], by simp [hget, h_id] ⟩

/-- Two items resolved from concurrent insert inputs against the same pre-state
    cannot be origin-reachable from each other. The proof derives a clock-safety
    contradiction: if item₂ were reachable from item₁, then item₂ already existed
    in the pre-state, so its id's clock check would fail — contradicting the
    successful second insert. -/
theorem concurrent_insert_not_reachable [DecidableEq A]
    {input₁ input₂ : IntegrateInput A} {item₁ item₂ : YjsItem A}
    {sa sb : YjsState A}
    (h_inv : YjsArrInvariant sa.toList)
    (h_toItem₁ : input₁.toItem sa.items = Except.ok item₁)
    (h_toItem₂ : input₂.toItem sa.items = Except.ok item₂)
    (h_item₁_valid : item₁.isValid)
    (h_ab : (do let arr₂ ← sa.insert input₁; arr₂.insert input₂) = Except.ok sb) :
    ¬OriginReachable item₁ (YjsPtr.itemPtr item₂) ∧
    ¬OriginReachable item₂ (YjsPtr.itemPtr item₁) := by
  obtain ⟨ arr₂, h_ins₁, h_ins₂ ⟩ := Except.bind_eq_ok_exist h_ab
  have h_ins₁_items : integrateSafe input₁ sa.items = Except.ok arr₂.items := by
    cases hsafe : integrateSafe input₁ sa.items with
    | error err => simp [YjsState.insert, hsafe] at h_ins₁
    | ok arr => simp [YjsState.insert, hsafe] at h_ins₁; cases h_ins₁; simp
  constructor
  · -- item₂ reachable from item₁ ⟹ item₂ ∈ sa ⟹ item₂ ∈ arr₂ ⟹ clock contradiction
    intro h_reach
    have h_mem_sa := toItem_reachable_mem h_inv h_toItem₁ h_reach
    have ⟨ idx, _, h_arr₂_def, _ ⟩ :=
      YjsArrInvariant_integrateSafe input₁ item₁ sa.items arr₂.items h_inv h_toItem₁ h_item₁_valid h_ins₁_items
    have h_mem_arr₂ : item₂ ∈ (show Array (YjsItem A) from arr₂) := by
      rw [h_arr₂_def]
      by_cases hle : idx ≤ Array.size sa.items
      · simp [Array.insertIdxIfInBounds, hle, Array.mem_insertIdx, h_mem_sa]
      · omega
    have h_id₂ := IntegrateInput.toItem_id_eq input₂ sa item₂ h_toItem₂
    have h_clock_false := isClockSafe_false_of_mem h_mem_arr₂ h_id₂
    have h_clock_true : isClockSafe input₂.id arr₂.items = true := by
      simp [YjsState.insert, integrateSafe] at h_ins₂; split at h_ins₂ <;> [assumption; simp at h_ins₂]
    rw [h_clock_false] at h_clock_true; exact absurd h_clock_true (by simp)
  · -- item₁ reachable from item₂ ⟹ item₁ ∈ sa ⟹ clock contradiction on sa directly
    intro h_reach
    have h_mem_sa := toItem_reachable_mem h_inv h_toItem₂ h_reach
    have h_id₁ := IntegrateInput.toItem_id_eq input₁ sa item₁ h_toItem₁
    have h_clock_false := isClockSafe_false_of_mem h_mem_sa h_id₁
    have h_clock_true : isClockSafe input₁.id (show Array (YjsItem A) from sa) = true := by
      simp [YjsState.insert, integrateSafe] at h_ins₁; split at h_ins₁ <;> [assumption; simp at h_ins₁]
    rw [h_clock_false] at h_clock_true; exact absurd h_clock_true (by simp)

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b sa sb h_a_mem h_b_mem h_a_b_happens_before havalid hbvalid hab
  intro h_ab
  cases a with
  | insert aInput =>
    cases b with
    | insert bInput =>
      simp [Operation.effect] at h_ab ⊢
      have h_sa_inv : YjsArrInvariant sa.toList := by
        simpa [ValidatableOperation.StateInv] using havalid
      have h_a_valid_msg : ∃ aItem, aInput.toItem sa = Except.ok aItem ∧ aItem.isValid := by
        simpa [ValidatableOperation.isValidState, IsValidMessage] using hbvalid
      have h_b_valid_msg : ∃ bItem, bInput.toItem sa = Except.ok bItem ∧ bItem.isValid := by
        simpa [ValidatableOperation.isValidState, IsValidMessage] using hab
      obtain ⟨ aItem, h_a_toItem, h_a_item_valid ⟩ := h_a_valid_msg
      obtain ⟨ bItem, h_b_toItem, h_b_item_valid ⟩ := h_b_valid_msg
      have h_diff_client : aInput.id.clientId ≠ bInput.id.clientId :=
        hb_concurrent_diff_id network i
          (a := YjsOperation.insert aInput) h_a_mem
          (b := YjsOperation.insert bInput) h_b_mem
          h_a_b_happens_before
      have h_not_reach :=
        concurrent_insert_not_reachable h_sa_inv h_a_toItem h_b_toItem h_a_item_valid h_ab
      exact insert_commutative aInput bInput aItem bItem sa sb
        h_sa_inv
        h_a_toItem
        h_b_toItem
        h_diff_client
        h_not_reach.1
        h_not_reach.2
        h_a_item_valid
        h_b_item_valid
        h_ab
    | delete _ deletedId =>
      simp [Operation.effect, deleteValid] at *
      rw [insert_deleteById_commutative] at h_ab; assumption
  | delete _ deletedId =>
    cases b with
    | insert bInput =>
      simp [Operation.effect, deleteValid] at *
      rw [insert_deleteById_commutative]; assumption
    | delete _ deletedId' =>
      simp [Operation.effect, deleteValid, bind, Except.bind] at h_ab ⊢
      rw [deleteById_commutative] at h_ab
      exact h_ab

theorem pre_broadcast_lt_insert {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A}
  {i : ClientId}
  {pre post : List (Event (YjsOperation A))}
  {x input : IntegrateInput A} :
  network.histories i = pre ++ Event.Broadcast (YjsOperation.insert input) :: post →
  Event.Broadcast (YjsOperation.insert x) ∈ pre →
  (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
    (YjsOperation.insert x) (YjsOperation.insert input) := by
  intro h_hist h_mem
  rw [List.mem_iff_append] at h_mem
  obtain ⟨ l1, l2, h_pre ⟩ := h_mem
  subst h_pre
  have h_local : locallyOrdered network.toNodeHistories i
      (Event.Broadcast (YjsOperation.insert x))
      (Event.Broadcast (YjsOperation.insert input)) := by
    refine ⟨ l1, l2, post, ?_ ⟩
    simp [h_hist, List.append_assoc]
  exact HappensBefore.broadcast_broadcast_local h_local

theorem pre_deliver_lt_insert {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A}
  {i : ClientId}
  {pre post : List (Event (YjsOperation A))}
  {x input : IntegrateInput A} :
  network.histories i = pre ++ Event.Broadcast (YjsOperation.insert input) :: post →
  Event.Deliver (YjsOperation.insert x) ∈ pre →
  (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
    (YjsOperation.insert x) (YjsOperation.insert input) := by
  intro h_hist h_mem
  rw [List.mem_iff_append] at h_mem
  obtain ⟨ l1, l2, h_pre ⟩ := h_mem
  subst h_pre
  have h_local : locallyOrdered network.toNodeHistories i
      (Event.Deliver (YjsOperation.insert x))
      (Event.Broadcast (YjsOperation.insert input)) := by
    refine ⟨ l1, l2, post, ?_ ⟩
    simp [h_hist, List.append_assoc]
  exact HappensBefore.broadcast_deliver_local h_local

theorem effect_preserves_mem {A : Type} [DecidableEq A]
  (op : YjsOperation A) (s s' : YjsState A) (item : YjsItem A) :
  Operation.effect op s = Except.ok s' →
  item ∈ s.items →
  item ∈ s'.items := by
  intro h_eff h_mem
  cases op with
  | delete _ deletedId =>
    simp [Operation.effect, deleteValid] at h_eff
    subst h_eff
    simpa [deleteById] using h_mem
  | insert input =>
    simp [Operation.effect] at h_eff
    obtain ⟨ i, newItem, _h_new_id, _h_toItem, _h_item_mem, h_s' ⟩ :=
      integrateValid_exists_insertIdxIfBounds (init := s) (input := input) (state' := s') h_eff
    rw [h_s']
    simp [Array.insertIdxIfInBounds]
    split
    · exact (Array.mem_insertIdx (a := item) (b := newItem) (xs := s.items) (h := by assumption)).2 (Or.inr h_mem)
    · simp [*] at h_mem ⊢

theorem effect_list_preserves_mem {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s0 s : YjsState A) (item : YjsItem A) :
  effect_list ops s0 = Except.ok s →
  item ∈ s0.items →
  item ∈ s.items := by
  intro h_eff h_mem
  induction ops generalizing s0 s with
  | nil =>
    simp [effect_list] at h_eff
    cases h_eff
    simpa using h_mem
  | cons op ops ih =>
    simp [effect_list] at h_eff
    obtain ⟨ s1, h_op, h_tail ⟩ := Except.bind_eq_ok_exist h_eff
    have h_mem1 : item ∈ s1.items := effect_preserves_mem op s0 s1 item h_op h_mem
    exact ih (s0 := s1) (s := s) h_tail h_mem1

theorem uniqueId_deleteById {A : Type} [DecidableEq A]
  (s : YjsState A) (deletedId : YjsId) :
  uniqueId s.toList →
  uniqueId (deleteById s deletedId).toList := by
  intro h_unique
  simpa [deleteById, YjsState.toList] using h_unique

/-- Inserting a clock-safe item keeps ids unique: the new id differs from every existing one. -/
theorem insert_preserves_uniqueId {A : Type} [DecidableEq A]
  (s s' : YjsState A) (input : IntegrateInput A) :
  uniqueId s.toList →
  s.insert input = Except.ok s' →
  uniqueId s'.toList := by
  intro h_unique h_insert
  have h_clock : isClockSafe input.id s.items = true := by
    unfold YjsState.insert integrateSafe at h_insert
    obtain ⟨ _, h, - ⟩ := Except.bind_eq_ok_iff.1 h_insert
    split at h
    · assumption
    · cases h
  obtain ⟨ i, item, h_id, -, -, rfl ⟩ := integrateValid_exists_insertIdxIfBounds h_insert
  have h_new : ∀ a ∈ s.items, item.id ≠ a.id := by
    intro a ha heq
    obtain ⟨ k, hk, rfl ⟩ := Array.mem_iff_getElem.1 ha
    simp only [isClockSafe, Array.all_eq_true, decide_eq_true_eq] at h_clock
    have hk' := h_clock k hk
    rw [← h_id, heq] at hk'
    exact lt_irrefl _ (hk' rfl)
  simp only [YjsState.toList] at h_unique ⊢
  unfold Array.insertIdxIfInBounds
  split
  · rename_i h_le
    rw [Array.toList_insertIdx]
    refine List.Pairwise_insertIdx _ _ _ (by simpa using h_le) h_unique ?_ ?_
    · intro j _
      exact (h_new _ (by simp)).symm
    · intro j _ _
      exact h_new _ (by simp)
  · exact h_unique

theorem effect_list_uniqueId_from_IdNoDup {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s : YjsState A) :
  IdNoDup ops →
  effect_list ops Operation.init = Except.ok s →
  uniqueId s.toList := by
  intro h_nodup h_eff
  have h_from_state :
      ∀ {ops : List (YjsOperation A)} {s0 s : YjsState A},
        uniqueId s0.toList → IdNoDup ops → effect_list ops s0 = Except.ok s → uniqueId s.toList := by
    intro ops s0 s h_unique0 h_nodup0 h_eff0
    induction ops generalizing s0 s with
    | nil =>
      simp [effect_list] at h_eff0
      cases h_eff0
      simpa using h_unique0
    | cons op ops ih =>
      simp [effect_list] at h_eff0
      obtain ⟨ s1, h_op, h_tail ⟩ := Except.bind_eq_ok_exist h_eff0
      have h_nodup_tail : IdNoDup ops := by
        simpa [IdNoDup] using (List.pairwise_cons.mp h_nodup0).2
      have h_unique1 : uniqueId s1.toList := by
        cases op with
        | delete _ deletedId =>
          simp [Operation.effect, deleteValid] at h_op
          subst h_op
          exact uniqueId_deleteById s0 deletedId h_unique0
        | insert input =>
          simp [Operation.effect] at h_op
          exact insert_preserves_uniqueId s0 s1 input h_unique0 h_op
      exact ih h_unique1 h_nodup_tail h_tail
  have h_init_unique : uniqueId (Operation.init : Operation.State (YjsOperation A)).toList := by
    simp [Operation.init, YjsEmptyArray, YjsState.toList, uniqueId]
  exact h_from_state h_init_unique h_nodup h_eff

/-- Every item found in a replayed state was created by an insert in the list. -/
theorem effect_list_find?_exists_insert_id {A : Type} [DecidableEq A]
  {ops : List (YjsOperation A)} {state : YjsState A} {id : YjsId} {item : YjsItem A} :
  effect_list ops Operation.init = Except.ok state →
  state.find? (fun i => i.id = id) = some item →
  ∃ input, YjsOperation.insert input ∈ ops ∧ input.id = id := by
  intro h_eff h_find
  have h_mem : item ∈ state.items := Array.mem_of_find?_eq_some h_find
  have h_item_id : item.id = id := Array.find?_id_eq h_find
  subst h_item_id
  clear h_find
  -- An item of the final state is either initial or was inserted along the way.
  suffices h : ∀ (s₀ : YjsState A), effect_list ops s₀ = Except.ok state →
      item ∈ s₀.items ∨ ∃ input, YjsOperation.insert input ∈ ops ∧ input.id = item.id by
    rcases h _ h_eff with h | h
    · simp [Operation.init, YjsEmptyArray] at h
    · exact h
  clear h_eff
  induction ops with
  | nil =>
    intro s₀ h
    simp only [effect_list_nil, Except.ok.injEq] at h
    subst h
    exact Or.inl h_mem
  | cons op ops ih =>
    intro s₀ h
    rw [effect_list_cons, Except.bind_eq_ok_iff] at h
    obtain ⟨ s₁, h_op, h_rest ⟩ := h
    rcases ih s₁ h_rest with h₁ | ⟨ input, hmem, hid ⟩
    · cases op with
      | delete _ _ =>
        simp only [Operation.effect, deleteValid, Except.ok.injEq] at h_op
        subst h_op
        exact Or.inl (by simpa [deleteById] using h₁)
      | insert input =>
        obtain ⟨ i, newItem, h_new_id, -, -, rfl ⟩ :=
          integrateValid_exists_insertIdxIfBounds (by simpa [Operation.effect] using h_op)
        simp only [Array.insertIdxIfInBounds] at h₁
        split at h₁
        · rw [Array.mem_insertIdx] at h₁
          rcases h₁ with rfl | h₁
          · exact Or.inr ⟨ input, by simp, h_new_id.symm ⟩
          · exact Or.inl h₁
        · exact Or.inl h₁
    · exact Or.inr ⟨ input, by simp [hmem], hid ⟩

theorem toDeliver_mem_of_deliver_mem {A : Type} [DecidableEq A]
  (network : CausalNetwork (YjsOperation A)) (i : ClientId) (m : YjsOperation A) :
  Event.Deliver m ∈ network.histories i →
  m ∈ network.toDeliverMessages i := by
  intro h_mem
  simp [CausalNetwork.toDeliverMessages]
  exact ⟨ Event.Deliver m, h_mem, by simp ⟩

theorem deliver_mem_of_toDeliver_mem {A : Type} [DecidableEq A]
  (network : CausalNetwork (YjsOperation A)) (i : ClientId) (m : YjsOperation A) :
  m ∈ network.toDeliverMessages i →
  Event.Deliver m ∈ network.histories i := by
  intro h_mem
  simp [CausalNetwork.toDeliverMessages] at h_mem
  obtain ⟨ ev, h_ev_mem, h_ev_eq ⟩ := h_mem
  cases ev with
  | Broadcast _ =>
    simp at h_ev_eq
  | Deliver m' =>
    simp at h_ev_eq
    subst h_ev_eq
    exact h_ev_mem

theorem hbClosed_prefix {A : Type} [DecidableEq A]
  {hb : CausalOrder A} {ops₀ ops₁ : List A} :
  hbClosed hb (ops₀ ++ ops₁) →
  hbClosed hb ops₀ := by
  intro h_closed x y l₁ l₂ h_eq h_lt
  apply h_closed x y l₁ (l₂ ++ ops₁)
  · simp [List.append_assoc, h_eq]
  · exact h_lt

theorem toDeliverMessages_hbClosed {A : Type} [DecidableEq A]
  (network : YjsOperationNetwork A) (i : ClientId) :
  hbClosed (instCausalNetworkElemCausalOrder network.toCausalNetwork)
    (network.toCausalNetwork.toDeliverMessages i) := by
  let hb : CausalOrder (YjsOperation A) := instCausalNetworkElemCausalOrder network.toCausalNetwork
  change hbClosed hb (network.toCausalNetwork.toDeliverMessages i)
  have h_consistent_i : hb_consistent hb (network.toCausalNetwork.toDeliverMessages i) := by
    simpa [hb] using (hb_consistent_local_history (network := network.toCausalNetwork) (i := i))
  intro a b l₁ l₂ h_eq h_b_lt_a
  have h_a_mem : a ∈ network.toCausalNetwork.toDeliverMessages i := by
    rw [h_eq]
    simp
  have h_deliver_a_mem : Event.Deliver a ∈ network.toCausalNetwork.histories i := by
    exact deliver_mem_of_toDeliver_mem (network := network.toCausalNetwork) (i := i) (m := a) h_a_mem
  have h_local :
      locallyOrdered network.toCausalNetwork.toNodeHistories i (Event.Deliver b) (Event.Deliver a) := by
    exact network.toCausalNetwork.causal_delivery h_deliver_a_mem h_b_lt_a
  have h_deliver_b_mem : Event.Deliver b ∈ network.toCausalNetwork.histories i := by
    obtain ⟨ pre, mid, post, h_hist_eq ⟩ := h_local
    rw [h_hist_eq]
    simp
  have h_b_mem : b ∈ network.toCausalNetwork.toDeliverMessages i := by
    exact toDeliver_mem_of_deliver_mem (network := network.toCausalNetwork) (i := i) (m := b) h_deliver_b_mem
  have h_cons_suffix : hb_consistent hb (a :: l₂) := by
    apply hb_consistent_sublist (hb := hb) h_consistent_i
    rw [h_eq]
    simp
  have h_not_b_in_l₂ : b ∉ l₂ := by
    intro h_b_in_l₂
    cases h_cons_suffix with
    | cons _ _ _ h_no_lt =>
      exact h_no_lt b h_b_in_l₂ (le_of_lt h_b_lt_a)
  rw [h_eq] at h_b_mem
  simp [List.mem_append] at h_b_mem
  rcases h_b_mem with h_b_in_l₁ | h_b_eq_a | h_b_in_l₂
  · exact h_b_in_l₁
  · subst h_b_eq_a
    exfalso
    exact lt_irrefl _ h_b_lt_a
  · exfalso
    exact h_not_b_in_l₂ h_b_in_l₂

theorem toDeliverMessages_IdNoDup {A : Type} [DecidableEq A]
  (network : YjsOperationNetwork A) (i : ClientId) :
  IdNoDup (network.toCausalNetwork.toDeliverMessages i) := by
  have h_noDup_i : (network.toCausalNetwork.toDeliverMessages i).Nodup := by
    exact toDeliverMessages_Nodup (network := network.toCausalNetwork) (i := i)
  have h_op_id_eq_msg_id : ∀ op : YjsOperation A, WithId.id op = Message.messageId op := by
    intro op
    cases op <;> rfl
  unfold IdNoDup
  rw [List.pairwise_iff_getElem]
  intro idx₁ idx₂ h_idx₁ h_idx₂ h_idx_lt h_id_eq
  have h_pairwise_ne_i : List.Pairwise (fun x y => x ≠ y) (network.toCausalNetwork.toDeliverMessages i) := by
    simpa [List.nodup_iff_pairwise_ne] using h_noDup_i
  rw [List.pairwise_iff_getElem] at h_pairwise_ne_i
  have h_msg_id_eq :
      Message.messageId (network.toCausalNetwork.toDeliverMessages i)[idx₁] =
        Message.messageId (network.toCausalNetwork.toDeliverMessages i)[idx₂] := by
    rw [←h_op_id_eq_msg_id (network.toCausalNetwork.toDeliverMessages i)[idx₁]]
    rw [←h_op_id_eq_msg_id (network.toCausalNetwork.toDeliverMessages i)[idx₂]]
    exact h_id_eq
  have h_deliver_mem₁ :
      Event.Deliver (network.toCausalNetwork.toDeliverMessages i)[idx₁] ∈
        network.toCausalNetwork.histories i := by
    apply deliver_mem_of_toDeliver_mem (network := network.toCausalNetwork) (i := i)
    exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages i) (h := h_idx₁)
  have h_deliver_mem₂ :
      Event.Deliver (network.toCausalNetwork.toDeliverMessages i)[idx₂] ∈
        network.toCausalNetwork.histories i := by
    apply deliver_mem_of_toDeliver_mem (network := network.toCausalNetwork) (i := i)
    exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages i) (h := h_idx₂)
  obtain ⟨ c₁, h_broadcast_mem₁ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₁
  obtain ⟨ c₂, h_broadcast_mem₂ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₂
  have h_op_eq :
      (network.toCausalNetwork.toDeliverMessages i)[idx₁] =
        (network.toCausalNetwork.toDeliverMessages i)[idx₂] := by
    exact (network.toCausalNetwork.msg_id_unique h_broadcast_mem₁ h_broadcast_mem₂ h_msg_id_eq).2
  exact h_pairwise_ne_i idx₁ idx₂ h_idx₁ h_idx₂ h_idx_lt h_op_eq

/-! ## Replaying operation lists

The state reached by replaying a list of operations is analysed through two facts:
items are never removed (`effect_list_preserves_mem`), and an item found by id was
created by the unique insert with that id in the list
(`effect_list_find?_exists_insert_id`, `ReplayPrefix.find?_of_mem`).  Together with
`IntegrateInput.toItem_congr` this gives *replay determinism*
(`toItem_deterministic`): the item an insert resolves to does not depend on which
valid replay produced the state.  Causal validity (`isValidState_insert_causally`)
is the instance of determinism comparing the broadcasting client's state with the
state of any causally closed replay. -/

/-- An operation is *sourced* when some client broadcast it. -/
abbrev YjsOperationNetwork.Sourced {A : Type} [DecidableEq A] (network : YjsOperationNetwork A)
    (op : YjsOperation A) : Prop :=
  ∃ i, Event.Broadcast op ∈ network.histories i

/-- The causal order of a Yjs operation network. -/
abbrev YjsOperationNetwork.hb {A : Type} [DecidableEq A] (network : YjsOperationNetwork A) :
    CausalOrder (YjsOperation A) :=
  instCausalNetworkElemCausalOrder network.toCausalNetwork

theorem YjsOperation.messageId_eq (op : YjsOperation A) : Message.messageId op = op.id := by
  cases op <;> rfl

/-- Sourced operations are determined by their id (network axiom `msg_id_unique`). -/
theorem YjsOperationNetwork.sourced_id_unique {A : Type} [DecidableEq A]
    (network : YjsOperationNetwork A) {a b : YjsOperation A}
    (ha : network.Sourced a) (hb : network.Sourced b) (h : a.id = b.id) : a = b := by
  obtain ⟨ i, hi ⟩ := ha
  obtain ⟨ j, hj ⟩ := hb
  exact (network.toCausalNetwork.msg_id_unique hi hj
    (by rw [YjsOperation.messageId_eq, YjsOperation.messageId_eq]; exact h)).2

theorem mem_deliverOps {pre : List (Event (YjsOperation A))} {a : YjsOperation A} :
    a ∈ deliverOps pre ↔ Event.Deliver a ∈ pre := by
  unfold deliverOps
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨ ev, hmem, hev ⟩
    cases ev <;> simp [eventDeliver] at hev
    subst hev
    exact hmem
  · intro h
    exact ⟨ _, h, rfl ⟩

theorem deliverOps_append (l₁ l₂ : List (Event (YjsOperation A))) :
    deliverOps (l₁ ++ l₂) = deliverOps l₁ ++ deliverOps l₂ := by
  simp [deliverOps]

theorem toDeliverMessages_eq_deliverOps {A : Type} [DecidableEq A]
    (network : CausalNetwork (YjsOperation A)) (i : ClientId) :
    network.toDeliverMessages i = deliverOps (network.histories i) := by
  unfold CausalNetwork.toDeliverMessages deliverOps
  rfl

/-- The broadcast state of a sourced insert: the state of the broadcasting client just
before the broadcast, at which the input is valid
(network axiom `broadcast_only_valid_messages`). -/
theorem YjsOperationNetwork.source_state {A : Type} [DecidableEq A]
    (network : YjsOperationNetwork A) {op : IntegrateInput A}
    (h : network.Sourced (YjsOperation.insert op)) :
    ∃ (j : ClientId) (pre post : List (Event (YjsOperation A))) (s₀ : YjsState A)
      (item₀ : YjsItem A),
      network.histories j = pre ++ Event.Broadcast (YjsOperation.insert op) :: post ∧
      effect_list (deliverOps pre) Operation.init = Except.ok s₀ ∧
      op.toItem s₀.items = Except.ok item₀ ∧ item₀.isValid := by
  obtain ⟨ j, hmem ⟩ := h
  obtain ⟨ pre, post, hhist ⟩ := List.mem_iff_append.1 hmem
  obtain ⟨ s₀, hs₀, hvalid ⟩ := network.broadcast_only_valid_messages j (pre := pre)
    (post := post) (e := YjsOperation.insert op) (by simpa using hhist.symm)
  obtain ⟨ item₀, hitem, hvalid ⟩ : ∃ item, op.toItem s₀.items = Except.ok item ∧ item.isValid := by
    simpa [ValidMessage.isValidMessage, IsValidMessage] using hvalid
  exact ⟨ j, pre, post, s₀, item₀, hhist, interpHistory_eq_effect_deliverOps hs₀, hitem, hvalid ⟩

/-- The dependencies of a sourced insert are sourced causal predecessors: each dependency
id is the id of an insert delivered at the source before the broadcast. -/
theorem YjsOperationNetwork.deps_hb {A : Type} [DecidableEq A]
    (network : YjsOperationNetwork A) {op : IntegrateInput A}
    (h : network.Sourced (YjsOperation.insert op)) {oid : YjsId} (hoid : oid ∈ op.depIds) :
    ∃ o : IntegrateInput A, o.id = oid ∧ network.Sourced (YjsOperation.insert o) ∧
      network.hb.lt (YjsOperation.insert o) (YjsOperation.insert op) := by
  obtain ⟨ j, pre, post, s₀, item₀, hhist, hs₀, hitem, - ⟩ := network.source_state h
  obtain ⟨ x, hx ⟩ := IntegrateInput.toItem_find?_dep hitem hoid
  obtain ⟨ o, hmem, hid ⟩ := effect_list_find?_exists_insert_id hs₀ hx
  have hdel : Event.Deliver (YjsOperation.insert o) ∈ pre := mem_deliverOps.1 hmem
  refine ⟨ o, hid, ?_, pre_deliver_lt_insert hhist hdel ⟩
  exact network.toCausalNetwork.deliver_has_a_cause (by rw [hhist]; exact List.mem_append_left _ hdel)

/-- A *replay prefix* for the insert `op`: `s` is the state reached by replaying a list `L`
that is hb-closed and duplicate-free and contains a sourced insert for each dependency id of
`op`.  Both the broadcasting client's state and any causally closed replay containing the
predecessors of `op` are replay prefixes for `op`. -/
structure ReplayPrefix {A : Type} [DecidableEq A] (network : YjsOperationNetwork A)
    (L : List (YjsOperation A)) (op : IntegrateInput A) (s : YjsState A) : Prop where
  closed : hbClosed network.hb L
  nodup : IdNoDup L
  deps : ∀ oid ∈ op.depIds, ∃ o : IntegrateInput A,
    o.id = oid ∧ network.Sourced (YjsOperation.insert o) ∧ YjsOperation.insert o ∈ L
  replay : effect_list L Operation.init = Except.ok s

namespace ReplayPrefix

variable {A : Type} [DecidableEq A] {network : YjsOperationNetwork A}
  {L : List (YjsOperation A)} {op : IntegrateInput A} {s : YjsState A}

theorem uniqueId (h : ReplayPrefix network L op s) : uniqueId s.toList :=
  effect_list_uniqueId_from_IdNoDup L s h.nodup h.replay

/-- The part of a replay before a sourced member insert `o` is a replay prefix for `o`, and
the item created there for `o` is the item found under `o.id` in the final state. -/
theorem find?_of_mem (h : ReplayPrefix network L op s) {o : IntegrateInput A}
    (hsrc : network.Sourced (YjsOperation.insert o)) (hmem : YjsOperation.insert o ∈ L) :
    ∃ (L₀ : List (YjsOperation A)) (s₀ : YjsState A) (x : YjsItem A),
      L₀.length < L.length ∧ ReplayPrefix network L₀ o s₀ ∧
      o.toItem s₀.items = Except.ok x ∧ s.items.find? (fun i => i.id = o.id) = some x := by
  obtain ⟨ L₀, L₁, rfl ⟩ := List.mem_iff_append.1 hmem
  have hrep := h.replay
  rw [effect_list_append, Except.bind_eq_ok_iff] at hrep
  obtain ⟨ s₀, hs₀, hrest ⟩ := hrep
  rw [effect_list_cons, Except.bind_eq_ok_iff] at hrest
  obtain ⟨ s₁, hstep, hs ⟩ := hrest
  obtain ⟨ _, x, -, hx, hx_mem, - ⟩ :=
    integrateValid_exists_insertIdxIfBounds (by simpa [Operation.effect] using hstep)
  refine ⟨ L₀, s₀, x, by simp, ?_, hx, ?_ ⟩
  · exact {
      closed := hbClosed_prefix (ops₁ := YjsOperation.insert o :: L₁) h.closed
      nodup := List.Pairwise.sublist (List.sublist_append_left _ _) h.nodup
      deps := fun oid hoid => by
        obtain ⟨ o', hid, hsrc', hlt ⟩ := network.deps_hb hsrc hoid
        exact ⟨ o', hid, hsrc', h.closed _ _ L₀ L₁ rfl hlt ⟩
      replay := hs₀ }
  · exact exists_find?_eq_some_of_exists_mem_id _ _ _
      (effect_list_preserves_mem L₁ s₁ s x hs hx_mem)
      (IntegrateInput.toItem_id_eq o s₀.items x hx) (by simpa [YjsState.toList] using h.uniqueId)

end ReplayPrefix

/-- **Replay determinism.**  Two replay prefixes for the same insert resolve it to the same
item.  By `IntegrateInput.toItem_congr` it suffices that the two states agree on the items
found under the dependency ids; each such item was created by the (unique, sourced) insert
with that id, which both replays contain, and the claim follows by induction on the length
of the first replay. -/
theorem toItem_deterministic {A : Type} [DecidableEq A] (network : YjsOperationNetwork A) :
    ∀ (n : ℕ) {L₁ L₂ : List (YjsOperation A)} {op : IntegrateInput A} {s₁ s₂ : YjsState A}
      {item : YjsItem A},
      L₁.length = n →
      ReplayPrefix network L₁ op s₁ → ReplayPrefix network L₂ op s₂ →
      op.toItem s₁.items = Except.ok item → op.toItem s₂.items = Except.ok item := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L₁ L₂ op s₁ s₂ item hlen h₁ h₂ hitem
  rw [← hitem]
  apply IntegrateInput.toItem_congr
  intro oid hoid
  obtain ⟨ o, rfl, hsrc, hmem₁ ⟩ := h₁.deps oid hoid
  have hmem₂ : YjsOperation.insert o ∈ L₂ := by
    obtain ⟨ o', hid', hsrc', hmem₂' ⟩ := h₂.deps o.id hoid
    have := network.sourced_id_unique hsrc' hsrc hid'
    cases this
    exact hmem₂'
  obtain ⟨ L₁₀, s₁₀, x₁, hlen₁, h₁₀, hx₁, hf₁ ⟩ := h₁.find?_of_mem hsrc hmem₁
  obtain ⟨ L₂₀, s₂₀, x₂, -, h₂₀, hx₂, hf₂ ⟩ := h₂.find?_of_mem hsrc hmem₂
  rw [hf₁, hf₂]
  have := ih L₁₀.length (by omega) rfl h₁₀ h₂₀ hx₁
  exact congrArg some (Except.ok.inj (this.symm.trans hx₂)).symm

/-- The deliveries of a client before one of its broadcasts form an hb-closed,
duplicate-free list. -/
theorem YjsOperationNetwork.deliverOps_pre_valid {A : Type} [DecidableEq A]
    (network : YjsOperationNetwork A) {j : ClientId} {e : YjsOperation A}
    {pre post : List (Event (YjsOperation A))}
    (hhist : network.histories j = pre ++ Event.Broadcast e :: post) :
    hbClosed network.hb (deliverOps pre) ∧ IdNoDup (deliverOps pre) := by
  have hsplit : network.toCausalNetwork.toDeliverMessages j = deliverOps pre ++ deliverOps post := by
    rw [toDeliverMessages_eq_deliverOps, hhist, ← List.singleton_append, ← List.append_assoc,
      deliverOps_append, deliverOps_append]
    simp [deliverOps, eventDeliver]
  constructor
  · have := toDeliverMessages_hbClosed network j
    rw [hsplit] at this
    exact hbClosed_prefix this
  · have := toDeliverMessages_IdNoDup network j
    rw [hsplit] at this
    exact List.Pairwise.sublist (List.sublist_append_left _ _) this

/-- **Causal validity.**  An insert that was valid when broadcast is valid at the state of any
hb-consistent, hb-closed, duplicate-free replay containing all of its causal predecessors:
by replay determinism both states resolve the insert to the same item, and validity is a
property of that item. -/
theorem isValidState_insert_causally {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A}
  (input : IntegrateInput A)
  (s : Operation.State (YjsOperation A))
  (l : List (YjsOperation A)) :
  (∃ i, Event.Broadcast (YjsOperation.insert input) ∈ network.histories i) →
  (∀ x, (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt x (YjsOperation.insert input) → x ∈ l) →
  hb_consistent (instCausalNetworkElemCausalOrder network.toCausalNetwork) l →
  hbClosed (instCausalNetworkElemCausalOrder network.toCausalNetwork) l →
  effect_list l Operation.init = Except.ok s →
  IdNoDup l →
  ∃ item, input.toItem s = Except.ok item ∧ item.isValid := by
  intro h_source h_lt _ h_closed h_effect h_nodup
  obtain ⟨ j, pre, post, s₀, item₀, hhist, hs₀, hitem₀, hvalid₀ ⟩ := network.source_state h_source
  refine ⟨ item₀, ?_, hvalid₀ ⟩
  obtain ⟨ h_pre_closed, h_pre_nodup ⟩ := network.deliverOps_pre_valid hhist
  have h_src : ReplayPrefix network (deliverOps pre) input s₀ := {
    closed := h_pre_closed
    nodup := h_pre_nodup
    deps := fun oid hoid => by
      obtain ⟨ x, hx ⟩ := IntegrateInput.toItem_find?_dep hitem₀ hoid
      obtain ⟨ o, hmem, hid ⟩ := effect_list_find?_exists_insert_id hs₀ hx
      refine ⟨ o, hid, ?_, hmem ⟩
      exact network.toCausalNetwork.deliver_has_a_cause
        (by rw [hhist]; exact List.mem_append_left _ (mem_deliverOps.1 hmem))
    replay := hs₀ }
  have h_l : ReplayPrefix network l input s := {
    closed := h_closed
    nodup := h_nodup
    deps := fun oid hoid => by
      obtain ⟨ o, hid, hsrc, hlt ⟩ := network.deps_hb h_source hoid
      exact ⟨ o, hid, hsrc, h_lt _ hlt ⟩
    replay := h_effect }
  exact toItem_deterministic network _ rfl h_src h_l hitem₀

theorem YjsOperationNetwork_converge' {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsState A) :
  let hist_i := network.toDeliverMessages i
  let hist_j := network.toDeliverMessages j
  interpOps hist_i Operation.init = Except.ok res₀ →
  interpOps hist_j Operation.init = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
  := by
  intros hist_i hist_j h_res₀ h_res₁ h_hist_mem

  subst hist_i hist_j

  let hb : CausalOrder (YjsOperation A) := instCausalNetworkElemCausalOrder network.toCausalNetwork

  have h_deliver_mem : ∀ {k : ClientId} {m : YjsOperation A},
      m ∈ network.toCausalNetwork.toDeliverMessages k →
        Event.Deliver m ∈ network.toCausalNetwork.histories k := by
    intro k m h_mem
    simp [CausalNetwork.toDeliverMessages] at h_mem
    obtain ⟨ ev, h_ev_mem, h_ev_eq ⟩ := h_mem
    cases ev with
    | Broadcast _ => simp at h_ev_eq
    | Deliver m' => simp at h_ev_eq; subst h_ev_eq; simpa using h_ev_mem

  let StateSource : YjsOperation A → Prop := fun a => ∃ i, Event.Broadcast a ∈ network.toCausalNetwork.histories i
  haveI : CausallyValidatableOperation (A := YjsOperation A) (S := YjsId) (hb := hb) StateSource := {
    isValidState_of_history := by
      intro a s l h_source h_lt h_consistent h_closed h_effect h_nodup
      cases a with
      | delete _ _ => simp [ValidatableOperation.isValidState, IsValidMessage]
      | insert input =>
        simpa [ValidatableOperation.isValidState, IsValidMessage] using
          isValidState_insert_causally (network := network) (input := input) (s := s) (l := l)
            h_source h_lt h_consistent h_closed h_effect h_nodup
  }

  have h := hb_consistent_effect_convergent (s := res₀) (hb := hb) StateSource
    (network.toCausalNetwork.toDeliverMessages i)
    (network.toCausalNetwork.toDeliverMessages j)
    (fun x hx => let ⟨ c, h ⟩ := network.toCausalNetwork.deliver_has_a_cause (h_deliver_mem hx); ⟨ c, h ⟩)
    (fun x hx => let ⟨ c, h ⟩ := network.toCausalNetwork.deliver_has_a_cause (h_deliver_mem hx); ⟨ c, h ⟩)
    (hb_consistent_local_history (network := network.toCausalNetwork) (i := i))
    (hb_consistent_local_history (network := network.toCausalNetwork) (i := j))
    (toDeliverMessages_hbClosed (network := network) (i := i))
    (toDeliverMessages_hbClosed (network := network) (i := j))
    (YjsOperationNetwork_concurrentCommutative network i)
    (toDeliverMessages_IdNoDup (network := network) (i := i))
    (toDeliverMessages_IdNoDup (network := network) (i := j))
    h_hist_mem
    h_res₀

  have h_res_ok_eq : Except.ok (ε := IntegrateError) res₀ = Except.ok res₁ := by
    rw [<-h_res₀, <-h_res₁]
    simp [interpOps] at *
    rw [h, h_res₀]

  cases h_res_ok_eq
  simp
end YjsNetwork
