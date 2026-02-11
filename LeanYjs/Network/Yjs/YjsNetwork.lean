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
      have hs' : s' = deleteById s deletedId := by
        simpa [deleteValid] using h_effect.symm
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

theorem Subtype_eq_of_val {α : Type} {P : α → Prop} {x y : { a : α // P a }} : x.val = y.val → x = y := by
  intros h
  cases x; cases y
  simp at h
  congr

theorem Except.map_eq_eq {α β ε : Type} (f : α → β) {e1 e2 : Except ε α} :
  (∀x y, f x = f y → x = y) →
  f <$> e1 = f <$> e2
  → e1 = e2 := by
  intro h_f h_eq
  cases e1 with
  | error err1 =>
    cases e2 with
    | error err2 =>
      simp at h_eq
      rw [h_eq]
    | ok val2 =>
      simp at h_eq
  | ok val1 =>
    cases e2 with
    | error err2 =>
      simp at h_eq
    | ok val2 =>
      simp at h_eq
      have h_val_eq : val1 = val2 := h_f val1 val2 h_eq
      rw [h_val_eq]

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

theorem integrateValid_exists_insertIdxIfBounds {A : Type} [inst : DecidableEq A]
  {init : YjsState A} {input : IntegrateInput A}
  {state' : YjsState A} :
  (h_effect : init.insert input = Except.ok state') →
  ∃ i item, item.id = input.id ∧ state' = { init with items := init.items.insertIdxIfInBounds i item } := by
  intro h_effect
  have h_integrate : integrate input init.items = Except.ok state'.items := by
    unfold YjsState.insert at h_effect
    simp [integrateSafe] at h_effect
    split at h_effect
    · cases heq : integrate input init.items with
      | error err =>
        simp [heq] at h_effect
      | ok items' =>
        simp [heq] at h_effect
        subst h_effect
        rfl
    · simp at h_effect
  obtain ⟨ leftIdx, h_leftIdx, h1 ⟩ := Except.bind_eq_ok_exist h_integrate
  obtain ⟨ rightIdx, h_rightIdx, h2 ⟩ := Except.bind_eq_ok_exist h1
  obtain ⟨ destIdx, h_destIdx, h3 ⟩ := Except.bind_eq_ok_exist h2
  obtain ⟨ item', h_item', h4 ⟩ := Except.bind_eq_ok_exist h3
  have h_state' : state'.items = init.items.insertIdxIfInBounds destIdx item' := by
    simp [pure, Except.pure] at h4
    grind
  have h_item_id : item'.id = input.id := by
    cases hleft : getPtrExcept init.items leftIdx with
    | error err =>
      simp [mkItemByIndex, hleft] at h_item'
      cases h_item'
    | ok leftPtr =>
      cases hright : getPtrExcept init.items rightIdx with
      | error err =>
        simp [mkItemByIndex, hleft, hright] at h_item'
        cases h_item'
      | ok rightPtr =>
        have h_item_eq := h_item'
        rw [mkItemByIndex, hleft, hright] at h_item_eq
        simp [bind, Except.bind] at h_item_eq
        have h_item_def : item' = YjsItem.mk leftPtr rightPtr input.id input.content := by
          cases h_item_eq
          rfl
        simp [h_item_def]
  have hdeleted : state'.deletedIds = init.deletedIds := by
    simp [YjsState.insert] at h_effect
    cases heq : integrateSafe input init.items with
      | error err =>
        simp [heq] at h_effect
      | ok items' =>
        simp [heq] at h_effect
        subst h_effect
        rfl
  refine ⟨ destIdx, item', h_item_id, ?_ ⟩
  obtain ⟨ _, _ ⟩ := state'
  grind

theorem IntegrateInput.toItem_id_eq {A : Type} [DecidableEq A]
  (input : IntegrateInput A) (arr : Array (YjsItem A)) (item : YjsItem A) :
  input.toItem arr = Except.ok item →
  item.id = input.id := by
  intro h
  unfold IntegrateInput.toItem at h
  cases h_originId : input.originId with
  | none =>
    simp [h_originId] at h
    cases h_rightOriginId : input.rightOriginId with
    | none =>
      simp [h_rightOriginId] at h
      cases h
      rfl
    | some rid =>
      simp [h_rightOriginId] at h
      cases h_find : arr.find? (fun item_1 => item_1.id = rid) with
      | none =>
        simp [h_find] at h
        cases h
      | some rightItem =>
        simp [h_find] at h
        cases h
        rfl
  | some oid =>
    simp [h_originId] at h
    cases h_find_origin : arr.find? (fun item_1 => item_1.id = oid) with
    | none =>
      simp [h_find_origin] at h
      cases h
    | some originItem =>
      simp [h_find_origin] at h
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        simp [h_rightOriginId] at h
        cases h
        rfl
      | some rid =>
        simp [h_rightOriginId] at h
        cases h_find_right : arr.find? (fun item_1 => item_1.id = rid) with
        | none =>
          simp [h_find_right] at h
          cases h
        | some rightItem =>
          simp [h_find_right] at h
          cases h
          rfl

theorem IntegrateInput.toItem_deleteById_ok {A : Type} [DecidableEq A]
  (input : IntegrateInput A) (arr : YjsState A) (item : YjsItem A) (deletedId : YjsId) :
  input.toItem arr.items = Except.ok item →
  input.toItem (deleteById arr deletedId) = Except.ok item := by
  intro h
  simp [IntegrateInput.toItem] at *
  assumption

theorem exists_find?_eq_some_of_exists_mem_id {A : Type} [DecidableEq A]
  (arr : Array (YjsItem A)) (targetId : YjsId) :
  (∃ item, item ∈ arr ∧ item.id = targetId) →
  ∃ item, arr.find? (fun i => i.id = targetId) = some item := by
  intro h_exists
  by_cases h_none : arr.find? (fun i => i.id = targetId) = none
  · rw [Array.find?_eq_none] at h_none
    obtain ⟨ item, h_mem, h_id ⟩ := h_exists
    have h_false := h_none item h_mem
    simp [h_id] at h_false
  · cases h_find : arr.find? (fun i => i.id = targetId) with
    | none =>
      contradiction
    | some item =>
      exact ⟨ item, rfl ⟩

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
      simp at h_interp
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
        simp at h_interp
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
        simp at h_interp
        generalize h_effect : Operation.effect (YjsOperation.insert input) init = state' at *
        cases state' with
        | error err =>
          cases h_interp
        | ok state' =>
          rw [ok_bind] at h_interp
          apply ih h_interp at h_in_state
          cases h_in_state with
          | inl h_init_mem =>
            simp [Operation.effect] at h_effect
            have ⟨ _, item, h_item_id, h_insert ⟩ : ∃ i item, item.id = input.id ∧ state' = { init with items := init.items.insertIdxIfInBounds i item } := by
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

theorem interpHistory_find?_exists_deliver_insert {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))}
  {state : YjsState A}
  {id : YjsId}
  {item : YjsItem A} :
  interpHistory pre Operation.init = Except.ok state →
  state.find? (fun i => i.id = id) = some item →
  ∃ input, Event.Deliver (YjsOperation.insert input) ∈ pre ∧ input.id = id := by
  intro h_interp h_find
  have h_item_mem : item ∈ state := Array.mem_of_find?_eq_some h_find
  have h_ptr_in : ArrSet state.toList (YjsPtr.itemPtr item) := by
    simpa [ArrSet] using h_item_mem
  have h_from_interp := interpOps_ArrSet (A := A) (items := pre)
    (state := state) (init := Operation.init) (x := item) h_interp h_ptr_in
  cases h_from_interp with
  | inl h_in_init =>
    obtain ⟨ y, h_y_init, h_y_id ⟩ := h_in_init
    simp [ArrSet, Operation.init, YjsEmptyArray] at h_y_init
  | inr h_in_pre =>
    obtain ⟨ input, h_input_id, h_input_mem ⟩ := h_in_pre
    have h_item_id : item.id = id := by
      rw [Array.find?_eq_some_iff_getElem] at h_find
      simpa using h_find.1
    refine ⟨ input, h_input_mem, ?_ ⟩
    exact h_input_id.trans h_item_id

def IsStateAt {A M} [DecidableEq A] [Operation A] [DecidableEq M] [Message A M] [ValidMessage A] {network : OperationNetwork A} (a : A) (arr : Operation.State A) : Prop :=
  ∃i hist1 hist2, network.histories i = hist1 ++ [Event.Broadcast a] ++ hist2 ∧
    interpHistory hist1 Operation.init = Except.ok arr ∧
    ValidMessage.isValidMessage arr a

theorem OriginReachable_HappensBefore {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {i : ClientId} {a b : YjsOperation A} {inputA inputB : IntegrateInput A} {itemA itemB : YjsItem A} {state_a state_b : Array (YjsItem A)}:
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
        exact Array.mem_of_find?_eq_some h_find
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
        exact Array.mem_of_find?_eq_some h_find

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
    simp [ArrSet, Operation.init, YjsEmptyArray] at h_b_in_init
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

theorem deleteItemById_isValid {A : Type} [DecidableEq A] (item : YjsItem A) (id : YjsId) :
  item.isValid →
  (deleteItemById item id).isValid := by
  intro h_valid
  simpa [deleteItemById] using h_valid

theorem OriginReachable_root_deleted_irrel {A : Type}
  (o r : YjsPtr A) (id : YjsId) (c : A) (d₁ d₂ : Bool) (x : YjsPtr A) :
  OriginReachable (YjsPtr.itemPtr (YjsItem.mk o r id c)) x →
  OriginReachable (YjsPtr.itemPtr (YjsItem.mk o r id c)) x := by
  intro h_reach
  simpa using h_reach

theorem YjsItem.isValid_root_deleted_irrel {A : Type} [DecidableEq A]
  (o r : YjsPtr A) (id : YjsId) (c : A) (d₁ d₂ : Bool) :
  (YjsItem.mk o r id c).isValid →
  (YjsItem.mk o r id c).isValid := by
  intro h_valid
  simpa using h_valid

theorem IntegrateInput.toItem_deleteById_valid {A : Type} [DecidableEq A]
  (input : IntegrateInput A) (arr : Array (YjsItem A)) (item : YjsItem A) (deletedId : YjsId) :
  input.toItem arr = Except.ok item →
  item.isValid →
  ∃ item', input.toItem (deleteById arr deletedId) = Except.ok item' ∧ item'.isValid := by
  intro h_toItem h_valid
  refine ⟨ toItemDeleteTransform item deletedId, ?_, ?_ ⟩
  · exact IntegrateInput.toItem_deleteById_ok input arr item deletedId h_toItem
  · cases item
    simpa [toItemDeleteTransform, deletePtrById, deleteItemById] using h_valid

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b sa sb h_a_mem h_b_mem h_a_b_happens_before havalid hbvalid hab
  intro h_ab
  cases a with
  | insert aInput =>
    cases b with
    | insert bInput =>
      simp [Operation.effect, integrateValid] at h_ab ⊢
      have h_sa_inv : YjsArrInvariant sa.toList := by
        simpa [Operation.StateInv] using havalid
      have h_a_valid_msg : ∃ aItem, aInput.toItem sa = Except.ok aItem ∧ aItem.isValid := by
        simpa [Operation.isValidState, IsValidMessage] using hbvalid
      have h_b_valid_msg : ∃ bItem, bInput.toItem sa = Except.ok bItem ∧ bItem.isValid := by
        simpa [Operation.isValidState, IsValidMessage] using hab
      obtain ⟨ aItem, h_a_toItem, h_a_item_valid ⟩ := h_a_valid_msg
      obtain ⟨ bItem, h_b_toItem, h_b_item_valid ⟩ := h_b_valid_msg
      have h_diff_client : aInput.id.clientId ≠ bInput.id.clientId := by
        exact hb_concurrent_diff_id network i
          (a := YjsOperation.insert aInput) h_a_mem
          (b := YjsOperation.insert bInput) h_b_mem
          h_a_b_happens_before
      have h_not_reach :
          ¬OriginReachable aItem (YjsPtr.itemPtr bItem) ∧
          ¬OriginReachable bItem (YjsPtr.itemPtr aItem) := by
        obtain ⟨ arr2, h_a_ok, h_b_ok ⟩ := Except.bind_eq_ok_exist h_ab
        constructor
        · intro h_reach_ab
          generalize h_a_ptr_def : YjsPtr.itemPtr aItem = a_ptr at h_reach_ab
          have h_OriginReachableStep_ArrSet : ∀ x,
            OriginReachableStep a_ptr x → ArrSet sa.toList x := by
            intro x h_step
            cases h_step with
            | reachable o r id c =>
              simp at h_a_ptr_def
              have h_to_item := (IntegrateInput.toItem_ok_iff aInput sa aItem h_sa_inv.unique).1 h_a_toItem
              obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
              rw [h_a_ptr_def] at hdef
              cases hdef
              cases h_originId : aInput.originId with
              | none =>
                simp [isLeftIdPtr, h_originId] at horigin
                subst horigin
                simp [ArrSet]
              | some pid =>
                simp [isLeftIdPtr, h_originId] at horigin
                obtain ⟨ item, h_eq, h_find ⟩ := horigin
                subst h_eq
                simp [ArrSet]
                exact Array.mem_of_find?_eq_some h_find
            | reachable_right o r id c =>
              simp at h_a_ptr_def
              have h_to_item := (IntegrateInput.toItem_ok_iff aInput sa aItem h_sa_inv.unique).1 h_a_toItem
              obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
              rw [h_a_ptr_def] at hdef
              cases hdef
              cases h_rightOriginId : aInput.rightOriginId with
              | none =>
                simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
                subst hrightOrigin
                simp [ArrSet]
              | some pid =>
                simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
                obtain ⟨ item, h_eq, h_find ⟩ := hrightOrigin
                subst h_eq
                simp [ArrSet]
                exact Array.mem_of_find?_eq_some h_find

          have h_b_in_sa_arrset : ArrSet sa.toList (YjsPtr.itemPtr bItem) := by
            cases h_reach_ab with
            | reachable_single _ _ h_step =>
              exact h_OriginReachableStep_ArrSet _ h_step
            | reachable_head _ y _ h_step h_reach_tail =>
              apply h_OriginReachableStep_ArrSet at h_step
              have h_closed : IsClosedItemSet (ArrSet sa.toList) := by
                exact h_sa_inv.closed
              exact reachable_in _ _ h_closed _ h_reach_tail h_step

          have h_b_in_sa : bItem ∈ (show Array (YjsItem A) from sa) := by
            simpa [ArrSet] using h_b_in_sa_arrset

          have ⟨ idx_a, _, h_arr2_def, _ ⟩ :=
            YjsArrInvariant_integrateSafe aInput aItem sa arr2 h_sa_inv h_a_toItem h_a_item_valid h_a_ok

          have h_b_in_arr2 : bItem ∈ (show Array (YjsItem A) from arr2) := by
            rw [h_arr2_def]
            by_cases hle : idx_a ≤ Array.size sa
            · simp [Array.insertIdxIfInBounds, hle, Array.mem_insertIdx, h_b_in_sa]
            · exfalso
              omega

          have h_b_item_id : bItem.id = bInput.id :=
            IntegrateInput.toItem_id_eq bInput sa bItem h_b_toItem

          have h_clock_false : isClockSafe bInput.id (show Array (YjsItem A) from arr2) = false := by
            unfold isClockSafe
            simp
            rw [Array.mem_iff_getElem] at h_b_in_arr2
            obtain ⟨ i, hi, hget ⟩ := h_b_in_arr2
            refine ⟨ i, hi, ?_ ⟩
            constructor
            · simp [hget, h_b_item_id]
            · simp [hget, h_b_item_id]

          have h_clock_true : isClockSafe bInput.id (show Array (YjsItem A) from arr2) = true := by
            unfold integrateSafe at h_b_ok
            split at h_b_ok
            · assumption
            · simp at h_b_ok

          rw [h_clock_false] at h_clock_true
          contradiction
        · intro h_reach_ba
          generalize h_b_ptr_def : YjsPtr.itemPtr bItem = b_ptr at h_reach_ba
          have h_OriginReachableStep_ArrSet : ∀ x,
            OriginReachableStep b_ptr x → ArrSet sa.toList x := by
            intro x h_step
            cases h_step with
            | reachable o r id c =>
              simp at h_b_ptr_def
              have h_to_item := (IntegrateInput.toItem_ok_iff bInput sa bItem h_sa_inv.unique).1 h_b_toItem
              obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
              rw [h_b_ptr_def] at hdef
              cases hdef
              cases h_originId : bInput.originId with
              | none =>
                simp [isLeftIdPtr, h_originId] at horigin
                subst horigin
                simp [ArrSet]
              | some pid =>
                simp [isLeftIdPtr, h_originId] at horigin
                obtain ⟨ item, h_eq, h_find ⟩ := horigin
                subst h_eq
                simp [ArrSet]
                exact Array.mem_of_find?_eq_some h_find
            | reachable_right o r id c =>
              simp at h_b_ptr_def
              have h_to_item := (IntegrateInput.toItem_ok_iff bInput sa bItem h_sa_inv.unique).1 h_b_toItem
              obtain ⟨ origin, rightOrigin, id', content', hdef, horigin, hrightOrigin, hid, hcontent ⟩ := h_to_item
              rw [h_b_ptr_def] at hdef
              cases hdef
              cases h_rightOriginId : bInput.rightOriginId with
              | none =>
                simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
                subst hrightOrigin
                simp [ArrSet]
              | some pid =>
                simp [isRightIdPtr, h_rightOriginId] at hrightOrigin
                obtain ⟨ item, h_eq, h_find ⟩ := hrightOrigin
                subst h_eq
                simp [ArrSet]
                exact Array.mem_of_find?_eq_some h_find

          have h_a_in_sa_arrset : ArrSet sa.toList (YjsPtr.itemPtr aItem) := by
            cases h_reach_ba with
            | reachable_single _ _ h_step =>
              exact h_OriginReachableStep_ArrSet _ h_step
            | reachable_head _ y _ h_step h_reach_tail =>
              apply h_OriginReachableStep_ArrSet at h_step
              have h_closed : IsClosedItemSet (ArrSet sa.toList) := by
                exact h_sa_inv.closed
              exact reachable_in _ _ h_closed _ h_reach_tail h_step

          have h_a_in_sa : aItem ∈ (show Array (YjsItem A) from sa) := by
            simpa [ArrSet] using h_a_in_sa_arrset

          have h_a_item_id : aItem.id = aInput.id :=
            IntegrateInput.toItem_id_eq aInput sa aItem h_a_toItem

          have h_clock_false : isClockSafe aInput.id (show Array (YjsItem A) from sa) = false := by
            unfold isClockSafe
            simp
            rw [Array.mem_iff_getElem] at h_a_in_sa
            obtain ⟨ i, hi, hget ⟩ := h_a_in_sa
            refine ⟨ i, hi, ?_ ⟩
            constructor
            · simp [hget, h_a_item_id]
            · simp [hget, h_a_item_id]

          have h_clock_true : isClockSafe aInput.id (show Array (YjsItem A) from sa) = true := by
            unfold integrateSafe at h_a_ok
            split at h_a_ok
            · assumption
            · simp at h_a_ok

          rw [h_clock_false] at h_clock_true
          contradiction
      have h_comm :
          (do
            let arr2 ← integrateSafe aInput sa
            integrateSafe bInput arr2) =
          (do
            let arr2' ← integrateSafe bInput sa
            integrateSafe aInput arr2') := by
        exact integrate_commutative aInput bInput aItem bItem sa
          h_sa_inv
          h_a_toItem
          h_b_toItem
          h_diff_client
          h_not_reach.1
          h_not_reach.2
          h_a_item_valid
          h_b_item_valid
      calc
        (do
          let arr2' ← integrateSafe bInput sa
          integrateSafe aInput arr2') =
          (do
            let arr2 ← integrateSafe aInput sa
            integrateSafe bInput arr2) := by
              simpa using h_comm.symm
        _ = Except.ok sb := h_ab
    | delete _ deletedId =>
      simp [Operation.effect, integrateValid, deleteValid] at h_ab ⊢
      have h_comm :
          (do
            let state ← integrateSafe aInput sa
            Except.ok (deleteById state deletedId)) =
          integrateSafe aInput (deleteById sa deletedId) := by
        simpa using (integrateSafe_deleteById_commutative (newItem := aInput) (arr := sa) (id := deletedId))
      have h_target : integrateSafe aInput (deleteById sa deletedId) = Except.ok sb := by
        calc
          integrateSafe aInput (deleteById sa deletedId)
              = (do
                  let state ← integrateSafe aInput sa
                  Except.ok (deleteById state deletedId)) := by
                    simpa using h_comm.symm
          _ = Except.ok sb := h_ab
      simpa [bind, Except.bind] using h_target
  | delete _ deletedId =>
    cases b with
    | insert bInput =>
      simp [Operation.effect, integrateValid, deleteValid] at h_ab ⊢
      have h_comm :
          (do
            let state ← integrateSafe bInput sa
            Except.ok (deleteById state deletedId)) =
          integrateSafe bInput (deleteById sa deletedId) := by
        simpa using (integrateSafe_deleteById_commutative (newItem := bInput) (arr := sa) (id := deletedId))
      have h_target :
          (do
            let state ← integrateSafe bInput sa
            Except.ok (deleteById state deletedId)) = Except.ok sb := by
        calc
          (do
            let state ← integrateSafe bInput sa
            Except.ok (deleteById state deletedId))
              = integrateSafe bInput (deleteById sa deletedId) := h_comm
          _ = Except.ok sb := h_ab
      simpa [bind, Except.bind] using h_target
    | delete _ deletedId' =>
      simp [Operation.effect, deleteValid, bind, Except.bind] at h_ab ⊢
      rw [deleteById_commutative] at h_ab
      exact h_ab
  -- simp [Operation.State, Operation.Error] at *
  -- simp [effect_comp, effect]
  -- apply Except.map_eq_eq (f := fun (x : YjsArray A) => x.val)
  -- . intros x y h_eq
  --   apply Subtype_eq_of_val
  --   exact h_eq
  -- . obtain ⟨ a ⟩ := a
  --   obtain ⟨ b ⟩ := b
  --   cases a with
  --   | insert a =>
  --     cases b with
  --     | insert b =>
  --       conv =>
  --         lhs
  --         enter [2]
  --         simp [Operation.effect]
  --       rw [integrateValid_bind_integrateSafe]
  --       conv =>
  --         rhs
  --         enter [2]
  --         simp [Operation.effect]
  --       rw [integrateValid_bind_integrateSafe]
  --       apply integrate_commutative
  --       . obtain ⟨ s, h_s ⟩ := s
  --         simp; assumption
  --       . sorry
  --       . sorry
  --       . apply hb_concurrent_diff_id _ _
  --           (a := ⟨ YjsOperation.insert a ⟩) (b := ⟨YjsOperation.insert b ⟩) h_a_mem h_b_mem h_a_b_happens_before
  --       . intros h_reachable
  --         obtain ⟨ _, h_b_hb_a ⟩ := h_a_b_happens_before
  --         apply h_b_hb_a
  --         apply OriginReachable_HappensBefore h_a_mem h_b_mem rfl rfl h_reachable
  --       . intros h_reachable
  --         obtain ⟨ h_a_hb_b, _ ⟩ := h_a_b_happens_before
  --         apply h_a_hb_b
  --         apply OriginReachable_HappensBefore h_b_mem h_a_mem rfl rfl h_reachable
  --       . obtain ⟨ a, _ ⟩ := a
  --         assumption
  --       . obtain ⟨ b, _ ⟩ := b
  --         assumption
  --     | delete _ deletedId =>
  --       simp [Operation.State, Operation.Error, Operation.effect]
  --       simp [deleteValid]
  --       rw [<-bind_map_left (f := fun (x : YjsArray A) => x.val) (g := fun arr => Except.ok (deleteById arr deletedId)),
  --           integrateValid_eq_integrateSafe,
  --           integrateSafe_deleteById_commutative]
  --       simp [bind, Except.bind]
  --       rw [integrateValid_eq_integrateSafe]
  --   | delete _ deletedId =>
  --     cases b with
  --     | insert b =>
  --       simp [Operation.State, Operation.Error, Operation.effect]
  --       simp [deleteValid]
  --       rw [<-bind_map_left (f := fun (x : YjsArray A) => x.val) (g := fun arr => Except.ok (deleteById arr deletedId)),
  --           integrateValid_eq_integrateSafe,
  --           integrateSafe_deleteById_commutative]
  --       simp [bind, Except.bind]
  --       rw [integrateValid_eq_integrateSafe]
  --     | delete _ deletedId' =>
  --       simp [Operation.Error, Operation.effect, deleteValid, bind, Except.bind]
  --       apply deleteById_commutative

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
    simpa [h_hist, List.append_assoc]
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
    simpa [h_hist, List.append_assoc]
  exact HappensBefore.broadcast_deliver_local h_local

theorem findLeftIdx_ok_ge_minus_one {A : Type} [DecidableEq A]
  {originId : Option YjsId} {arr : Array (YjsItem A)} {leftIdx : Int} :
  findLeftIdx originId arr = Except.ok leftIdx →
  (-1 : Int) ≤ leftIdx := by
  intro h
  cases h_originId : originId with
  | none =>
    simp [findLeftIdx, h_originId] at h
    cases h
    simp
  | some oid =>
    simp [findLeftIdx, h_originId] at h
    cases h_find : arr.findIdx? (fun item => item.id = oid) with
    | none =>
      simp [h_find] at h
    | some idx =>
      simp [h_find] at h
      cases h
      omega

theorem findRightIdx_ok_le_size {A : Type} [DecidableEq A]
  {rightOriginId : Option YjsId} {arr : Array (YjsItem A)} {rightIdx : Int} :
  findRightIdx rightOriginId arr = Except.ok rightIdx →
  rightIdx ≤ arr.size := by
  intro h
  cases h_rightOriginId : rightOriginId with
  | none =>
    simp [findRightIdx, h_rightOriginId] at h
    cases h
    simp
  | some oid =>
    simp [findRightIdx, h_rightOriginId] at h
    cases h_find : arr.findIdx? (fun item => item.id = oid) with
    | none =>
      simp [h_find] at h
    | some idx =>
      simp [h_find] at h
      cases h
      rw [Array.findIdx?_eq_some_iff_getElem] at h_find
      obtain ⟨ h_lt, _, _ ⟩ := h_find
      omega

theorem findLeftIdx_ok_lt_size {A : Type} [DecidableEq A]
  {originId : Option YjsId} {arr : Array (YjsItem A)} {leftIdx : Int} :
  findLeftIdx originId arr = Except.ok leftIdx →
  leftIdx < arr.size := by
  intro h
  cases h_originId : originId with
  | none =>
    simp [findLeftIdx, h_originId] at h
    cases h
    omega
  | some oid =>
    simp [findLeftIdx, h_originId] at h
    cases h_find : arr.findIdx? (fun item => item.id = oid) with
    | none =>
      simp [h_find] at h
    | some idx =>
      simp [h_find] at h
      cases h
      rw [Array.findIdx?_eq_some_iff_getElem] at h_find
      obtain ⟨ h_lt, _, _ ⟩ := h_find
      omega

theorem integrateValid_inserts_id {A : Type} [DecidableEq A]
  (input : IntegrateInput A) (arr arr' : Array (YjsItem A)) :
  integrateValid input arr = Except.ok arr' →
  ∃ item, item.id = input.id ∧ item ∈ arr' := by
  intro h_ok
  have h_integrate : integrate input arr = Except.ok arr' := by
    unfold integrateValid at h_ok
    simp [integrateSafe] at h_ok
    split at h_ok
    · exact h_ok
    · simp at h_ok
  unfold integrate at h_integrate
  obtain ⟨ leftIdx, h_left, h1 ⟩ := Except.bind_eq_ok_exist h_integrate
  obtain ⟨ rightIdx, h_right, h2 ⟩ := Except.bind_eq_ok_exist h1
  obtain ⟨ destIdx, h_dest, h3 ⟩ := Except.bind_eq_ok_exist h2
  obtain ⟨ item, h_item, h4 ⟩ := Except.bind_eq_ok_exist h3
  have h_arr'_eq : arr' = arr.insertIdxIfInBounds destIdx item := by
    cases h4
    rfl
  have h_item_id : item.id = input.id := by
    cases hleft : getPtrExcept arr leftIdx with
    | error err =>
      simp [mkItemByIndex, hleft] at h_item
      cases h_item
    | ok leftPtr =>
      cases hright : getPtrExcept arr rightIdx with
      | error err =>
        simp [mkItemByIndex, hleft, hright] at h_item
        cases h_item
      | ok rightPtr =>
        have h_item_eq := h_item
        rw [mkItemByIndex, hleft, hright] at h_item_eq
        simp [bind, Except.bind] at h_item_eq
        have h_item_def : item = YjsItem.mk leftPtr rightPtr input.id input.content := by
          cases h_item_eq
          rfl
        simpa [h_item_def]
  have h_left_ge : (-1 : Int) ≤ leftIdx := findLeftIdx_ok_ge_minus_one h_left
  have h_right_le : rightIdx ≤ arr.size := findRightIdx_ok_le_size h_right
  have h_left_lt : leftIdx < arr.size := findLeftIdx_ok_lt_size h_left
  have h_dest_le : destIdx ≤ arr.size := by
    exact findIntegratedIndex_ok_le_size leftIdx rightIdx input arr destIdx
      h_left_ge h_left_lt h_right_le h_dest
  refine ⟨ item, h_item_id, ?_ ⟩
  rw [h_arr'_eq]
  simp [Array.insertIdxIfInBounds, h_dest_le]
  exact (Array.mem_insertIdx (a := item) (b := item) (xs := arr) (h := h_dest_le)).2 (Or.inl rfl)

theorem effect_preserves_stateEqIgnoreDeleted {A : Type} [DecidableEq A]
  (op : YjsOperation A) (s s' : Array (YjsItem A)) :
  Operation.effect op s = Except.ok s' →
  StateEqIgnoreDeleted s s' := by
  intro h_eff
  cases op with
  | delete _ deletedId =>
    simp [Operation.effect, deleteValid] at h_eff
    subst h_eff
    exact StateEqIgnoreDeleted_deleteById s deletedId
  | insert input =>
    simp [Operation.effect] at h_eff
    obtain ⟨ i, newItem, _h_new_id, h_s' ⟩ :=
      integrateValid_exists_insertIdxIfBounds (init := s) (input := input) (state' := s') h_eff
    subst h_s'
    exact StateEqIgnoreDeleted_insertIdxIfInBounds s i newItem

theorem effect_list_preserves_stateEqIgnoreDeleted {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s₀ s : Array (YjsItem A)) :
  effect_list ops s₀ = Except.ok s →
  StateEqIgnoreDeleted s₀ s := by
  intro h_eff
  induction ops generalizing s₀ s with
  | nil =>
    simp [effect_list] at h_eff
    cases h_eff
    exact StateEqIgnoreDeleted.refl s₀
  | cons op ops ih =>
    simp [effect_list] at h_eff
    obtain ⟨ s₁, h_op, h_tail ⟩ := Except.bind_eq_ok_exist h_eff
    have h01 : StateEqIgnoreDeleted s₀ s₁ :=
      effect_preserves_stateEqIgnoreDeleted op s₀ s₁ h_op
    have h12 : StateEqIgnoreDeleted s₁ s := ih s₁ s h_tail
    exact StateEqIgnoreDeleted.trans h01 h12

theorem effect_preserves_id_exists {A : Type} [DecidableEq A]
  (op : YjsOperation A) (s s' : Array (YjsItem A)) (targetId : YjsId) :
  Operation.effect op s = Except.ok s' →
  (∃ item, item ∈ s ∧ item.id = targetId) →
  (∃ item', item' ∈ s' ∧ item'.id = targetId) := by
  intro h_eff h_exists
  cases op with
  | delete id deletedId =>
    simp [Operation.effect, deleteValid] at h_eff
    subst h_eff
    obtain ⟨ item, h_mem, h_id ⟩ := h_exists
    refine ⟨ item, ?_, h_id ⟩
    · simpa [deleteById] using h_mem
  | insert input =>
    simp [Operation.effect] at h_eff
    obtain ⟨ item0, h_mem0, h_id0 ⟩ := h_exists
    obtain ⟨ i, newItem, h_new_id, h_s' ⟩ :=
      integrateValid_exists_insertIdxIfBounds (init := s) (input := input) (state' := s') h_eff
    refine ⟨ item0, ?_, h_id0 ⟩
    rw [h_s']
    simp [Array.insertIdxIfInBounds]
    split
    · exact (Array.mem_insertIdx (a := item0) (b := newItem) (xs := s) (h := by assumption)).2 (Or.inr h_mem0)
    · simpa [*] using h_mem0

theorem effect_list_preserves_id_exists {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s0 s : Array (YjsItem A)) (targetId : YjsId) :
  effect_list ops s0 = Except.ok s →
  (∃ item, item ∈ s0 ∧ item.id = targetId) →
  (∃ item', item' ∈ s ∧ item'.id = targetId) := by
  intro h_eff h_exists
  induction ops generalizing s0 s with
  | nil =>
    simp at h_eff
    subst h_eff
    simpa using h_exists
  | cons op ops ih =>
    simp [effect_list] at h_eff
    obtain ⟨ s1, h_op, h_tail ⟩ := Except.bind_eq_ok_exist h_eff
    have h_exists1 := effect_preserves_id_exists op s0 s1 targetId h_op h_exists
    exact ih (s0 := s1) (s := s) h_tail h_exists1

theorem effect_list_insert_mem_implies_id_exists_from_state {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s0 s : Array (YjsItem A)) (input : IntegrateInput A) :
  effect_list ops s0 = Except.ok s →
  ((∃ item0, item0 ∈ s0 ∧ item0.id = input.id) ∨ YjsOperation.insert input ∈ ops) →
  ∃ item, item ∈ s ∧ item.id = input.id := by
  intro h_eff h_seed
  induction ops generalizing s0 s with
  | nil =>
    simp [effect_list] at h_eff
    have hs : s0 = s := by
      cases h_eff
      rfl
    subst s
    cases h_seed with
    | inl h_exists =>
      simpa using h_exists
    | inr h_mem =>
      cases h_mem
  | cons op ops ih =>
    simp [effect_list] at h_eff
    obtain ⟨ s1, h_op, h_tail ⟩ := Except.bind_eq_ok_exist h_eff
    cases h_seed with
    | inl h_exists =>
      have h_exists1 := effect_preserves_id_exists op s0 s1 input.id h_op h_exists
      exact ih (s0 := s1) (s := s) h_tail (Or.inl h_exists1)
    | inr h_mem =>
      simp at h_mem
      cases h_mem with
      | inl h_eq =>
        subst h_eq
        simp [Operation.effect] at h_op
        obtain ⟨ item1, h_item1_id, h_item1_mem ⟩ :=
          integrateValid_inserts_id (input := input) (arr := s0) (arr' := s1) h_op
        exact ih (s0 := s1) (s := s) h_tail (Or.inl ⟨ item1, h_item1_mem, h_item1_id ⟩)
      | inr h_mem_tail =>
        exact ih (s0 := s1) (s := s) h_tail (Or.inr h_mem_tail)

theorem effect_list_insert_mem_implies_id_exists {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s : Array (YjsItem A)) (input : IntegrateInput A) :
  effect_list ops Operation.init = Except.ok s →
  YjsOperation.insert input ∈ ops →
  ∃ item, item ∈ s ∧ item.id = input.id := by
  intro h_eff h_mem
  let sInit : Operation.State (YjsOperation A) := Operation.init
  have h_eff' : effect_list ops sInit = Except.ok s := by
    simpa [sInit] using h_eff
  exact effect_list_insert_mem_implies_id_exists_from_state
    (A := A) (ops := ops) (s0 := sInit) (s := s) (input := input) h_eff' (Or.inr h_mem)

theorem uniqueId_deleteById {A : Type} [DecidableEq A]
  (arr : Array (YjsItem A)) (deletedId : YjsId) :
  uniqueId arr.toList →
  uniqueId (deleteById arr deletedId).toList := by
  intro h_unique
  simp [uniqueId] at h_unique ⊢
  rw [List.pairwise_iff_getElem] at h_unique ⊢
  intro i j hi hj hij
  have hi' : i < arr.toList.length := by simpa [deleteById] using hi
  have hj' : j < arr.toList.length := by simpa [deleteById] using hj
  simpa [deleteById, deleteItemById_id_eq] using h_unique i j hi' hj' hij

theorem effect_list_uniqueId_from_IdNoDup {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s : Array (YjsItem A)) :
  IdNoDup ops →
  effect_list ops Operation.init = Except.ok s →
  uniqueId s.toList := by
  intro h_nodup h_eff
  sorry

theorem toItem_isValid_transport_min_bridge {A : Type} [DecidableEq A]
  (input : IntegrateInput A)
  (state₀ s : Array (YjsItem A))
  (item₀ : YjsItem A)
  (h_toItem₀ : input.toItem state₀ = Except.ok item₀)
  (h_item_valid₀ : item₀.isValid)
  (h_unique_s : uniqueId s.toList)
  (h_origin_find_in_s :
    ∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
      ∃ originItem', s.find? (fun i => i.id = oid) = some originItem') :
  ∃ item, input.toItem s = Except.ok item ∧ item.isValid := by
  have h_rel : StateEqIgnoreDeleted state₀ s :=
    stateEqIgnoreDeleted_from_origin_lookup
      (state₀ := state₀) (s := s) h_unique_s h_origin_find_in_s
  obtain ⟨ item, h_toItem_s, h_item_rel ⟩ :=
    toItem_exists_transport
      (input := input) (state₀ := state₀) (s := s) (item₀ := item₀)
      h_toItem₀ h_rel h_unique_s
  exact ⟨ item, h_toItem_s, ItemEqIgnoreDeleted.isValid h_item_rel h_item_valid₀ ⟩

theorem isValidState_insert_from_source {A : Type} [DecidableEq A]
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
  intro h_source h_lt h_consistent h_closed h_effect h_nodup
  obtain ⟨ srcClient, h_broadcast_mem ⟩ := h_source
  rw [List.mem_iff_append] at h_broadcast_mem
  obtain ⟨ pre, post, h_hist_eq ⟩ := h_broadcast_mem
  have h_valid_at_broadcast :
      ∃ state,
        interpHistory pre Operation.init = Except.ok state ∧
        ValidMessage.isValidMessage state (YjsOperation.insert input) := by
    have h_hist_eq' :
        pre ++ [Event.Broadcast (YjsOperation.insert input)] ++ post =
          network.histories srcClient := by
      simpa using h_hist_eq.symm
    simpa using
      (network.broadcast_only_valid_messages srcClient (pre := pre) (post := post)
        (e := YjsOperation.insert input) h_hist_eq')
  obtain ⟨ state₀, h_state₀, h_msg_valid₀ ⟩ := h_valid_at_broadcast
  have h_valid_msg₀ :
      ∃ item, input.toItem state₀ = Except.ok item ∧ item.isValid := by
    simpa [ValidMessage.isValidMessage, IsValidMessage] using h_msg_valid₀
  obtain ⟨ item₀, h_toItem₀, h_item_valid₀ ⟩ := h_valid_msg₀
  have h_pre_broadcast_in_l :
      ∀ x, Event.Broadcast (YjsOperation.insert x) ∈ pre →
        YjsOperation.insert x ∈ l := by
    intro x h_mem_pre
    apply h_lt
    exact pre_broadcast_lt_insert (network := network)
      (i := srcClient) (pre := pre) (post := post)
      (x := x) (input := input) h_hist_eq h_mem_pre
  have h_pre_deliver_in_l :
      ∀ x, Event.Deliver (YjsOperation.insert x) ∈ pre →
        YjsOperation.insert x ∈ l := by
    intro x h_mem_pre
    apply h_lt
    exact pre_deliver_lt_insert (network := network)
      (i := srcClient) (pre := pre) (post := post)
      (x := x) (input := input) h_hist_eq h_mem_pre
  have h_origin_pre :
      ∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
        ∃ x, YjsOperation.insert x ∈ l ∧ x.id = oid := by
    intro oid originItem h_find
    obtain ⟨ x, h_deliver_mem, h_x_id ⟩ :=
      interpHistory_find?_exists_deliver_insert (A := A)
        (pre := pre) (state := state₀) (id := oid) (item := originItem)
        h_state₀ h_find
    exact ⟨ x, h_pre_deliver_in_l x h_deliver_mem, h_x_id ⟩
  let sArr : Array (YjsItem A) := s
  have h_origin_find_in_s :
      ∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
        ∃ originItem', sArr.find? (fun i => i.id = oid) = some originItem' := by
    intro oid originItem h_find₀
    obtain ⟨ x, h_x_mem_l, h_x_id ⟩ := h_origin_pre oid originItem h_find₀
    have h_exists_in_s : ∃ item : YjsItem A, item ∈ sArr ∧ item.id = oid := by
      obtain ⟨ item, h_item_mem, h_item_id ⟩ :=
        effect_list_insert_mem_implies_id_exists (ops := l) (s := sArr) (input := x) (by simpa [sArr] using h_effect) h_x_mem_l
      exact ⟨ item, h_item_mem, by simpa [h_x_id] using h_item_id ⟩
    exact exists_find?_eq_some_of_exists_mem_id sArr oid h_exists_in_s
  have h_unique_s : uniqueId sArr.toList := by
    exact effect_list_uniqueId_from_IdNoDup (ops := l) (s := sArr) h_nodup (by simpa [sArr] using h_effect)
  -- Remaining core step:
  -- transport `input.toItem state₀ = ok item₀` and `item₀.isValid` to state `s`
  -- built by `effect_list l init = ok s`.
  exact toItem_isValid_transport_min_bridge
    (input := input) (state₀ := state₀) (s := sArr) (item₀ := item₀)
    h_toItem₀ h_item_valid₀ h_unique_s h_origin_find_in_s

instance [DecidableEq A] {network : YjsOperationNetwork A} : MonotoneOperation (YjsOperation A) (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) YjsId where
  StateSource a := ∃ i, Event.Broadcast a ∈ network.toCausalNetwork.histories i
  isValidState_mono := by
    intro a s l h_source h_lt h_consistent h_closed h_effect h_nodup
    cases a with
    | delete id deletedId =>
      simp [Operation.isValidState, IsValidMessage]
    | insert input =>
      simpa [Operation.isValidState, IsValidMessage] using
        (isValidState_insert_from_source (network := network) (input := input) (s := s) (l := l)
          h_source h_lt h_consistent h_closed h_effect h_nodup)

theorem YjsOperationNetwork_converge' {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : Array (YjsItem A)) :
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
  have h_consistent_i : hb_consistent hb (network.toCausalNetwork.toDeliverMessages i) := by
    apply hb_consistent_local_history
  have h_consistent_j : hb_consistent hb (network.toCausalNetwork.toDeliverMessages j) := by
    apply hb_consistent_local_history

  have h_noDup_i : (network.toCausalNetwork.toDeliverMessages i).Nodup := by
    apply toDeliverMessages_Nodup

  have h_noDup_j : (network.toCausalNetwork.toDeliverMessages j).Nodup := by
    apply toDeliverMessages_Nodup

  have h_deliver_mem_of_toDeliver_mem :
      ∀ {k : ClientId} {m : YjsOperation A},
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

  have h_toDeliver_mem_of_deliver_mem :
      ∀ {k : ClientId} {m : YjsOperation A},
        Event.Deliver m ∈ network.toCausalNetwork.histories k →
          m ∈ network.toCausalNetwork.toDeliverMessages k := by
    intro k m h_mem
    simp [CausalNetwork.toDeliverMessages]
    exact ⟨ Event.Deliver m, h_mem, by simp ⟩

  have h_closed_i :
      hbClosed hb (network.toCausalNetwork.toDeliverMessages i) := by
    intro a b l₁ l₂ h_eq h_b_lt_a
    have h_a_mem : a ∈ network.toCausalNetwork.toDeliverMessages i := by
      rw [h_eq]
      simp
    have h_deliver_a_mem : Event.Deliver a ∈ network.toCausalNetwork.histories i := by
      exact h_deliver_mem_of_toDeliver_mem h_a_mem
    have h_local :
        locallyOrdered network.toCausalNetwork.toNodeHistories i (Event.Deliver b) (Event.Deliver a) := by
      exact network.toCausalNetwork.causal_delivery h_deliver_a_mem h_b_lt_a
    have h_deliver_b_mem : Event.Deliver b ∈ network.toCausalNetwork.histories i := by
      obtain ⟨ pre, mid, post, h_hist_eq ⟩ := h_local
      rw [h_hist_eq]
      simp
    have h_b_mem : b ∈ network.toCausalNetwork.toDeliverMessages i := by
      exact h_toDeliver_mem_of_deliver_mem h_deliver_b_mem
    have h_cons_suffix : hb_consistent hb (a :: l₂) := by
      apply hb_consistent_sublist (hb := hb) h_consistent_i
      rw [h_eq]
      simpa using (List.sublist_append_right (l₁ := a :: l₂) (l₂ := l₁))
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

  have h_closed_j :
      hbClosed hb (network.toCausalNetwork.toDeliverMessages j) := by
    intro a b l₁ l₂ h_eq h_b_lt_a
    have h_a_mem : a ∈ network.toCausalNetwork.toDeliverMessages j := by
      rw [h_eq]
      simp
    have h_deliver_a_mem : Event.Deliver a ∈ network.toCausalNetwork.histories j := by
      exact h_deliver_mem_of_toDeliver_mem h_a_mem
    have h_local :
        locallyOrdered network.toCausalNetwork.toNodeHistories j (Event.Deliver b) (Event.Deliver a) := by
      exact network.toCausalNetwork.causal_delivery h_deliver_a_mem h_b_lt_a
    have h_deliver_b_mem : Event.Deliver b ∈ network.toCausalNetwork.histories j := by
      obtain ⟨ pre, mid, post, h_hist_eq ⟩ := h_local
      rw [h_hist_eq]
      simp
    have h_b_mem : b ∈ network.toCausalNetwork.toDeliverMessages j := by
      exact h_toDeliver_mem_of_deliver_mem h_deliver_b_mem
    have h_cons_suffix : hb_consistent hb (a :: l₂) := by
      apply hb_consistent_sublist (hb := hb) h_consistent_j
      rw [h_eq]
      simpa using (List.sublist_append_right (l₁ := a :: l₂) (l₂ := l₁))
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

  have h_op_id_eq_msg_id : ∀ op : YjsOperation A, WithId.id op = Message.messageId op := by
    intro op
    cases op <;> rfl

  have h_id_no_dup_i : IdNoDup (network.toCausalNetwork.toDeliverMessages i) := by
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
      apply h_deliver_mem_of_toDeliver_mem
      exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages i) (h := h_idx₁)
    have h_deliver_mem₂ :
        Event.Deliver (network.toCausalNetwork.toDeliverMessages i)[idx₂] ∈
          network.toCausalNetwork.histories i := by
      apply h_deliver_mem_of_toDeliver_mem
      exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages i) (h := h_idx₂)
    obtain ⟨ c₁, h_broadcast_mem₁ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₁
    obtain ⟨ c₂, h_broadcast_mem₂ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₂
    have h_op_eq :
        (network.toCausalNetwork.toDeliverMessages i)[idx₁] =
          (network.toCausalNetwork.toDeliverMessages i)[idx₂] := by
      exact (network.toCausalNetwork.msg_id_unique h_broadcast_mem₁ h_broadcast_mem₂ h_msg_id_eq).2
    exact h_pairwise_ne_i idx₁ idx₂ h_idx₁ h_idx₂ h_idx_lt h_op_eq

  have h_id_no_dup_j : IdNoDup (network.toCausalNetwork.toDeliverMessages j) := by
    unfold IdNoDup
    rw [List.pairwise_iff_getElem]
    intro idx₁ idx₂ h_idx₁ h_idx₂ h_idx_lt h_id_eq
    have h_pairwise_ne_j : List.Pairwise (fun x y => x ≠ y) (network.toCausalNetwork.toDeliverMessages j) := by
      simpa [List.nodup_iff_pairwise_ne] using h_noDup_j
    rw [List.pairwise_iff_getElem] at h_pairwise_ne_j
    have h_msg_id_eq :
        Message.messageId (network.toCausalNetwork.toDeliverMessages j)[idx₁] =
          Message.messageId (network.toCausalNetwork.toDeliverMessages j)[idx₂] := by
      rw [←h_op_id_eq_msg_id (network.toCausalNetwork.toDeliverMessages j)[idx₁]]
      rw [←h_op_id_eq_msg_id (network.toCausalNetwork.toDeliverMessages j)[idx₂]]
      exact h_id_eq
    have h_deliver_mem₁ :
        Event.Deliver (network.toCausalNetwork.toDeliverMessages j)[idx₁] ∈
          network.toCausalNetwork.histories j := by
      apply h_deliver_mem_of_toDeliver_mem
      exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages j) (h := h_idx₁)
    have h_deliver_mem₂ :
        Event.Deliver (network.toCausalNetwork.toDeliverMessages j)[idx₂] ∈
          network.toCausalNetwork.histories j := by
      apply h_deliver_mem_of_toDeliver_mem
      exact List.getElem_mem (l := network.toCausalNetwork.toDeliverMessages j) (h := h_idx₂)
    obtain ⟨ c₁, h_broadcast_mem₁ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₁
    obtain ⟨ c₂, h_broadcast_mem₂ ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_mem₂
    have h_op_eq :
        (network.toCausalNetwork.toDeliverMessages j)[idx₁] =
          (network.toCausalNetwork.toDeliverMessages j)[idx₂] := by
      exact (network.toCausalNetwork.msg_id_unique h_broadcast_mem₁ h_broadcast_mem₂ h_msg_id_eq).2
    exact h_pairwise_ne_j idx₁ idx₂ h_idx₁ h_idx₂ h_idx_lt h_op_eq

  have h_concurrent_commutative : concurrent_commutative (hb := hb) (network.toCausalNetwork.toDeliverMessages i) := by
    apply YjsOperationNetwork_concurrentCommutative network i

  have h := hb_consistent_effect_convergent (s := res₀) (hb := hb)
    (network.toCausalNetwork.toDeliverMessages i)
    (network.toCausalNetwork.toDeliverMessages j)
    (by
      intro x hx
      have h_deliver_x_mem : Event.Deliver x ∈ network.toCausalNetwork.histories i := by
        exact h_deliver_mem_of_toDeliver_mem hx
      obtain ⟨ c, h_broadcast_x_mem ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_x_mem
      exact ⟨ c, h_broadcast_x_mem ⟩)
    (by
      intro x hx
      have h_deliver_x_mem : Event.Deliver x ∈ network.toCausalNetwork.histories j := by
        exact h_deliver_mem_of_toDeliver_mem hx
      obtain ⟨ c, h_broadcast_x_mem ⟩ := network.toCausalNetwork.deliver_has_a_cause h_deliver_x_mem
      exact ⟨ c, h_broadcast_x_mem ⟩)
    h_consistent_i
    h_consistent_j
    h_closed_i
    h_closed_j
    h_concurrent_commutative
    h_id_no_dup_i
    h_id_no_dup_j
    h_hist_mem
    h_res₀

  have h_res_ok_eq : Except.ok (ε := IntegrateError) res₀ = Except.ok res₁ := by
    rw [<-h_res₀, <-h_res₁]
    simp [interpOps] at *
    rw [h, h_res₀]

  cases h_res_ok_eq
  simp
end YjsNetwork
