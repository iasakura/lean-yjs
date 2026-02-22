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
  ∃ i item, item.id = input.id ∧ input.toItem init.items = Except.ok item ∧
    item ∈ state'.items ∧
    state' = { init with items := init.items.insertIdxIfInBounds i item } := by
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
  obtain ⟨ leftPtr, h_leftPtr, h_leftIdPtr ⟩ :=
    findLeftIdx_getElemExcept (arr := init.items) (input := input) h_leftIdx
  obtain ⟨ rightPtr, h_rightPtr, h_rightIdPtr ⟩ :=
    findRightIdx_getElemExcept (arr := init.items) (input := input) h_rightIdx
  have h_state' : state'.items = init.items.insertIdxIfInBounds destIdx item' := by
    simp [pure, Except.pure] at h4
    grind
  have h_item_def : item' = YjsItem.mk leftPtr rightPtr input.id input.content := by
    have hmk : mkItemByIndex leftIdx rightIdx input init.items = Except.ok item' := h_item'
    simp [mkItemByIndex, h_leftPtr, h_rightPtr, bind, Except.bind, pure, Except.pure] at hmk
    simpa using hmk.symm
  have h_toItem : input.toItem init.items = Except.ok item' := by
    cases h_originId : input.originId with
    | none =>
      have h_left_eq : leftPtr = YjsPtr.first := by
        simpa [isLeftIdPtr, h_originId] using h_leftIdPtr
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        have h_right_eq : rightPtr = YjsPtr.last := by
          simpa [isRightIdPtr, h_rightOriginId] using h_rightIdPtr
        simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_item_def, h_left_eq, h_right_eq,
          bind, Except.bind, pure, Except.pure]
      | some rid =>
        obtain ⟨ rightItem, h_right_eq, h_find_right ⟩ :
            ∃ rightItem, rightPtr = YjsPtr.itemPtr rightItem ∧
              init.items.find? (fun i => i.id = rid) = some rightItem := by
          simpa [isRightIdPtr, h_rightOriginId] using h_rightIdPtr
        simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_item_def,
          h_left_eq, h_right_eq, h_find_right, bind, Except.bind, pure, Except.pure]
    | some oid =>
      obtain ⟨ originItem, h_left_eq, h_find_left ⟩ :
          ∃ originItem, leftPtr = YjsPtr.itemPtr originItem ∧
            init.items.find? (fun i => i.id = oid) = some originItem := by
        simpa [isLeftIdPtr, h_originId] using h_leftIdPtr
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        have h_right_eq : rightPtr = YjsPtr.last := by
          simpa [isRightIdPtr, h_rightOriginId] using h_rightIdPtr
        simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_item_def,
          h_left_eq, h_find_left, h_right_eq, bind, Except.bind, pure, Except.pure]
      | some rid =>
        obtain ⟨ rightItem, h_right_eq, h_find_right ⟩ :
            ∃ rightItem, rightPtr = YjsPtr.itemPtr rightItem ∧
              init.items.find? (fun i => i.id = rid) = some rightItem := by
          simpa [isRightIdPtr, h_rightOriginId] using h_rightIdPtr
        simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_item_def,
          h_left_eq, h_find_left, h_right_eq, h_find_right, bind, Except.bind, pure, Except.pure]
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
  have h_left_ge : (-1 : Int) ≤ leftIdx := by
    cases h_originId : input.originId with
    | none =>
      simp [findLeftIdx, h_originId] at h_leftIdx
      cases h_leftIdx
      omega
    | some oid =>
      simp [findLeftIdx, h_originId] at h_leftIdx
      cases h_find : init.items.findIdx? (fun item => item.id = oid) with
      | none =>
        simp [h_find] at h_leftIdx
      | some idx =>
        simp [h_find] at h_leftIdx
        cases h_leftIdx
        omega
  have h_right_le : rightIdx ≤ init.items.size := by
    cases h_rightOriginId : input.rightOriginId with
    | none =>
      simp [findRightIdx, h_rightOriginId] at h_rightIdx
      cases h_rightIdx
      omega
    | some oid =>
      simp [findRightIdx, h_rightOriginId] at h_rightIdx
      cases h_find : init.items.findIdx? (fun item => item.id = oid) with
      | none =>
        simp [h_find] at h_rightIdx
      | some idx =>
        simp [h_find] at h_rightIdx
        cases h_rightIdx
        rw [Array.findIdx?_eq_some_iff_getElem] at h_find
        obtain ⟨ h_lt, _, _ ⟩ := h_find
        omega
  have h_left_lt : leftIdx < init.items.size := by
    cases h_originId : input.originId with
    | none =>
      simp [findLeftIdx, h_originId] at h_leftIdx
      cases h_leftIdx
      omega
    | some oid =>
      simp [findLeftIdx, h_originId] at h_leftIdx
      cases h_find : init.items.findIdx? (fun item => item.id = oid) with
      | none =>
        simp [h_find] at h_leftIdx
      | some idx =>
        simp [h_find] at h_leftIdx
        cases h_leftIdx
        rw [Array.findIdx?_eq_some_iff_getElem] at h_find
        obtain ⟨ h_lt, _, _ ⟩ := h_find
        omega
  have h_dest_le : destIdx ≤ init.items.size := by
    exact findIntegratedIndex_ok_le_size_from_eq leftIdx rightIdx input init.items destIdx
      h_left_ge h_left_lt h_right_le h_destIdx
  have h_item_mem : item' ∈ state'.items := by
    rw [h_state']
    have h_mem_insert : item' ∈ init.items.insertIdx destIdx item' h_dest_le :=
      (Array.mem_insertIdx (a := item') (b := item') (xs := init.items) (h := h_dest_le)).2 (Or.inl rfl)
    simpa [Array.insertIdxIfInBounds, h_dest_le] using h_mem_insert
  have hdeleted : state'.deletedIds = init.deletedIds := by
    simp [YjsState.insert] at h_effect
    cases heq : integrateSafe input init.items with
      | error err =>
        simp [heq] at h_effect
      | ok items' =>
        simp [heq] at h_effect
        subst h_effect
        rfl
  refine ⟨ destIdx, item', h_item_id, h_toItem, h_item_mem, ?_ ⟩
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

def deliverOps {A : Type} (pre : List (Event (YjsOperation A))) : List (YjsOperation A) :=
  pre.filterMap eventDeliver

theorem interpHistory_eq_effect_deliverOps {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))} {state : YjsState A} :
  interpHistory pre Operation.init = Except.ok state →
  effect_list (deliverOps pre) Operation.init = Except.ok state := by
  intro h_interp
  simpa [interpHistory, interpOps, deliverOps] using h_interp

theorem deliver_insert_mem_deliverOps {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))} {x : IntegrateInput A} :
  Event.Deliver (YjsOperation.insert x) ∈ pre →
  YjsOperation.insert x ∈ deliverOps pre := by
  intro h_mem
  unfold deliverOps
  exact List.mem_filterMap.2 ⟨ Event.Deliver (YjsOperation.insert x), h_mem, by simp [eventDeliver] ⟩

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
          rw [ok_bind] at h_interp
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

theorem interpHistory_find?_exists_deliver_insert {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))}
  {state : YjsState A}
  {id : YjsId}
  {item : YjsItem A} :
  interpHistory pre Operation.init = Except.ok state →
  state.find? (fun i => i.id = id) = some item →
  ∃ input, Event.Deliver (YjsOperation.insert input) ∈ pre ∧ input.id = id := by
  intro h_interp h_find
  have h_item_mem : item ∈ state.items := by
    simpa [YjsState.find?] using Array.mem_of_find?_eq_some h_find
  have h_ptr_in : ArrSet state.toList (YjsPtr.itemPtr item) := by
    simpa [ArrSet, YjsState.toList] using h_item_mem
  have h_from_interp := interpOps_ArrSet (A := A) (items := pre)
    (state := state) (init := Operation.init) (x := item) h_interp h_ptr_in
  cases h_from_interp with
  | inl h_in_init =>
    obtain ⟨ y, h_y_init, h_y_id ⟩ := h_in_init
    have h_y_nil : y ∈ ([] : List (YjsItem A)) := by
      simpa [ArrSet, Operation.init, YjsEmptyArray, YjsState.toList] using h_y_init
    cases h_y_nil
  | inr h_in_pre =>
    obtain ⟨ input, h_input_id, h_input_mem ⟩ := h_in_pre
    have h_find_items : state.items.find? (fun i => i.id = id) = some item := by
      simpa [YjsState.find?] using h_find
    have h_item_id : item.id = id := by
      rw [Array.find?_eq_some_iff_getElem] at h_find_items
      simpa using h_find_items.1
    refine ⟨ input, h_input_mem, ?_ ⟩
    exact h_input_id.trans h_item_id

def IsStateAt {A M} [DecidableEq A] [Operation A] [DecidableEq M] [Message A M] [ValidMessage A] {network : OperationNetwork A} (a : A) (arr : Operation.State A) : Prop :=
  ∃i hist1 hist2, network.histories i = hist1 ++ [Event.Broadcast a] ++ hist2 ∧
    interpHistory hist1 Operation.init = Except.ok arr ∧
    ValidMessage.isValidMessage arr a

theorem OriginReachable_HappensBefore {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {i : ClientId} {a b : YjsOperation A} {inputA inputB : IntegrateInput A} {itemA itemB : YjsItem A} {state_a state_b : YjsState A}:
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
      simpa [ArrSet, Operation.init, YjsEmptyArray, YjsState.toList] using h_y_init
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

theorem deleteItemById_isValid {A : Type} [DecidableEq A] (item : YjsItem A) (id : YjsId) :
  item.isValid → item.isValid := by
  intro h_valid
  exact h_valid

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
  (input : IntegrateInput A) (arr : YjsState A) (item : YjsItem A) (deletedId : YjsId) :
  input.toItem arr.items = Except.ok item →
  item.isValid →
  ∃ item', input.toItem (deleteById arr deletedId).items = Except.ok item' ∧ item'.isValid := by
  intro h_toItem h_valid
  refine ⟨ item, ?_, h_valid ⟩
  exact IntegrateInput.toItem_deleteById_ok input arr item deletedId h_toItem

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b sa sb h_a_mem h_b_mem h_a_b_happens_before havalid hbvalid hab
  intro h_ab
  cases a with
  | insert aInput =>
    cases b with
    | insert bInput =>
      simp [Operation.effect, integrateValidState] at h_ab ⊢
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
        have h_a_ok_items : integrateSafe aInput sa.items = Except.ok arr2.items := by
          cases hsafe : integrateSafe aInput sa.items with
          | error err => simp [YjsState.insert, hsafe] at h_a_ok
          | ok arr =>
            simp [YjsState.insert, hsafe] at h_a_ok
            cases h_a_ok
            simpa [hsafe]
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
                simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find
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
                simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find

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
            simpa [ArrSet, YjsState.toList] using h_b_in_sa_arrset

          have ⟨ idx_a, _, h_arr2_def, _ ⟩ :=
            YjsArrInvariant_integrateSafe aInput aItem sa.items arr2.items h_sa_inv h_a_toItem h_a_item_valid h_a_ok_items

          have h_b_in_arr2 : bItem ∈ (show Array (YjsItem A) from arr2) := by
            rw [h_arr2_def]
            by_cases hle : idx_a ≤ Array.size sa.items
            · simp [Array.insertIdxIfInBounds, hle, Array.mem_insertIdx, h_b_in_sa]
            · exfalso
              omega

          have h_b_item_id : bItem.id = bInput.id :=
            IntegrateInput.toItem_id_eq bInput sa bItem h_b_toItem

          have h_clock_false : isClockSafe bInput.id arr2.items = false := by
            unfold isClockSafe
            simp
            rw [Array.mem_iff_getElem] at h_b_in_arr2
            obtain ⟨ i, hi, hget ⟩ := h_b_in_arr2
            refine ⟨ i, hi, ?_ ⟩
            constructor
            · simp [hget, h_b_item_id]
            · simp [hget, h_b_item_id]

          have h_clock_true : isClockSafe bInput.id arr2.items = true := by
            simp [YjsState.insert, integrateSafe] at h_b_ok
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
                simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find
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
                simpa [YjsState.toList] using Array.mem_of_find?_eq_some h_find

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
            simpa [ArrSet, YjsState.toList] using h_a_in_sa_arrset

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
            simp [YjsState.insert, integrateSafe] at h_a_ok
            split at h_a_ok
            · assumption
            · simp at h_a_ok

          rw [h_clock_false] at h_clock_true
          contradiction
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
  (input : IntegrateInput A) (s s' : YjsState A) :
  s.insert input = Except.ok s' →
  ∃ item, item.id = input.id ∧ item ∈ s'.items := by
  intro h_ok
  have h_integrate : integrate input s.items = Except.ok s'.items := by
    have h_safe : integrateSafe input s.items = Except.ok s'.items := by
      cases hsafe : integrateSafe input s.items with
      | error err =>
        simp [YjsState.insert, hsafe] at h_ok
      | ok arr =>
        simp [YjsState.insert, hsafe] at h_ok
        cases h_ok
        simpa [hsafe]
    unfold integrateSafe at h_safe
    split at h_safe
    · exact h_safe
    · simp at h_safe
  unfold integrate at h_integrate
  obtain ⟨ leftIdx, h_left, h1 ⟩ := Except.bind_eq_ok_exist h_integrate
  obtain ⟨ rightIdx, h_right, h2 ⟩ := Except.bind_eq_ok_exist h1
  obtain ⟨ destIdx, h_dest, h3 ⟩ := Except.bind_eq_ok_exist h2
  obtain ⟨ item, h_item, h4 ⟩ := Except.bind_eq_ok_exist h3
  have h_arr'_eq : s'.items = s.items.insertIdxIfInBounds destIdx item := by
    simpa [pure, Except.pure] using h4.symm
  have h_item_id : item.id = input.id := by
    cases hleft : getPtrExcept s.items leftIdx with
    | error err =>
      simp [mkItemByIndex, hleft] at h_item
      cases h_item
    | ok leftPtr =>
      cases hright : getPtrExcept s.items rightIdx with
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
  have h_right_le : rightIdx ≤ s.items.size := findRightIdx_ok_le_size h_right
  have h_left_lt : leftIdx < s.items.size := findLeftIdx_ok_lt_size h_left
  have h_dest_le : destIdx ≤ s.items.size := by
    exact findIntegratedIndex_ok_le_size_from_eq leftIdx rightIdx input s.items destIdx
      h_left_ge h_left_lt h_right_le h_dest
  refine ⟨ item, h_item_id, ?_ ⟩
  rw [h_arr'_eq]
  simp [Array.insertIdxIfInBounds, h_dest_le]
  exact (Array.mem_insertIdx (a := item) (b := item) (xs := s.items) (h := h_dest_le)).2 (Or.inl rfl)

theorem effect_preserves_id_exists {A : Type} [DecidableEq A]
  (op : YjsOperation A) (s s' : YjsState A) (targetId : YjsId) :
  Operation.effect op s = Except.ok s' →
  (∃ item, item ∈ s.items ∧ item.id = targetId) →
  (∃ item', item' ∈ s'.items ∧ item'.id = targetId) := by
  intro h_eff h_exists
  cases op with
  | delete _ deletedId =>
    simp [Operation.effect, deleteValid] at h_eff
    subst h_eff
    obtain ⟨ item, h_mem, h_id ⟩ := h_exists
    refine ⟨ item, ?_, h_id ⟩
    simpa [deleteById] using h_mem
  | insert input =>
    simp [Operation.effect] at h_eff
    obtain ⟨ item0, h_mem0, h_id0 ⟩ := h_exists
    obtain ⟨ i, newItem, h_new_id, _h_toItem, _h_item_mem, h_s' ⟩ :=
      integrateValid_exists_insertIdxIfBounds (init := s) (input := input) (state' := s') h_eff
    refine ⟨ item0, ?_, h_id0 ⟩
    rw [h_s']
    simp [Array.insertIdxIfInBounds]
    split
    · exact (Array.mem_insertIdx (a := item0) (b := newItem) (xs := s.items) (h := by assumption)).2 (Or.inr h_mem0)
    · simpa [*] using h_mem0

theorem effect_list_preserves_id_exists {A : Type} [DecidableEq A]
  (ops : List (YjsOperation A)) (s0 s : YjsState A) (targetId : YjsId) :
  effect_list ops s0 = Except.ok s →
  (∃ item, item ∈ s0.items ∧ item.id = targetId) →
  (∃ item', item' ∈ s.items ∧ item'.id = targetId) := by
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
    · simpa [*] using h_mem

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

theorem insert_preserves_uniqueId {A : Type} [DecidableEq A]
  (s s' : YjsState A) (input : IntegrateInput A) :
  uniqueId s.toList →
  s.insert input = Except.ok s' →
  uniqueId s'.toList := by
  intro h_unique h_insert
  have h_safe : integrateSafe input s.items = Except.ok s'.items := by
    cases hsafe : integrateSafe input s.items with
    | error err => simp [YjsState.insert, hsafe] at h_insert
    | ok arr =>
      simp [YjsState.insert, hsafe] at h_insert
      cases h_insert
      simpa [hsafe]
  have h_clock : isClockSafe input.id s.items = true := by
    have h_safe0 := h_safe
    unfold integrateSafe at h_safe0
    split at h_safe0
    · assumption
    · cases h_safe0
  have h_integrate : integrate input s.items = Except.ok s'.items := by
    unfold integrateSafe at h_safe
    rw [h_clock] at h_safe
    simpa using h_safe
  unfold integrate at h_integrate
  obtain ⟨ leftIdx, h_left, h1 ⟩ := Except.bind_eq_ok_exist h_integrate
  obtain ⟨ rightIdx, h_right, h2 ⟩ := Except.bind_eq_ok_exist h1
  obtain ⟨ destIdx, h_dest, h3 ⟩ := Except.bind_eq_ok_exist h2
  obtain ⟨ item, h_item, h4 ⟩ := Except.bind_eq_ok_exist h3
  have h_arr'_eq : s'.items = s.items.insertIdxIfInBounds destIdx item := by
    simpa [pure, Except.pure] using h4.symm
  have h_item_id : item.id = input.id := by
    cases hleft : getPtrExcept s.items leftIdx with
    | error err =>
      simp [mkItemByIndex, hleft] at h_item
      cases h_item
    | ok leftPtr =>
      cases hright : getPtrExcept s.items rightIdx with
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
  have h_right_le : rightIdx ≤ s.items.size := findRightIdx_ok_le_size h_right
  have h_left_lt : leftIdx < s.items.size := findLeftIdx_ok_lt_size h_left
  have h_dest_le : destIdx ≤ s.items.size := by
    exact findIntegratedIndex_ok_le_size_from_eq leftIdx rightIdx input s.items destIdx h_left_ge h_left_lt h_right_le h_dest
  have h_clock_all := h_clock
  simp [isClockSafe] at h_clock_all
  have h_new_id_neq : ∀ a, a ∈ s.items → item.id ≠ a.id := by
    intro a hmem h_eq
    rcases (Array.mem_iff_getElem.mp hmem) with ⟨ i, hi, hget ⟩
    have h_or := h_clock_all i hi
    have h_id_eq : s.items[i].id = input.id := by
      calc
        s.items[i].id = a.id := by simpa [hget]
        _ = item.id := h_eq.symm
        _ = input.id := h_item_id
    have h_client_eq : s.items[i].id.clientId = input.id.clientId := by
      simpa using congrArg YjsId.clientId h_id_eq
    have h_lt_clock : s.items[i].id.clock < input.id.clock := by
      cases h_or with
      | inl h_not => exact False.elim (h_not h_client_eq)
      | inr hlt => exact hlt
    have h_eq_clock : s.items[i].id.clock = input.id.clock := by
      simpa using congrArg YjsId.clock h_id_eq
    omega
  have h_pair_insert :
      List.Pairwise (fun x y : YjsItem A => x.id ≠ y.id) (s.items.toList.insertIdx destIdx item) := by
    refine List.Pairwise_insertIdx (R := fun x y : YjsItem A => x.id ≠ y.id) (l := s.items.toList) (i := destIdx) (newItem := item) ?_ ?_ ?_ ?_
    · simpa [Array.length_toList] using h_dest_le
    · simpa [uniqueId, YjsState.toList] using h_unique
    · intro j hji
      have hjlen : j < s.items.toList.length := by
        have : j < s.items.size := lt_of_lt_of_le hji h_dest_le
        simpa [Array.length_toList] using this
      have hmem_list : s.items.toList[j] ∈ s.items.toList := List.getElem_mem (l := s.items.toList) (h := hjlen)
      have hmem_arr : s.items.toList[j] ∈ s.items := by
        simpa [YjsState.toList] using hmem_list
      have hneq : item.id ≠ (s.items.toList[j]).id := h_new_id_neq _ hmem_arr
      simpa [ne_comm] using hneq
    · intro j hji hjlen
      have hmem_list : s.items.toList[j] ∈ s.items.toList := List.getElem_mem (l := s.items.toList) (h := hjlen)
      have hmem_arr : s.items.toList[j] ∈ s.items := by
        simpa [YjsState.toList] using hmem_list
      exact h_new_id_neq _ hmem_arr
  simpa [uniqueId, YjsState.toList, h_arr'_eq, List.insertIdxIfInBounds_toArray, Array.insertIdxIfInBounds, h_dest_le] using h_pair_insert

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

theorem effect_list_find?_exists_insert_id {A : Type} [DecidableEq A]
  {ops : List (YjsOperation A)} {state : YjsState A} {id : YjsId} {item : YjsItem A} :
  effect_list ops Operation.init = Except.ok state →
  state.find? (fun i => i.id = id) = some item →
  ∃ input, YjsOperation.insert input ∈ ops ∧ input.id = id := by
  intro h_eff h_find
  have h_filterMap_deliver :
      ∀ xs : List (YjsOperation A), List.filterMap (eventDeliver ∘ Event.Deliver) xs = xs := by
    intro xs
    induction xs with
    | nil =>
      simp
    | cons op xs ih =>
      simpa [List.filterMap, eventDeliver, Function.comp] using congrArg (List.cons op) ih
  have h_interp : interpHistory (ops.map Event.Deliver) Operation.init = Except.ok state := by
    unfold interpHistory interpOps
    rw [List.filterMap_map]
    calc
      effect_list (List.filterMap (eventDeliver ∘ Event.Deliver) ops) Operation.init
          = effect_list ops Operation.init := by
            simpa [h_filterMap_deliver ops]
      _ = Except.ok state := h_eff
  obtain ⟨ input, h_mem_hist, h_id ⟩ :=
    interpHistory_find?_exists_deliver_insert (A := A)
      (pre := ops.map Event.Deliver) (state := state) (id := id) (item := item)
      h_interp h_find
  have h_mem_ops : YjsOperation.insert input ∈ ops := by
    simpa using h_mem_hist
  exact ⟨ input, h_mem_ops, h_id ⟩

theorem effect_list_split_at_mem {A : Type} [DecidableEq A]
  {ops : List (YjsOperation A)} {op : YjsOperation A} {s : YjsState A} :
  effect_list ops Operation.init = Except.ok s →
  op ∈ ops →
  ∃ ops₀ ops₁ s₀,
    ops = ops₀ ++ op :: ops₁ ∧
    effect_list ops₀ Operation.init = Except.ok s₀ := by
  intro h_eff h_mem
  rcases List.mem_iff_append.mp h_mem with ⟨ ops₀, ops₁, h_split ⟩
  subst h_split
  have h_bind :
      (do
        let s' ← effect_list ops₀ Operation.init
        effect_list (op :: ops₁) s') = Except.ok s := by
    simpa [effect_list_append] using h_eff
  obtain ⟨ s₀, h_pre, _h_tail ⟩ := Except.bind_eq_ok_exist h_bind
  exact ⟨ ops₀, ops₁, s₀, rfl, h_pre ⟩

theorem find_implies_insert_mem_preOps {A : Type} [DecidableEq A]
  {preOps : List (YjsOperation A)} {state₀ : YjsState A}
  {oid : YjsId} {originItem : YjsItem A} :
  effect_list preOps Operation.init = Except.ok state₀ →
  state₀.find? (fun i => i.id = oid) = some originItem →
  ∃ op, YjsOperation.insert op ∈ preOps ∧ op.id = oid := by
  intro h_eff h_find
  exact effect_list_find?_exists_insert_id (ops := preOps) (state := state₀) (id := oid) (item := originItem) h_eff h_find

theorem split_preOps_at_insert {A : Type} [DecidableEq A]
  {preOps : List (YjsOperation A)} {op : IntegrateInput A} {state : YjsState A} :
  effect_list preOps Operation.init = Except.ok state →
  YjsOperation.insert op ∈ preOps →
  ∃ ops0 ops1 s0,
    preOps = ops0 ++ [YjsOperation.insert op] ++ ops1 ∧
    effect_list ops0 Operation.init = Except.ok s0 := by
  intro h_eff h_mem
  obtain ⟨ ops0, ops1, s0, h_split, h_pre ⟩ :=
    effect_list_split_at_mem (ops := preOps) (op := YjsOperation.insert op) (s := state) h_eff h_mem
  exact ⟨ ops0, ops1, s0, by simpa using h_split, h_pre ⟩

theorem split_prefix_toItem_originItem {A : Type} [DecidableEq A]
  {preOps : List (YjsOperation A)} {state₀ : YjsState A}
  {oid : YjsId} {originItem : YjsItem A}
  {op : IntegrateInput A} {ops0 ops1 : List (YjsOperation A)} {s0 : YjsState A} :
  effect_list preOps Operation.init = Except.ok state₀ →
  IdNoDup preOps →
  state₀.find? (fun i => i.id = oid) = some originItem →
  op.id = oid →
  preOps = ops0 ++ [YjsOperation.insert op] ++ ops1 →
  effect_list ops0 Operation.init = Except.ok s0 →
  op.toItem s0.items = Except.ok originItem := by
  intro h_eff h_nodup h_find h_op_id h_split h_pre
  subst h_split
  have h_bind :
      (do
        let s' ← effect_list ops0 Operation.init
        effect_list (YjsOperation.insert op :: ops1) s') = Except.ok state₀ := by
    simpa [effect_list_append] using h_eff
  obtain ⟨ s_mid, h_pre_mid, h_tail_mid ⟩ := Except.bind_eq_ok_exist h_bind
  have hs_mid : s_mid = s0 := by
    rw [h_pre] at h_pre_mid
    cases h_pre_mid
    rfl
  cases hs_mid
  have h_tail :
      effect_list (YjsOperation.insert op :: ops1) s0 = Except.ok state₀ := by
    simpa using h_tail_mid
  have h_tail_bind :
      (do
        let s' ← Operation.effect (YjsOperation.insert op) s0
        effect_list ops1 s') = Except.ok state₀ := by
    simpa [effect_list] using h_tail
  obtain ⟨ s1, h_insert_eff, h_rest_eff ⟩ := Except.bind_eq_ok_exist h_tail_bind
  have h_insert_state : s0.insert op = Except.ok s1 := by
    simpa [Operation.effect] using h_insert_eff
  obtain ⟨ _i, insertedItem, h_inserted_id, h_toItem, h_inserted_mem_s1, _h_s1 ⟩ :=
    integrateValid_exists_insertIdxIfBounds (init := s0) (input := op) (state' := s1) h_insert_state
  have h_inserted_mem_state0 : insertedItem ∈ state₀.items := by
    exact effect_list_preserves_mem (ops := ops1) (s0 := s1) (s := state₀) (item := insertedItem)
      h_rest_eff h_inserted_mem_s1
  have h_unique_state0 : uniqueId state₀.toList := by
    exact effect_list_uniqueId_from_IdNoDup (ops := ops0 ++ [YjsOperation.insert op] ++ ops1) (s := state₀)
      h_nodup h_eff
  have h_inserted_oid : insertedItem.id = oid := by
    simpa [h_op_id] using h_inserted_id
  have h_find_inserted : state₀.find? (fun i => i.id = oid) = some insertedItem := by
    apply exists_find?_eq_some_of_exists_mem_id (arr := state₀.items) (targetId := oid) (item := insertedItem)
    · simpa [YjsState.toList] using h_inserted_mem_state0
    · exact h_inserted_oid
    · simpa [YjsState.toList] using h_unique_state0
  have h_item_eq : insertedItem = originItem := by
    apply Option.some.inj
    calc
      some insertedItem = state₀.find? (fun i => i.id = oid) := by
        symm
        exact h_find_inserted
      _ = some originItem := h_find
  simpa [h_item_eq] using h_toItem

theorem insert_mem_l_from_pre_deliver {A : Type} [DecidableEq A]
  {pre : List (Event (YjsOperation A))} {l : List (YjsOperation A)}
  {op : IntegrateInput A} :
  (∀ x, Event.Deliver (YjsOperation.insert x) ∈ pre → YjsOperation.insert x ∈ l) →
  Event.Deliver (YjsOperation.insert op) ∈ pre →
  YjsOperation.insert op ∈ l := by
  intro h_pre_deliver_in_l h_mem
  exact h_pre_deliver_in_l op h_mem

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
  · simpa [List.append_assoc, h_eq]
  · exact h_lt

theorem dep_ids_exist_in_source_prefix {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {op : IntegrateInput A} {j : ClientId}
  {preHist postHist : List (Event (YjsOperation A))} {s : YjsState A} {item : YjsItem A} :
  network.histories j = preHist ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist ->
  interpHistory preHist Operation.init = Except.ok s ->
  op.toItem s.items = Except.ok item ->
  (match op.originId with
    | none => True
    | some oid => exists o, Event.Deliver (YjsOperation.insert o) ∈ preHist /\ o.id = oid) /\
  (match op.rightOriginId with
    | none => True
    | some rid => exists r, Event.Deliver (YjsOperation.insert r) ∈ preHist /\ r.id = rid) := by
  intro _h_hist h_interp h_toItem
  constructor
  · cases h_originId : op.originId with
    | none =>
      simp [h_originId]
    | some oid =>
      cases h_find_origin : s.find? (fun i => i.id = oid) with
      | none =>
        have h_find_origin_arr : s.items.find? (fun i => i.id = oid) = none := by
          simpa [YjsState.find?] using h_find_origin
        exfalso
        cases h_rightOriginId : op.rightOriginId with
        | none =>
          simp [IntegrateInput.toItem, h_originId, h_find_origin_arr, h_rightOriginId, bind, Except.bind] at h_toItem
        | some rid =>
          simp [IntegrateInput.toItem, h_originId, h_find_origin_arr, h_rightOriginId, bind, Except.bind] at h_toItem
      | some originItem =>
        have h_find_origin' : s.find? (fun i => i.id = oid) = some originItem := h_find_origin
        obtain ⟨ o, h_mem, h_id ⟩ :=
          interpHistory_find?_exists_deliver_insert (A := A)
            (pre := preHist) (state := s) (id := oid) (item := originItem)
            h_interp h_find_origin'
        exact ⟨ o, h_mem, h_id ⟩
  · cases h_rightOriginId : op.rightOriginId with
    | none =>
      simp [h_rightOriginId]
    | some rid =>
      cases h_find_right : s.find? (fun i => i.id = rid) with
      | none =>
        have h_find_right_arr : s.items.find? (fun i => i.id = rid) = none := by
          simpa [YjsState.find?] using h_find_right
        exfalso
        cases h_originId : op.originId with
        | none =>
          simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_find_right_arr, bind, Except.bind] at h_toItem
        | some oid =>
          cases h_find_origin_arr : s.items.find? (fun item => item.id = oid) with
          | none =>
            simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_find_right_arr, h_find_origin_arr, bind, Except.bind] at h_toItem
          | some originItem =>
            simp [IntegrateInput.toItem, h_originId, h_rightOriginId, h_find_right_arr, h_find_origin_arr, bind, Except.bind] at h_toItem
      | some rightItem =>
        have h_find_right' : s.find? (fun i => i.id = rid) = some rightItem := h_find_right
        obtain ⟨ r, h_mem, h_id ⟩ :=
          interpHistory_find?_exists_deliver_insert (A := A)
            (pre := preHist) (state := s) (id := rid) (item := rightItem)
            h_interp h_find_right'
        exact ⟨ r, h_mem, h_id ⟩

theorem dep_insert_lt_target {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {j : ClientId}
  {preHist postHist : List (Event (YjsOperation A))}
  {dep target : IntegrateInput A} :
  network.histories j = preHist ++ [Event.Broadcast (YjsOperation.insert target)] ++ postHist ->
  Event.Deliver (YjsOperation.insert dep) ∈ preHist ->
  (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
    (YjsOperation.insert dep) (YjsOperation.insert target) := by
  intro h_hist h_mem
  have h_hist' : network.histories j =
      preHist ++ Event.Broadcast (YjsOperation.insert target) :: postHist := by
    simpa [List.singleton_append, List.append_assoc] using h_hist
  exact pre_deliver_lt_insert (network := network) (i := j) (pre := preHist)
    (post := postHist) (x := dep) (input := target) h_hist' h_mem

theorem hbClosed_predecessor_in_prefix {A : Type} [DecidableEq A]
  {hb : CausalOrder (YjsOperation A)}
  {l l' l'' : List (YjsOperation A)} {dep target : YjsOperation A} :
  hbClosed hb l ->
  l = l' ++ [target] ++ l'' ->
  dep < target ->
  dep ∈ l' := by
  intro h_closed h_split h_lt
  have h_split' : l = l' ++ target :: l'' := by
    simpa [List.singleton_append, List.append_assoc] using h_split
  exact h_closed target dep l' l'' h_split' h_lt

theorem prefix_find_exact_by_id {A : Type} [DecidableEq A]
  {ops : List (YjsOperation A)} {s : YjsState A}
  {oid : YjsId} {item : YjsItem A} :
  effect_list ops Operation.init = Except.ok s ->
  IdNoDup ops ->
  (exists op, YjsOperation.insert op ∈ ops /\ op.id = oid) ->
  s.find? (fun i => i.id = oid) = some item ->
  forall item', s.find? (fun i => i.id = oid) = some item' -> item' = item := by
  intro _h_eff _h_nodup _h_exists h_find item' h_find'
  rw [h_find] at h_find'
  cases h_find'
  rfl

theorem prefix_find_exists_by_insert_mem {A : Type} [DecidableEq A]
  {ops : List (YjsOperation A)} {s : YjsState A} {dep : IntegrateInput A} :
  effect_list ops Operation.init = Except.ok s ->
  IdNoDup ops ->
  YjsOperation.insert dep ∈ ops ->
  exists depItem, s.find? (fun i => i.id = dep.id) = some depItem := by
  intro h_eff h_nodup h_dep_mem
  obtain ⟨ ops0, ops1, s0, h_split, h_ops0_eff ⟩ :=
    split_preOps_at_insert
      (preOps := ops) (op := dep) (state := s) h_eff h_dep_mem
  subst h_split
  have h_bind :
      (do
        let s' ← effect_list ops0 Operation.init
        effect_list (YjsOperation.insert dep :: ops1) s') = Except.ok s := by
    simpa [effect_list_append] using h_eff
  obtain ⟨ sMid, h_ops0_eff', h_tail_eff ⟩ := Except.bind_eq_ok_exist h_bind
  have h_sMid_eq : sMid = s0 := by
    rw [h_ops0_eff] at h_ops0_eff'
    cases h_ops0_eff'
    rfl
  have h_tail_eff' : effect_list (YjsOperation.insert dep :: ops1) s0 = Except.ok s := by
    simpa [h_sMid_eq] using h_tail_eff
  have h_tail_bind :
      (do
        let s' ← Operation.effect (YjsOperation.insert dep) s0
        effect_list ops1 s') = Except.ok s := by
    simpa [effect_list] using h_tail_eff'
  obtain ⟨ sAfterInsert, h_insert_eff, h_suffix_eff ⟩ := Except.bind_eq_ok_exist h_tail_bind
  simp [Operation.effect] at h_insert_eff
  obtain ⟨ _idx, insertedItem, h_inserted_id, _h_toItem, h_inserted_mem, _h_state_eq ⟩ :=
    integrateValid_exists_insertIdxIfBounds (init := s0) (input := dep) (state' := sAfterInsert) h_insert_eff
  have h_inserted_mem_final : insertedItem ∈ s.items := by
    exact effect_list_preserves_mem
      (ops := ops1) (s0 := sAfterInsert) (s := s) (item := insertedItem)
      h_suffix_eff h_inserted_mem
  have h_unique_s : uniqueId s.toList := by
    exact effect_list_uniqueId_from_IdNoDup (ops := ops0 ++ [YjsOperation.insert dep] ++ ops1) (s := s) h_nodup h_eff
  have h_find_inserted :
      s.find? (fun i => i.id = dep.id) = some insertedItem := by
    apply exists_find?_eq_some_of_exists_mem_id (arr := s.items) (targetId := dep.id) (item := insertedItem)
    · simpa [YjsState.toList] using h_inserted_mem_final
    · exact h_inserted_id
    · simpa [YjsState.toList] using h_unique_s
  exact ⟨ insertedItem, h_find_inserted ⟩

theorem IdNoDup_mem_id_eq_imp_eq {A S : Type} [DecidableEq A] [DecidableEq S] [WithId A S]
  {ops : List A} {x y : A} :
  IdNoDup ops ->
  x ∈ ops ->
  y ∈ ops ->
  WithId.id x = WithId.id y ->
  x = y := by
  intro h_nodup h_mem_x h_mem_y h_id_eq
  induction ops generalizing x y with
  | nil =>
    cases h_mem_x
  | cons a ops ih =>
    have h_pair := List.pairwise_cons.mp h_nodup
    have h_head_tail : ∀ b, b ∈ ops -> WithId.id a ≠ WithId.id b := h_pair.1
    have h_tail_nodup : IdNoDup ops := h_pair.2
    simp at h_mem_x h_mem_y
    cases h_mem_x with
    | inl h_x_eq =>
      subst h_x_eq
      cases h_mem_y with
      | inl h_y_eq =>
        exact h_y_eq.symm
      | inr h_y_tail =>
        exfalso
        exact (h_head_tail y h_y_tail) h_id_eq
    | inr h_x_tail =>
      cases h_mem_y with
      | inl h_y_eq =>
        subst h_y_eq
        exfalso
        exact (h_head_tail x h_x_tail) h_id_eq.symm
      | inr h_y_tail =>
        exact ih h_tail_nodup h_x_tail h_y_tail h_id_eq

theorem toItem_prefix_invariant {A : Type} [DecidableEq A]
  {hb : CausalOrder (YjsOperation A)} {network : YjsOperationNetwork A}
  {op : IntegrateInput A} {item : YjsItem A}
  {l1 l2 l1' l1'' l2' l2'' : List (YjsOperation A)}
  {s1 s2 : YjsState A} :
  hb_consistent hb l1 ->
  hb_consistent hb l2 ->
  hbClosed hb l1 ->
  hbClosed hb l2 ->
  IdNoDup l1 ->
  IdNoDup l2 ->
  l1 = l1' ++ [YjsOperation.insert op] ++ l1'' ->
  l2 = l2' ++ [YjsOperation.insert op] ++ l2'' ->
  effect_list l1' Operation.init = Except.ok s1 ->
  effect_list l2' Operation.init = Except.ok s2 ->
  hb = instCausalNetworkElemCausalOrder network.toCausalNetwork ->
  (exists j, Event.Broadcast (YjsOperation.insert op) ∈ network.histories j) ->
  op.toItem s1.items = Except.ok item ->
  op.toItem s2.items = Except.ok item := by
  intro h_cons1 h_cons2 h_closed1 h_closed2 h_nodup1 h_nodup2
    h_split1 h_split2 h_eff1 h_eff2 h_hb_eq h_source h_toItem
  have h_hb_eq' : hb = instCausalNetworkElemCausalOrder network.toCausalNetwork := h_hb_eq
  clear h_hb_eq
  have h_l1'_sublist : l1'.Sublist l1 := by
    rw [h_split1]
    simpa [List.append_assoc] using
      (List.sublist_append_left l1' ([YjsOperation.insert op] ++ l1''))
  have h_l2'_sublist : l2'.Sublist l2 := by
    rw [h_split2]
    simpa [List.append_assoc] using
      (List.sublist_append_left l2' ([YjsOperation.insert op] ++ l2''))
  have h_nodup_l1' : IdNoDup l1' := List.Pairwise.sublist h_l1'_sublist h_nodup1
  have h_nodup_l2' : IdNoDup l2' := List.Pairwise.sublist h_l2'_sublist h_nodup2
  obtain ⟨ j, h_source_mem ⟩ := h_source
  rw [List.mem_iff_append] at h_source_mem
  obtain ⟨ preHist, postHist, h_hist_src ⟩ := h_source_mem
  have h_hist_src' :
      network.histories j = preHist ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist := by
    simpa [List.singleton_append, List.append_assoc] using h_hist_src
  have h_valid_at_src :
      ∃ sSrc,
        interpHistory preHist Operation.init = Except.ok sSrc ∧
        ValidMessage.isValidMessage sSrc (YjsOperation.insert op) := by
    have h_hist_src_for_valid :
        preHist ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist =
          network.histories j := by
      simpa using h_hist_src'.symm
    simpa using
      (network.broadcast_only_valid_messages j (pre := preHist) (post := postHist)
        (e := YjsOperation.insert op) h_hist_src_for_valid)
  obtain ⟨ sSrc, h_interp_src, h_valid_src ⟩ := h_valid_at_src
  obtain ⟨ srcItem, h_toItem_src, _h_srcItem_valid ⟩ :
      ∃ it, op.toItem sSrc.items = Except.ok it ∧ it.isValid := by
    simpa [ValidMessage.isValidMessage, IsValidMessage] using h_valid_src
  have h_dep_from_source :
      (match op.originId with
        | none => True
        | some oid => exists o, Event.Deliver (YjsOperation.insert o) ∈ preHist /\ o.id = oid) /\
      (match op.rightOriginId with
        | none => True
        | some rid => exists r, Event.Deliver (YjsOperation.insert r) ∈ preHist /\ r.id = rid) := by
    exact dep_ids_exist_in_source_prefix
      (network := network) (op := op) (j := j)
      (preHist := preHist) (postHist := postHist) (s := sSrc) (item := srcItem)
      h_hist_src' h_interp_src h_toItem_src
  -- Step 3.5(a): dependency resolution on both sides (s1/s2)
  have h_dep_left :
    (match op.originId with
      | none => True
      | some oid => exists io, s1.find? (fun i => i.id = oid) = some io) := by
    cases h_originId : op.originId with
    | none =>
      simp [h_originId]
    | some oid =>
      have h_find : s1.find? (fun i => i.id = oid) ≠ none := by
        -- derived from `toItem = ok` in `s1`
        intro hnone
        have hnone_arr : s1.items.find? (fun i => i.id = oid) = none := by
          simpa [YjsState.find?] using hnone
        cases h_rightOriginId : op.rightOriginId with
        | none =>
          simp [IntegrateInput.toItem, h_originId, hnone_arr, h_rightOriginId, bind, Except.bind] at h_toItem
        | some rid =>
          simp [IntegrateInput.toItem, h_originId, hnone_arr, h_rightOriginId, bind, Except.bind] at h_toItem
      cases h_find_some : s1.find? (fun i => i.id = oid) with
      | none =>
        exfalso
        exact h_find h_find_some
      | some io =>
        exact ⟨ io, h_find_some ⟩
  have h_dep_right :
    (match op.rightOriginId with
      | none => True
      | some rid => exists ir, s1.find? (fun i => i.id = rid) = some ir) := by
    cases h_rightOriginId : op.rightOriginId with
    | none =>
      simp [h_rightOriginId]
    | some rid =>
      have h_find : s1.find? (fun i => i.id = rid) ≠ none := by
        intro hnone
        have hnone_arr : s1.items.find? (fun i => i.id = rid) = none := by
          simpa [YjsState.find?] using hnone
        cases h_originId : op.originId with
        | none =>
          simp [IntegrateInput.toItem, h_originId, h_rightOriginId, hnone_arr, bind, Except.bind] at h_toItem
        | some oid =>
          cases h_find_origin_arr : s1.items.find? (fun i => i.id = oid) with
          | none =>
            simp [IntegrateInput.toItem, h_originId, h_rightOriginId, hnone_arr, h_find_origin_arr, bind, Except.bind] at h_toItem
          | some io =>
            simp [IntegrateInput.toItem, h_originId, h_rightOriginId, hnone_arr, h_find_origin_arr, bind, Except.bind] at h_toItem
      cases h_find_some : s1.find? (fun i => i.id = rid) with
      | none =>
        exfalso
        exact h_find h_find_some
      | some ir =>
        exact ⟨ ir, h_find_some ⟩
  have h_dep_left' :
    (match op.originId with
      | none => True
      | some oid => exists io, s2.find? (fun i => i.id = oid) = some io) := by
    cases h_originId : op.originId with
    | none =>
      simp [h_originId]
    | some oid =>
      have h_dep_source_left :
          ∃ o, Event.Deliver (YjsOperation.insert o) ∈ preHist ∧ o.id = oid := by
        simpa [h_originId] using h_dep_from_source.1
      obtain ⟨ o, h_dep_mem_preHist, h_dep_id ⟩ := h_dep_source_left
      have h_dep_lt_net :
          (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
            (YjsOperation.insert o) (YjsOperation.insert op) := by
        exact dep_insert_lt_target
          (network := network) (j := j) (preHist := preHist) (postHist := postHist)
          (dep := o) (target := op) h_hist_src' h_dep_mem_preHist
      have h_dep_lt_hb : (YjsOperation.insert o) < (YjsOperation.insert op) := by
        simpa [h_hb_eq'] using h_dep_lt_net
      have h_dep_mem_l2' : YjsOperation.insert o ∈ l2' := by
        exact hbClosed_predecessor_in_prefix
          (hb := hb) (l := l2) (l' := l2') (l'' := l2'')
          (dep := YjsOperation.insert o) (target := YjsOperation.insert op)
          h_closed2 h_split2 h_dep_lt_hb
      obtain ⟨ io, h_find_io ⟩ :=
        prefix_find_exists_by_insert_mem
          (ops := l2') (s := s2) (dep := o) h_eff2 h_nodup_l2' h_dep_mem_l2'
      exact ⟨ io, by simpa [h_dep_id] using h_find_io ⟩
  have h_dep_right' :
    (match op.rightOriginId with
      | none => True
      | some rid => exists ir, s2.find? (fun i => i.id = rid) = some ir) := by
    cases h_rightOriginId : op.rightOriginId with
    | none =>
      simp [h_rightOriginId]
    | some rid =>
      have h_dep_source_right :
          ∃ r, Event.Deliver (YjsOperation.insert r) ∈ preHist ∧ r.id = rid := by
        simpa [h_rightOriginId] using h_dep_from_source.2
      obtain ⟨ r, h_dep_mem_preHist, h_dep_id ⟩ := h_dep_source_right
      have h_dep_lt_net :
          (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
            (YjsOperation.insert r) (YjsOperation.insert op) := by
        exact dep_insert_lt_target
          (network := network) (j := j) (preHist := preHist) (postHist := postHist)
          (dep := r) (target := op) h_hist_src' h_dep_mem_preHist
      have h_dep_lt_hb : (YjsOperation.insert r) < (YjsOperation.insert op) := by
        simpa [h_hb_eq'] using h_dep_lt_net
      have h_dep_mem_l2' : YjsOperation.insert r ∈ l2' := by
        exact hbClosed_predecessor_in_prefix
          (hb := hb) (l := l2) (l' := l2') (l'' := l2'')
          (dep := YjsOperation.insert r) (target := YjsOperation.insert op)
          h_closed2 h_split2 h_dep_lt_hb
      obtain ⟨ ir, h_find_ir ⟩ :=
        prefix_find_exists_by_insert_mem
          (ops := l2') (s := s2) (dep := r) h_eff2 h_nodup_l2' h_dep_mem_l2'
      exact ⟨ ir, by simpa [h_dep_id] using h_find_ir ⟩
  -- Step 3.5(b): dependency equality between s1 and s2
  have h_dep_eq_core :
    ∀ depIdOpt : Option YjsId,
      (match depIdOpt with
        | none => True
        | some did =>
          ∃ dep, Event.Deliver (YjsOperation.insert dep) ∈ preHist ∧ dep.id = did) ->
      (match depIdOpt with
        | none => True
        | some did =>
          forall i1 i2,
            s1.find? (fun i => i.id = did) = some i1 ->
            s2.find? (fun i => i.id = did) = some i2 ->
            i1 = i2) := by
    intro depIdOpt h_src_dep
    cases depIdOpt with
    | none =>
      simp
    | some did =>
      obtain ⟨ dep, h_dep_mem_preHist, h_dep_id ⟩ := by
        simpa using h_src_dep
      obtain ⟨ pre0, post0, h_dep_split ⟩ := List.mem_iff_append.mp h_dep_mem_preHist
      intro i1 i2 h_find1 h_find2
      have h_dep_eq_by_len :
          ∀ n did0 pre0 post0 dep,
            pre0.length = n ->
            preHist = pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0 ->
            dep.id = did0 ->
            ∀ i1 i2,
              s1.find? (fun i => i.id = did0) = some i1 ->
              s2.find? (fun i => i.id = did0) = some i2 ->
              i1 = i2 := by
        intro n
        induction' n using Nat.strong_induction_on with n ih
        intro did0 pre0 post0 dep h_len h_split_src h_dep_id' i1 i2 h_find1 h_find2
        have h_dep_mem_preHist' :
            Event.Deliver (YjsOperation.insert dep) ∈ preHist := by
          rw [h_split_src]
          simp
        have h_dep_lt_net :
            (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
              (YjsOperation.insert dep) (YjsOperation.insert op) := by
          exact dep_insert_lt_target
            (network := network) (j := j) (preHist := preHist) (postHist := postHist)
            (dep := dep) (target := op) h_hist_src' h_dep_mem_preHist'
        have h_dep_lt_hb : (YjsOperation.insert dep) < (YjsOperation.insert op) := by
          simpa [h_hb_eq'] using h_dep_lt_net
        have h_dep_mem_l1' : YjsOperation.insert dep ∈ l1' := by
          exact hbClosed_predecessor_in_prefix
            (hb := hb) (l := l1) (l' := l1') (l'' := l1'')
            (dep := YjsOperation.insert dep) (target := YjsOperation.insert op)
            h_closed1 h_split1 h_dep_lt_hb
        have h_dep_mem_l2' : YjsOperation.insert dep ∈ l2' := by
          exact hbClosed_predecessor_in_prefix
            (hb := hb) (l := l2) (l' := l2') (l'' := l2'')
            (dep := YjsOperation.insert dep) (target := YjsOperation.insert op)
            h_closed2 h_split2 h_dep_lt_hb
        obtain ⟨ b1pre, b1post, sb1, h_split_b1, h_eff_b1pre ⟩ :=
          split_preOps_at_insert
            (preOps := l1') (op := dep) (state := s1) h_eff1 h_dep_mem_l1'
        obtain ⟨ b2pre, b2post, sb2, h_split_b2, h_eff_b2pre ⟩ :=
          split_preOps_at_insert
            (preOps := l2') (op := dep) (state := s2) h_eff2 h_dep_mem_l2'
        have h_toItem_b1 : dep.toItem sb1.items = Except.ok i1 := by
          exact split_prefix_toItem_originItem
            (preOps := l1') (state₀ := s1)
            (oid := did0) (originItem := i1)
            (op := dep) (ops0 := b1pre) (ops1 := b1post) (s0 := sb1)
            h_eff1 h_nodup_l1' h_find1 h_dep_id' h_split_b1 h_eff_b1pre
        have h_toItem_b2 : dep.toItem sb2.items = Except.ok i2 := by
          exact split_prefix_toItem_originItem
            (preOps := l2') (state₀ := s2)
            (oid := did0) (originItem := i2)
            (op := dep) (ops0 := b2pre) (ops1 := b2post) (s0 := sb2)
            h_eff2 h_nodup_l2' h_find2 h_dep_id' h_split_b2 h_eff_b2pre
        have h_dep_mem_hist_j :
            Event.Deliver (YjsOperation.insert dep) ∈ network.histories j := by
          rw [h_hist_src']
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl h_dep_mem_preHist')))
        obtain ⟨ jDep, h_dep_broadcast_mem ⟩ :=
          network.toCausalNetwork.deliver_has_a_cause h_dep_mem_hist_j
        rw [List.mem_iff_append] at h_dep_broadcast_mem
        obtain ⟨ preDep, postDep, h_dep_hist ⟩ := h_dep_broadcast_mem
        have h_dep_hist' :
            network.histories jDep =
              preDep ++ [Event.Broadcast (YjsOperation.insert dep)] ++ postDep := by
          simpa [List.singleton_append, List.append_assoc] using h_dep_hist
        have h_dep_valid_at_src :
            ∃ sDep,
              interpHistory preDep Operation.init = Except.ok sDep ∧
              ValidMessage.isValidMessage sDep (YjsOperation.insert dep) := by
          have h_dep_hist_for_valid :
              preDep ++ [Event.Broadcast (YjsOperation.insert dep)] ++ postDep =
                network.histories jDep := by
            simpa using h_dep_hist'.symm
          simpa using
            (network.broadcast_only_valid_messages jDep (pre := preDep) (post := postDep)
              (e := YjsOperation.insert dep) h_dep_hist_for_valid)
        obtain ⟨ sDep, h_interp_dep, h_valid_dep ⟩ := h_dep_valid_at_src
        obtain ⟨ depItemSrc, h_toItem_dep_src, _h_depItem_valid ⟩ :
            ∃ it, dep.toItem sDep.items = Except.ok it ∧ it.isValid := by
          simpa [ValidMessage.isValidMessage, IsValidMessage] using h_valid_dep
        have h_dep_from_source :
            (match dep.originId with
              | none => True
              | some oid => exists o, Event.Deliver (YjsOperation.insert o) ∈ preDep /\ o.id = oid) /\
            (match dep.rightOriginId with
              | none => True
              | some rid => exists r, Event.Deliver (YjsOperation.insert r) ∈ preDep /\ r.id = rid) := by
          exact dep_ids_exist_in_source_prefix
            (network := network) (op := dep) (j := jDep)
            (preHist := preDep) (postHist := postDep) (s := sDep) (item := depItemSrc)
            h_dep_hist' h_interp_dep h_toItem_dep_src
        have h_dep_mem_pre0_of_lt :
            ∀ {pred : IntegrateInput A},
              (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
                (YjsOperation.insert pred) (YjsOperation.insert dep) ->
              Event.Deliver (YjsOperation.insert pred) ∈ pre0 := by
          intro pred h_pred_lt_dep
          have h_local_pred_dep :
              locallyOrdered network.toNodeHistories j
                (Event.Deliver (YjsOperation.insert pred))
                (Event.Deliver (YjsOperation.insert dep)) := by
            exact network.toCausalNetwork.causal_delivery h_dep_mem_hist_j h_pred_lt_dep
          obtain ⟨ lp, lm, ls, h_loc_eq ⟩ := h_local_pred_dep
          have h_hist_j_dep :
              network.histories j =
                pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++
                  (post0 ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist) := by
            calc
              network.histories j
                  = preHist ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist := h_hist_src'
              _ = (pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0) ++
                    [Event.Broadcast (YjsOperation.insert op)] ++ postHist := by
                    simpa [h_split_src]
              _ = pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++
                    (post0 ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist) := by
                    simp [List.append_assoc]
          have h_nodup_loc :
              ((lp ++ [Event.Deliver (YjsOperation.insert pred)] ++ lm) ++
                [Event.Deliver (YjsOperation.insert dep)] ++ ls).Nodup := by
            have h_nodup_j := network.toNodeHistories.event_distinct j
            simpa [List.append_assoc, h_loc_eq] using h_nodup_j
          have h_eq_prefix :
              lp ++ [Event.Deliver (YjsOperation.insert pred)] ++ lm = pre0 := by
            apply nodup_prefix_unique (x := Event.Deliver (YjsOperation.insert dep)) h_nodup_loc
            calc
              ((lp ++ [Event.Deliver (YjsOperation.insert pred)] ++ lm) ++
                  [Event.Deliver (YjsOperation.insert dep)] ++ ls)
                  = network.histories j := by
                    simpa [List.append_assoc] using h_loc_eq.symm
              _ = pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++
                    (post0 ++ [Event.Broadcast (YjsOperation.insert op)] ++ postHist) := h_hist_j_dep
          have h_mem_prefix :
              Event.Deliver (YjsOperation.insert pred) ∈
                lp ++ [Event.Deliver (YjsOperation.insert pred)] ++ lm := by
            simp
          simpa [h_eq_prefix] using h_mem_prefix
        have h_dep_from_pre0 :
            (match dep.originId with
              | none => True
              | some oid => exists o, Event.Deliver (YjsOperation.insert o) ∈ pre0 /\ o.id = oid) /\
            (match dep.rightOriginId with
              | none => True
              | some rid => exists r, Event.Deliver (YjsOperation.insert r) ∈ pre0 /\ r.id = rid) := by
          constructor
          · cases h_dep_originId : dep.originId with
            | none =>
              simp [h_dep_originId]
            | some oid =>
              have h_dep_source_left :
                  ∃ o, Event.Deliver (YjsOperation.insert o) ∈ preDep ∧ o.id = oid := by
                simpa [h_dep_originId] using h_dep_from_source.1
              obtain ⟨ o, h_mem_preDep, h_o_id ⟩ := h_dep_source_left
              have h_o_lt_dep :
                  (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
                    (YjsOperation.insert o) (YjsOperation.insert dep) := by
                exact dep_insert_lt_target
                  (network := network) (j := jDep) (preHist := preDep) (postHist := postDep)
                  (dep := o) (target := dep) h_dep_hist' h_mem_preDep
              have h_o_mem_pre0 : Event.Deliver (YjsOperation.insert o) ∈ pre0 := by
                exact h_dep_mem_pre0_of_lt h_o_lt_dep
              exact ⟨ o, h_o_mem_pre0, h_o_id ⟩
          · cases h_dep_rightOriginId : dep.rightOriginId with
            | none =>
              simp [h_dep_rightOriginId]
            | some rid =>
              have h_dep_source_right :
                  ∃ r, Event.Deliver (YjsOperation.insert r) ∈ preDep ∧ r.id = rid := by
                simpa [h_dep_rightOriginId] using h_dep_from_source.2
              obtain ⟨ r, h_mem_preDep, h_r_id ⟩ := h_dep_source_right
              have h_r_lt_dep :
                  (instCausalNetworkElemCausalOrder network.toCausalNetwork).lt
                    (YjsOperation.insert r) (YjsOperation.insert dep) := by
                exact dep_insert_lt_target
                  (network := network) (j := jDep) (preHist := preDep) (postHist := postDep)
                  (dep := r) (target := dep) h_dep_hist' h_mem_preDep
              have h_r_mem_pre0 : Event.Deliver (YjsOperation.insert r) ∈ pre0 := by
                exact h_dep_mem_pre0_of_lt h_r_lt_dep
              exact ⟨ r, h_r_mem_pre0, h_r_id ⟩
        cases n with
        | zero =>
          have h_pre0_nil : pre0 = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa [h_len]
          cases h_pre0_nil
          have h_dep_origin_none : dep.originId = none := by
            cases h_originId : dep.originId with
            | none =>
              rfl
            | some oid =>
              exfalso
              have h_dep_origin_pre0 :
                  ∃ o, Event.Deliver (YjsOperation.insert o) ∈ ([] : List (Event (YjsOperation A))) ∧
                    o.id = oid := by
                simpa [h_originId] using h_dep_from_pre0.1
              obtain ⟨ o, h_mem_nil, _h_o_id ⟩ := h_dep_origin_pre0
              simpa using h_mem_nil
          have h_dep_right_none : dep.rightOriginId = none := by
            cases h_rightId : dep.rightOriginId with
            | none =>
              rfl
            | some rid =>
              exfalso
              have h_dep_right_pre0 :
                  ∃ r, Event.Deliver (YjsOperation.insert r) ∈ ([] : List (Event (YjsOperation A))) ∧
                    r.id = rid := by
                simpa [h_rightId] using h_dep_from_pre0.2
              obtain ⟨ r, h_mem_nil, _h_r_id ⟩ := h_dep_right_pre0
              simpa using h_mem_nil
          have h_eq_ok :
              (Except.ok i1 : Except IntegrateError (YjsItem A)) = Except.ok i2 := by
            calc
              (Except.ok i1 : Except IntegrateError (YjsItem A)) = dep.toItem sb1.items := by
                simpa using h_toItem_b1.symm
              _ = (pure (YjsItem.mk YjsPtr.first YjsPtr.last dep.id dep.content) :
                    Except IntegrateError (YjsItem A)) := by
                simp [IntegrateInput.toItem, h_dep_origin_none, h_dep_right_none, bind, Except.bind]
              _ = dep.toItem sb2.items := by
                simp [IntegrateInput.toItem, h_dep_origin_none, h_dep_right_none, bind, Except.bind]
              _ = Except.ok i2 := h_toItem_b2
          cases h_eq_ok
          rfl
        | succ n' =>
          have h_nodup_b1pre : IdNoDup b1pre := by
            have h_b1pre_sub : b1pre.Sublist l1' := by
              rw [h_split_b1]
              simpa [List.append_assoc] using
                (List.sublist_append_left b1pre ([YjsOperation.insert dep] ++ b1post))
            exact List.Pairwise.sublist h_b1pre_sub h_nodup_l1'
          have h_nodup_b2pre : IdNoDup b2pre := by
            have h_b2pre_sub : b2pre.Sublist l2' := by
              rw [h_split_b2]
              simpa [List.append_assoc] using
                (List.sublist_append_left b2pre ([YjsOperation.insert dep] ++ b2post))
            exact List.Pairwise.sublist h_b2pre_sub h_nodup_l2'
          have h_unique_sb1 : uniqueId sb1.toList := by
            exact effect_list_uniqueId_from_IdNoDup
              (ops := b1pre) (s := sb1) h_nodup_b1pre h_eff_b1pre
          have h_unique_sb2 : uniqueId sb2.toList := by
            exact effect_list_uniqueId_from_IdNoDup
              (ops := b2pre) (s := sb2) h_nodup_b2pre h_eff_b2pre
          have h_unique_s1 : uniqueId s1.toList := by
            exact effect_list_uniqueId_from_IdNoDup
              (ops := l1') (s := s1) h_nodup_l1' h_eff1
          have h_unique_s2 : uniqueId s2.toList := by
            exact effect_list_uniqueId_from_IdNoDup
              (ops := l2') (s := s2) h_nodup_l2' h_eff2
          have h_tail_eff1 :
              effect_list (YjsOperation.insert dep :: b1post) sb1 = Except.ok s1 := by
            have h_eff1_split :
                effect_list (b1pre ++ [YjsOperation.insert dep] ++ b1post) Operation.init = Except.ok s1 := by
              simpa [h_split_b1] using h_eff1
            have h_bind1 :
                (do
                  let s' ← effect_list b1pre Operation.init
                  effect_list (YjsOperation.insert dep :: b1post) s') = Except.ok s1 := by
              simpa [effect_list_append] using h_eff1_split
            obtain ⟨ sMid, h_pre_mid, h_tail_mid ⟩ := Except.bind_eq_ok_exist h_bind1
            have h_sMid_eq : sMid = sb1 := by
              rw [h_eff_b1pre] at h_pre_mid
              cases h_pre_mid
              rfl
            simpa [h_sMid_eq] using h_tail_mid
          have h_tail_eff2 :
              effect_list (YjsOperation.insert dep :: b2post) sb2 = Except.ok s2 := by
            have h_eff2_split :
                effect_list (b2pre ++ [YjsOperation.insert dep] ++ b2post) Operation.init = Except.ok s2 := by
              simpa [h_split_b2] using h_eff2
            have h_bind2 :
                (do
                  let s' ← effect_list b2pre Operation.init
                  effect_list (YjsOperation.insert dep :: b2post) s') = Except.ok s2 := by
              simpa [effect_list_append] using h_eff2_split
            obtain ⟨ sMid, h_pre_mid, h_tail_mid ⟩ := Except.bind_eq_ok_exist h_bind2
            have h_sMid_eq : sMid = sb2 := by
              rw [h_eff_b2pre] at h_pre_mid
              cases h_pre_mid
              rfl
            simpa [h_sMid_eq] using h_tail_mid
          have h_eq_dep_from_pre0 :
              ∀ didX,
                (∃ depX, Event.Deliver (YjsOperation.insert depX) ∈ pre0 ∧ depX.id = didX) ->
                ∀ x1 x2,
                  sb1.find? (fun i => i.id = didX) = some x1 ->
                  sb2.find? (fun i => i.id = didX) = some x2 ->
                  x1 = x2 := by
            intro didX h_depX_in_pre0 x1 x2 h_find_x1_sb1 h_find_x2_sb2
            obtain ⟨ depX, h_depX_mem_pre0, h_depX_id ⟩ := h_depX_in_pre0
            obtain ⟨ preX, postX, h_pre0_split ⟩ := List.mem_iff_append.mp h_depX_mem_pre0
            have h_preX_lt_pre0 : preX.length < pre0.length := by
              rw [h_pre0_split]
              simp
            have h_preX_lt_n : preX.length < Nat.succ n' := by
              simpa [h_len] using h_preX_lt_pre0
            have h_split_depX :
                preHist =
                  preX ++ [Event.Deliver (YjsOperation.insert depX)] ++
                    (postX ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0) := by
              calc
                preHist = pre0 ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0 := h_split_src
                _ = (preX ++ [Event.Deliver (YjsOperation.insert depX)] ++ postX) ++
                      [Event.Deliver (YjsOperation.insert dep)] ++ post0 := by
                      simpa [h_pre0_split]
                _ = preX ++ [Event.Deliver (YjsOperation.insert depX)] ++
                      (postX ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0) := by
                      simp [List.append_assoc]
            have h_x1_id : x1.id = didX := by
              have h_find_x1_arr :
                  sb1.items.find? (fun i => i.id = didX) = some x1 := by
                simpa [YjsState.find?] using h_find_x1_sb1
              rw [Array.find?_eq_some_iff_getElem] at h_find_x1_arr
              simpa using h_find_x1_arr.1
            have h_x2_id : x2.id = didX := by
              have h_find_x2_arr :
                  sb2.items.find? (fun i => i.id = didX) = some x2 := by
                simpa [YjsState.find?] using h_find_x2_sb2
              rw [Array.find?_eq_some_iff_getElem] at h_find_x2_arr
              simpa using h_find_x2_arr.1
            have h_x1_mem_sb1 : x1 ∈ sb1.items := by
              simpa [YjsState.find?] using Array.mem_of_find?_eq_some h_find_x1_sb1
            have h_x2_mem_sb2 : x2 ∈ sb2.items := by
              simpa [YjsState.find?] using Array.mem_of_find?_eq_some h_find_x2_sb2
            have h_x1_mem_s1 : x1 ∈ s1.items := by
              exact effect_list_preserves_mem
                (ops := YjsOperation.insert dep :: b1post) (s0 := sb1) (s := s1) (item := x1)
                h_tail_eff1 h_x1_mem_sb1
            have h_x2_mem_s2 : x2 ∈ s2.items := by
              exact effect_list_preserves_mem
                (ops := YjsOperation.insert dep :: b2post) (s0 := sb2) (s := s2) (item := x2)
                h_tail_eff2 h_x2_mem_sb2
            have h_find_x1_s1 :
                s1.find? (fun i => i.id = didX) = some x1 := by
              apply exists_find?_eq_some_of_exists_mem_id
                (arr := s1.items) (targetId := didX) (item := x1)
              · simpa [YjsState.toList] using h_x1_mem_s1
              · exact h_x1_id
              · simpa [YjsState.toList] using h_unique_s1
            have h_find_x2_s2 :
                s2.find? (fun i => i.id = didX) = some x2 := by
              apply exists_find?_eq_some_of_exists_mem_id
                (arr := s2.items) (targetId := didX) (item := x2)
              · simpa [YjsState.toList] using h_x2_mem_s2
              · exact h_x2_id
              · simpa [YjsState.toList] using h_unique_s2
            exact ih preX.length h_preX_lt_n didX preX
              (postX ++ [Event.Deliver (YjsOperation.insert dep)] ++ post0) depX
              rfl h_split_depX h_depX_id x1 x2 h_find_x1_s1 h_find_x2_s2
          have h_toItem_b1_iff :=
            (IntegrateInput.toItem_ok_iff dep sb1.items i1 h_unique_sb1).1 h_toItem_b1
          have h_toItem_b2_iff :=
            (IntegrateInput.toItem_ok_iff dep sb2.items i2 h_unique_sb2).1 h_toItem_b2
          obtain ⟨ origin1, right1, id1, content1, h_item_def1, h_origin_ptr1,
            h_right_ptr1, h_id_eq1, h_content_eq1 ⟩ := h_toItem_b1_iff
          obtain ⟨ origin2, right2, id2, content2, h_item_def2, h_origin_ptr2,
            h_right_ptr2, h_id_eq2, h_content_eq2 ⟩ := h_toItem_b2_iff
          have h_origin_eq : origin1 = origin2 := by
            cases h_originId : dep.originId with
            | none =>
              simp [isLeftIdPtr, h_originId] at h_origin_ptr1 h_origin_ptr2
              simpa [h_origin_ptr1, h_origin_ptr2]
            | some oid =>
              simp [isLeftIdPtr, h_originId] at h_origin_ptr1 h_origin_ptr2
              obtain ⟨ io1, h_origin1_eq, h_find_io1 ⟩ := h_origin_ptr1
              obtain ⟨ io2, h_origin2_eq, h_find_io2 ⟩ := h_origin_ptr2
              have h_dep_origin_pre0 :
                  ∃ o, Event.Deliver (YjsOperation.insert o) ∈ pre0 ∧ o.id = oid := by
                simpa [h_originId] using h_dep_from_pre0.1
              have h_io_eq : io1 = io2 := by
                exact h_eq_dep_from_pre0 oid h_dep_origin_pre0 io1 io2
                  (by simpa [YjsState.find?] using h_find_io1)
                  (by simpa [YjsState.find?] using h_find_io2)
              simpa [h_origin1_eq, h_origin2_eq, h_io_eq]
          have h_right_eq : right1 = right2 := by
            cases h_rightId : dep.rightOriginId with
            | none =>
              simp [isRightIdPtr, h_rightId] at h_right_ptr1 h_right_ptr2
              simpa [h_right_ptr1, h_right_ptr2]
            | some rid =>
              simp [isRightIdPtr, h_rightId] at h_right_ptr1 h_right_ptr2
              obtain ⟨ ir1, h_right1_eq, h_find_ir1 ⟩ := h_right_ptr1
              obtain ⟨ ir2, h_right2_eq, h_find_ir2 ⟩ := h_right_ptr2
              have h_dep_right_pre0 :
                  ∃ r, Event.Deliver (YjsOperation.insert r) ∈ pre0 ∧ r.id = rid := by
                simpa [h_rightId] using h_dep_from_pre0.2
              have h_ir_eq : ir1 = ir2 := by
                exact h_eq_dep_from_pre0 rid h_dep_right_pre0 ir1 ir2
                  (by simpa [YjsState.find?] using h_find_ir1)
                  (by simpa [YjsState.find?] using h_find_ir2)
              simpa [h_right1_eq, h_right2_eq, h_ir_eq]
          have h_id12 : id1 = id2 := by
            calc
              id1 = dep.id := h_id_eq1
              _ = id2 := h_id_eq2.symm
          have h_content12 : content1 = content2 := by
            calc
              content1 = dep.content := h_content_eq1
              _ = content2 := h_content_eq2.symm
          calc
            i1 = YjsItem.mk origin1 right1 id1 content1 := h_item_def1
            _ = YjsItem.mk origin2 right2 id2 content2 := by
              simp [h_origin_eq, h_right_eq, h_id12, h_content12]
            _ = i2 := h_item_def2.symm
      exact h_dep_eq_by_len pre0.length did pre0 post0 dep rfl
        (by simpa [List.singleton_append, List.append_assoc] using h_dep_split)
        h_dep_id i1 i2 h_find1 h_find2
  have h_dep_eq :
    (match op.originId with
      | none => True
      | some oid =>
        forall io1 io2,
          s1.find? (fun i => i.id = oid) = some io1 ->
          s2.find? (fun i => i.id = oid) = some io2 ->
          io1 = io2) := by
    exact h_dep_eq_core op.originId h_dep_from_source.1
  have h_dep_eq_right :
    (match op.rightOriginId with
      | none => True
      | some rid =>
        forall ir1 ir2,
          s1.find? (fun i => i.id = rid) = some ir1 ->
          s2.find? (fun i => i.id = rid) = some ir2 ->
          ir1 = ir2) := by
    exact h_dep_eq_core op.rightOriginId h_dep_from_source.2
  -- Step 3.5(c): close with `toItem_ok_iff`
  have h_toItem2 : op.toItem s2.items = Except.ok item := by
    have h_unique_s1 : uniqueId s1.toList := by
      exact effect_list_uniqueId_from_IdNoDup (ops := l1') (s := s1) h_nodup_l1' h_eff1
    have h_unique_s2 : uniqueId s2.toList := by
      exact effect_list_uniqueId_from_IdNoDup (ops := l2') (s := s2) h_nodup_l2' h_eff2
    have h_toItem_s1_iff :=
      (IntegrateInput.toItem_ok_iff op s1.items item h_unique_s1).1 h_toItem
    obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin_ptr_s1,
      h_right_ptr_s1, h_id_eq, h_content_eq ⟩ := h_toItem_s1_iff
    rw [IntegrateInput.toItem_ok_iff op s2.items item h_unique_s2]
    refine ⟨ origin, rightOrigin, id, content, h_item_def, ?_, ?_, h_id_eq, h_content_eq ⟩
    · cases h_originId : op.originId with
      | none =>
        simp [isLeftIdPtr, h_originId] at h_origin_ptr_s1 ⊢
        simpa [h_origin_ptr_s1]
      | some oid =>
        simp [isLeftIdPtr, h_originId] at h_origin_ptr_s1 ⊢
        obtain ⟨ io1, h_origin_eq, h_find1 ⟩ := h_origin_ptr_s1
        have h_dep_left'_some : ∃ io2, s2.find? (fun i => i.id = oid) = some io2 := by
          simpa [h_originId] using h_dep_left'
        obtain ⟨ io2, h_find2 ⟩ := h_dep_left'_some
        have h_dep_eq_some :
            forall io1 io2,
              s1.find? (fun i => i.id = oid) = some io1 ->
              s2.find? (fun i => i.id = oid) = some io2 ->
              io1 = io2 := by
          simpa [h_originId] using h_dep_eq
        have h_io_eq : io1 = io2 := h_dep_eq_some io1 io2 h_find1 h_find2
        refine ⟨ io2, ?_, ?_ ⟩
        · simpa [h_origin_eq, h_io_eq]
        · simpa [YjsState.find?] using h_find2
    · cases h_rightOriginId : op.rightOriginId with
      | none =>
        simp [isRightIdPtr, h_rightOriginId] at h_right_ptr_s1 ⊢
        simpa [h_right_ptr_s1]
      | some rid =>
        simp [isRightIdPtr, h_rightOriginId] at h_right_ptr_s1 ⊢
        obtain ⟨ ir1, h_right_eq, h_find1 ⟩ := h_right_ptr_s1
        have h_dep_right'_some : ∃ ir2, s2.find? (fun i => i.id = rid) = some ir2 := by
          simpa [h_rightOriginId] using h_dep_right'
        obtain ⟨ ir2, h_find2 ⟩ := h_dep_right'_some
        have h_dep_eq_right_some :
            forall ir1 ir2,
              s1.find? (fun i => i.id = rid) = some ir1 ->
              s2.find? (fun i => i.id = rid) = some ir2 ->
              ir1 = ir2 := by
          simpa [h_rightOriginId] using h_dep_eq_right
        have h_ir_eq : ir1 = ir2 := h_dep_eq_right_some ir1 ir2 h_find1 h_find2
        refine ⟨ ir2, ?_, ?_ ⟩
        · simpa [h_right_eq, h_ir_eq]
        · simpa [YjsState.find?] using h_find2
  exact h_toItem2

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

theorem split_l_at_insert {A : Type} [DecidableEq A]
  {l : List (YjsOperation A)} {op : IntegrateInput A} {s : YjsState A} :
  effect_list l Operation.init = Except.ok s ->
  YjsOperation.insert op ∈ l ->
  exists l0 l1 sl,
    l = l0 ++ [YjsOperation.insert op] ++ l1 /\
    effect_list l0 Operation.init = Except.ok sl := by
  intro h_eff h_mem
  exact split_preOps_at_insert (preOps := l) (op := op) (state := s) h_eff h_mem

theorem transport_to_l_prefix {A : Type} [DecidableEq A]
  {hb : CausalOrder (YjsOperation A)} {network : YjsOperationNetwork A}
  {preOps l : List (YjsOperation A)}
  {op : IntegrateInput A}
  {ops0 ops1 l0 l1 : List (YjsOperation A)}
  {s0 sl s : YjsState A} {originItem : YjsItem A} :
  hb_consistent hb preOps ->
  hbClosed hb preOps ->
  IdNoDup preOps ->
  hb_consistent hb l ->
  hbClosed hb l ->
  IdNoDup l ->
  preOps = ops0 ++ [YjsOperation.insert op] ++ ops1 ->
  l = l0 ++ [YjsOperation.insert op] ++ l1 ->
  effect_list ops0 Operation.init = Except.ok s0 ->
  effect_list l0 Operation.init = Except.ok sl ->
  hb = instCausalNetworkElemCausalOrder network.toCausalNetwork ->
  (exists j, Event.Broadcast (YjsOperation.insert op) ∈ network.histories j) ->
  op.toItem s0.items = Except.ok originItem ->
  op.toItem sl.items = Except.ok originItem := by
  intro h_preOps_consistent h_preOps_closed h_preOps_nodup
    h_l_consistent h_l_closed h_l_nodup
    h_preOps_split h_l_split h_ops0_eff h_l0_eff h_hb_eq h_source h_toItem_s0
  exact toItem_prefix_invariant
    (hb := hb) (network := network)
    (op := op) (item := originItem)
    (l1 := preOps) (l2 := l)
    (l1' := ops0) (l1'' := ops1)
    (l2' := l0) (l2'' := l1)
    (s1 := s0) (s2 := sl)
    h_preOps_consistent h_l_consistent
    h_preOps_closed h_l_closed
    h_preOps_nodup h_l_nodup
    h_preOps_split h_l_split
    h_ops0_eff h_l0_eff h_hb_eq
    h_source h_toItem_s0

theorem insert_step_contains_id {A : Type} [DecidableEq A]
  {op : IntegrateInput A} {sl s' : YjsState A} {originItem : YjsItem A} :
  op.toItem sl.items = Except.ok originItem ->
  Operation.effect (YjsOperation.insert op) sl = Except.ok s' ->
  exists item', item' ∈ s'.items /\ item'.id = originItem.id := by
  intro h_toItem h_eff
  simp [Operation.effect] at h_eff
  obtain ⟨ _i, insertedItem, h_inserted_id, h_inserted_toItem, h_inserted_mem, _h_state_eq ⟩ :=
    integrateValid_exists_insertIdxIfBounds (init := sl) (input := op) (state' := s') h_eff
  have h_origin_id : originItem.id = op.id :=
    IntegrateInput.toItem_id_eq op sl.items originItem h_toItem
  have h_inserted_eq : insertedItem = originItem := by
    have h_eq_ok :
        (Except.ok insertedItem : Except IntegrateError (YjsItem A)) =
        (Except.ok originItem : Except IntegrateError (YjsItem A)) := by
      calc
        (Except.ok insertedItem : Except IntegrateError (YjsItem A)) = op.toItem sl.items := by
          simpa using h_inserted_toItem.symm
        _ = Except.ok originItem := h_toItem
    cases h_eq_ok
    rfl
  refine ⟨ originItem, ?_, ?_ ⟩
  · simpa [h_inserted_eq] using h_inserted_mem
  · simpa [h_origin_id]

theorem suffix_preserves_id {A : Type} [DecidableEq A]
  {suffix : List (YjsOperation A)} {s0 s : YjsState A} {oid : YjsId} :
  effect_list suffix s0 = Except.ok s ->
  (exists item0, item0 ∈ s0.items /\ item0.id = oid) ->
  exists item, item ∈ s.items /\ item.id = oid := by
  intro h_eff h_exists
  exact effect_list_preserves_id_exists (ops := suffix) (s0 := s0) (s := s) (targetId := oid) h_eff h_exists

theorem find_exact_from_unique {A : Type} [DecidableEq A]
  {arr : Array (YjsItem A)} {oid : YjsId} {originItem item : YjsItem A} :
  uniqueId arr.toList ->
  arr.find? (fun i => i.id = oid) = some originItem ->
  arr.find? (fun i => i.id = oid) = some item ->
  item = originItem := by
  intro _h_unique h_find_origin h_find_item
  rw [h_find_origin] at h_find_item
  cases h_find_item
  rfl

theorem pre_deliver_insert_find_preserved {A : Type} [DecidableEq A]
  {hb : CausalOrder (YjsOperation A)}
  {network : YjsOperationNetwork A}
  {pre : List (Event (YjsOperation A))}
  {preOps l : List (YjsOperation A)} {state₀ : YjsState A} {s : YjsState A} :
  preOps = deliverOps pre →
  effect_list preOps Operation.init = Except.ok state₀ →
  effect_list l Operation.init = Except.ok s →
  (∀ x, Event.Deliver (YjsOperation.insert x) ∈ pre → YjsOperation.insert x ∈ l) →
  hb_consistent hb preOps →
  hbClosed hb preOps →
  IdNoDup preOps →
  hb_consistent hb l →
  hbClosed hb l →
  IdNoDup l →
  hb = instCausalNetworkElemCausalOrder network.toCausalNetwork →
  (∀ op, YjsOperation.insert op ∈ preOps →
    ∃ j, Event.Broadcast (YjsOperation.insert op) ∈ network.histories j) →
  (∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
    s.find? (fun i => i.id = oid) = some originItem) := by
  intro h_preOps_eq h_preOps_eff h_l_eff h_pre_deliver_in_l
    h_preOps_consistent h_preOps_closed h_preOps_nodup
    h_l_consistent h_l_closed h_l_nodup h_hb_eq h_source
    oid originItem h_find_origin
  obtain ⟨ op, h_op_mem_preOps, h_op_id ⟩ :=
    find_implies_insert_mem_preOps
      (preOps := preOps) (state₀ := state₀) (oid := oid) (originItem := originItem)
      h_preOps_eff h_find_origin
  obtain ⟨ ops0, ops1, s0, h_preOps_split, h_ops0_eff ⟩ :=
    split_preOps_at_insert
      (preOps := preOps) (op := op) (state := state₀)
      h_preOps_eff h_op_mem_preOps
  have h_op_toItem_s0 : op.toItem s0.items = Except.ok originItem := by
    exact split_prefix_toItem_originItem
      (preOps := preOps) (state₀ := state₀)
      (oid := oid) (originItem := originItem)
      (op := op) (ops0 := ops0) (ops1 := ops1) (s0 := s0)
      h_preOps_eff h_preOps_nodup h_find_origin h_op_id h_preOps_split h_ops0_eff
  have h_op_mem_deliverOps : YjsOperation.insert op ∈ deliverOps pre := by
    simpa [h_preOps_eq] using h_op_mem_preOps
  have h_deliver_mem_pre : Event.Deliver (YjsOperation.insert op) ∈ pre := by
    unfold deliverOps at h_op_mem_deliverOps
    rcases List.mem_filterMap.1 h_op_mem_deliverOps with ⟨ ev, h_ev_mem, h_ev_map ⟩
    cases ev with
    | Broadcast e =>
      simp [eventDeliver] at h_ev_map
    | Deliver e =>
      simp [eventDeliver] at h_ev_map
      cases h_ev_map
      simpa using h_ev_mem
  have h_op_mem_l : YjsOperation.insert op ∈ l := by
    exact insert_mem_l_from_pre_deliver
      (pre := pre) (l := l) (op := op)
      h_pre_deliver_in_l h_deliver_mem_pre
  obtain ⟨ l0, l1, sl, h_l_split, h_l0_eff ⟩ :=
    split_l_at_insert
      (l := l) (op := op) (s := s)
      h_l_eff h_op_mem_l
  obtain ⟨ j, h_op_source ⟩ := h_source op h_op_mem_preOps
  have h_op_toItem_sl : op.toItem sl.items = Except.ok originItem := by
    exact transport_to_l_prefix
      (hb := hb) (network := network)
      (preOps := preOps) (l := l)
      (op := op)
      (ops0 := ops0) (ops1 := ops1) (l0 := l0) (l1 := l1)
      (s0 := s0) (sl := sl) (s := s) (originItem := originItem)
      h_preOps_consistent h_preOps_closed h_preOps_nodup
      h_l_consistent h_l_closed h_l_nodup
      h_preOps_split h_l_split
      h_ops0_eff h_l0_eff h_hb_eq
      ⟨ j, h_op_source ⟩
      h_op_toItem_s0
  have h_l_eff_split : effect_list (l0 ++ [YjsOperation.insert op] ++ l1) Operation.init = Except.ok s := by
    simpa [h_l_split] using h_l_eff
  have h_l_bind :
      (do
        let s' ← effect_list l0 Operation.init
        effect_list (YjsOperation.insert op :: l1) s') = Except.ok s := by
    simpa [effect_list_append] using h_l_eff_split
  obtain ⟨ sl', h_l0_eff', h_tail_eff ⟩ := Except.bind_eq_ok_exist h_l_bind
  have h_sl_eq : sl' = sl := by
    rw [h_l0_eff] at h_l0_eff'
    cases h_l0_eff'
    rfl
  have h_tail_eff' : effect_list (YjsOperation.insert op :: l1) sl = Except.ok s := by
    simpa [h_sl_eq] using h_tail_eff
  have h_tail_bind :
      (do
        let s' ← Operation.effect (YjsOperation.insert op) sl
        effect_list l1 s') = Except.ok s := by
    simpa [effect_list] using h_tail_eff'
  obtain ⟨ sAfterInsert, h_insert_eff, h_suffix_eff ⟩ := Except.bind_eq_ok_exist h_tail_bind
  have h_exists_after_insert :
      ∃ item', item' ∈ sAfterInsert.items ∧ item'.id = originItem.id := by
    exact insert_step_contains_id
      (op := op) (sl := sl) (s' := sAfterInsert) (originItem := originItem)
      h_op_toItem_sl h_insert_eff
  have h_origin_id : originItem.id = oid := by
    have h_origin_id_op : originItem.id = op.id :=
      IntegrateInput.toItem_id_eq op s0.items originItem h_op_toItem_s0
    simpa [h_op_id] using h_origin_id_op
  have h_exists_final_oid : ∃ item', item' ∈ s.items ∧ item'.id = oid := by
    have h_exists_final_origin :
        ∃ item', item' ∈ s.items ∧ item'.id = originItem.id := by
      exact suffix_preserves_id
        (suffix := l1) (s0 := sAfterInsert) (s := s) (oid := originItem.id)
        h_suffix_eff h_exists_after_insert
    rcases h_exists_final_origin with ⟨ item', h_mem, h_id ⟩
    exact ⟨ item', h_mem, by simpa [h_origin_id] using h_id ⟩
  have h_origin_mem_after_insert : originItem ∈ sAfterInsert.items := by
    simp [Operation.effect] at h_insert_eff
    obtain ⟨ _i, insertedItem, _h_inserted_id, h_inserted_toItem, h_inserted_mem, _h_state_eq ⟩ :=
      integrateValid_exists_insertIdxIfBounds
        (init := sl) (input := op) (state' := sAfterInsert) h_insert_eff
    have h_inserted_eq : insertedItem = originItem := by
      have h_eq_ok :
          (Except.ok insertedItem : Except IntegrateError (YjsItem A)) =
          (Except.ok originItem : Except IntegrateError (YjsItem A)) := by
        calc
          (Except.ok insertedItem : Except IntegrateError (YjsItem A)) = op.toItem sl.items := by
            simpa using h_inserted_toItem.symm
          _ = Except.ok originItem := h_op_toItem_sl
      cases h_eq_ok
      rfl
    simpa [h_inserted_eq] using h_inserted_mem
  have h_origin_mem_final : originItem ∈ s.items := by
    exact effect_list_preserves_mem
      (ops := l1) (s0 := sAfterInsert) (s := s) (item := originItem)
      h_suffix_eff h_origin_mem_after_insert
  have h_unique_s : uniqueId s.toList := by
    exact effect_list_uniqueId_from_IdNoDup (ops := l) (s := s) h_l_nodup h_l_eff
  have h_find_origin_s : s.find? (fun i => i.id = oid) = some originItem := by
    apply exists_find?_eq_some_of_exists_mem_id (arr := s.items) (targetId := oid) (item := originItem)
    · simpa [YjsState.toList] using h_origin_mem_final
    · exact h_origin_id
    · simpa [YjsState.toList] using h_unique_s
  rcases h_exists_final_oid with ⟨ item', h_item'_mem, h_item'_id ⟩
  have h_find_item' : s.find? (fun i => i.id = oid) = some item' := by
    apply exists_find?_eq_some_of_exists_mem_id (arr := s.items) (targetId := oid) (item := item')
    · simpa [YjsState.toList] using h_item'_mem
    · exact h_item'_id
    · simpa [YjsState.toList] using h_unique_s
  have h_find_origin_arr : s.items.find? (fun i => i.id = oid) = some originItem := by
    simpa [YjsState.find?] using h_find_origin_s
  have h_find_item_arr : s.items.find? (fun i => i.id = oid) = some item' := by
    simpa [YjsState.find?] using h_find_item'
  have _h_item_eq : item' = originItem := by
    exact find_exact_from_unique
      (arr := s.items) (oid := oid) (originItem := originItem) (item := item')
      (by simpa [YjsState.toList] using h_unique_s)
      h_find_origin_arr h_find_item_arr
  exact h_find_origin_s

theorem toItem_isValid_transport_min_bridge {A : Type} [DecidableEq A]
  (input : IntegrateInput A) (state₀ s : Array (YjsItem A)) (item₀ : YjsItem A) :
  input.toItem state₀ = Except.ok item₀ →
  item₀.isValid →
  uniqueId s.toList →
  (∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
    s.find? (fun i => i.id = oid) = some originItem) →
  ∃ item, input.toItem s = Except.ok item ∧ item.isValid := by
  intro h_toItem₀ h_item_valid₀ h_unique_s h_origin_find_in_s
  refine ⟨ item₀, ?_, h_item_valid₀ ⟩
  cases h_originId : input.originId with
  | none =>
    cases h_rightOriginId : input.rightOriginId with
    | none =>
      simpa [IntegrateInput.toItem, h_originId, h_rightOriginId] using h_toItem₀
    | some rid =>
      simp [IntegrateInput.toItem, h_originId, h_rightOriginId] at h_toItem₀ ⊢
      cases h_find₀ : state₀.find? (fun item => item.id = rid) with
      | none =>
        simp [h_find₀] at h_toItem₀
        cases h_toItem₀
      | some rightItem =>
        simp [h_find₀] at h_toItem₀
        have h_find_s : s.find? (fun i => i.id = rid) = some rightItem :=
          h_origin_find_in_s rid rightItem h_find₀
        simpa [h_find₀, h_find_s] using h_toItem₀
  | some oid =>
    cases h_rightOriginId : input.rightOriginId with
    | none =>
      simp [IntegrateInput.toItem, h_originId, h_rightOriginId] at h_toItem₀ ⊢
      cases h_find₀ : state₀.find? (fun item => item.id = oid) with
      | none =>
        simp [h_find₀] at h_toItem₀
        cases h_toItem₀
      | some originItem =>
        have h_find_s : s.find? (fun i => i.id = oid) = some originItem :=
          h_origin_find_in_s oid originItem h_find₀
        simpa [h_find₀, h_find_s] using h_toItem₀
    | some rid =>
      simp [IntegrateInput.toItem, h_originId, h_rightOriginId] at h_toItem₀ ⊢
      cases h_find₀o : state₀.find? (fun item => item.id = oid) with
      | none =>
        simp [h_find₀o] at h_toItem₀
        cases h_toItem₀
      | some originItem =>
        have h_find_so : s.find? (fun i => i.id = oid) = some originItem :=
          h_origin_find_in_s oid originItem h_find₀o
        cases h_find₀r : state₀.find? (fun item => item.id = rid) with
        | none =>
          simp [h_find₀o, h_find₀r] at h_toItem₀
          cases h_toItem₀
        | some rightItem =>
          have h_find_sr : s.find? (fun i => i.id = rid) = some rightItem :=
            h_origin_find_in_s rid rightItem h_find₀r
          simp [h_find₀o, h_find₀r] at h_toItem₀
          simpa [h_find_so, h_find_sr] using h_toItem₀

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
  let hb : CausalOrder (YjsOperation A) := instCausalNetworkElemCausalOrder network.toCausalNetwork
  let preOps : List (YjsOperation A) := deliverOps pre
  have h_preOps_eq : preOps = deliverOps pre := rfl
  have h_preOps_effect : effect_list preOps Operation.init = Except.ok state₀ := by
    simpa [preOps] using
      (interpHistory_eq_effect_deliverOps (A := A) (pre := pre) (state := state₀) h_state₀)
  have h_toDeliver_split :
      network.toCausalNetwork.toDeliverMessages srcClient = preOps ++ deliverOps post := by
    unfold CausalNetwork.toDeliverMessages preOps deliverOps
    rw [h_hist_eq, List.filterMap_append]
    simp
    rfl
  have h_preOps_sublist :
      preOps.Sublist (network.toCausalNetwork.toDeliverMessages srcClient) := by
    rw [h_toDeliver_split]
    exact List.sublist_append_left preOps (deliverOps post)
  have h_preOps_consistent : hb_consistent hb preOps := by
    have h_cons_src : hb_consistent hb (network.toCausalNetwork.toDeliverMessages srcClient) := by
      simpa [hb] using
        (hb_consistent_local_history (network := network.toCausalNetwork) (i := srcClient))
    exact hb_consistent_sublist (hb := hb) h_cons_src h_preOps_sublist
  have h_preOps_closed : hbClosed hb preOps := by
    have h_closed_src : hbClosed hb (network.toCausalNetwork.toDeliverMessages srcClient) := by
      simpa [hb] using toDeliverMessages_hbClosed (network := network) (i := srcClient)
    have h_closed_split : hbClosed hb (preOps ++ deliverOps post) := by
      simpa [h_toDeliver_split] using h_closed_src
    exact hbClosed_prefix (hb := hb) (ops₀ := preOps) (ops₁ := deliverOps post) h_closed_split
  have h_preOps_nodup : IdNoDup preOps := by
    have h_nodup_src : IdNoDup (network.toCausalNetwork.toDeliverMessages srcClient) := by
      exact toDeliverMessages_IdNoDup (network := network) (i := srcClient)
    exact List.Pairwise.sublist h_preOps_sublist h_nodup_src
  have h_preOps_source :
      ∀ op, YjsOperation.insert op ∈ preOps →
        ∃ j, Event.Broadcast (YjsOperation.insert op) ∈ network.histories j := by
    intro op h_mem_preOps
    have h_mem_deliver : Event.Deliver (YjsOperation.insert op) ∈ pre := by
      unfold preOps at h_mem_preOps
      rcases List.mem_filterMap.1 h_mem_preOps with ⟨ ev, h_ev_mem, h_ev_map ⟩
      cases ev with
      | Broadcast e =>
        simp [eventDeliver] at h_ev_map
      | Deliver e =>
        simp [eventDeliver] at h_ev_map
        cases h_ev_map
        simpa using h_ev_mem
    have h_mem_deliver_hist : Event.Deliver (YjsOperation.insert op) ∈ network.histories srcClient := by
      rw [h_hist_eq]
      exact List.mem_append_left _ h_mem_deliver
    exact network.toCausalNetwork.deliver_has_a_cause h_mem_deliver_hist
  let sArr : Array (YjsItem A) := s.items
  have h_unique_s : uniqueId sArr.toList := by
    simpa [sArr] using effect_list_uniqueId_from_IdNoDup (ops := l) (s := s) h_nodup h_effect
  have h_origin_find_in_s :
      ∀ oid originItem, state₀.find? (fun i => i.id = oid) = some originItem →
        sArr.find? (fun i => i.id = oid) = some originItem := by
    intro oid originItem h_find
    have h_find_s : s.find? (fun i => i.id = oid) = some originItem := by
      exact pre_deliver_insert_find_preserved
        (hb := hb) (network := network) (pre := pre) (preOps := preOps) (l := l)
        (state₀ := state₀) (s := s)
        h_preOps_eq h_preOps_effect h_effect h_pre_deliver_in_l
        h_preOps_consistent h_preOps_closed h_preOps_nodup
        (by simpa [hb] using h_consistent) (by simpa [hb] using h_closed) h_nodup
        (by rfl)
        h_preOps_source oid originItem h_find
    simpa [sArr] using h_find_s
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
