import LeanYjs.Item
import LeanYjs.Algorithm.Delete.Basic
import LeanYjs.Algorithm.Delete.Spec
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Commutativity.InsertInsert
import LeanYjs.Algorithm.Commutativity.InsertDelete
import LeanYjs.Algorithm.Commutativity.DeleteDelete
import LeanYjs.Network.CausalNetwork
import LeanYjs.Network.CausalOrder
import LeanYjs.Network.OperationNetwork

section YjsNetwork

open NetworkModels

abbrev YjsValidItem A := { item : YjsItem A // item.isValid }

def YjsValidItem.id {A} (item : YjsValidItem A) : YjsId :=
  item.val.id

inductive YjsOperation A where
| insert (item : YjsValidItem A) : YjsOperation A
| delete (id deletedId : YjsId) : YjsOperation A
deriving Repr, DecidableEq

def YjsOperation.id {A} (op : YjsOperation A) : YjsId :=
  match op with
  | YjsOperation.insert item => item.val.id
  | YjsOperation.delete id _ => id

abbrev YjsArray A := { array : Array (YjsItem A) // YjsArrInvariant array.toList }

theorem YjsArrayInvariant_empty {A} : YjsArrInvariant ([] : List (YjsItem A)) := by
  constructor
  . constructor <;> simp [ArrSet]
  . constructor <;> simp [ArrSet]
  . constructor
  . constructor

def YjsEmptyArray {A} : YjsArray A :=
  ⟨ #[], (by simp [YjsArrayInvariant_empty]) ⟩

def integrateValid {A} [DecidableEq A] (item : YjsValidItem A) (state : YjsArray A) : Except IntegrateError (YjsArray A) :=
  let integrated := integrateSafe item.val state.val
  match (motive := (arr : Except IntegrateError (Array (YjsItem A))) → arr = integrated → Except IntegrateError (YjsArray A)) integrated, rfl with
  | Except.error e, _ => Except.error e
  | Except.ok arr, h_eq =>
    let proof : YjsArrInvariant arr.toList := by
      have ⟨ _, _, _, h ⟩ := YjsArrInvariant_integrateSafe item state arr state.prop item.prop (by subst integrated; rw [h_eq])
      apply h
    Except.ok ⟨ arr, proof ⟩

theorem integrateValid_eq_integrateSafe {A} [DecidableEq A] (item : YjsValidItem A) (state : YjsArray A) :
  (fun v => ↑v) <$> (integrateValid item state) = integrateSafe item.val state.val := by
  cases h_eq : integrateSafe item.val state.val with
  | error err =>
    simp [integrateValid]
    -- rw [heq] at h_integrate_valid causes error at dependent type of rfl depending integrateSafe ..., so use conv mode.`
    conv =>
      lhs
      enter [2, 3]
      rw [h_eq]
      rfl
    simp
  | ok integrated =>
    simp [integrateValid]
    conv =>
      lhs
      enter [2, 3]
      rw [h_eq]
      rfl
    simp

def deleteValid {A} [DecidableEq A] (id : YjsId) (state : YjsArray A) : YjsArray A :=
  let newArr := deleteById state.val id
  ⟨ newArr, by subst newArr; apply YjsArrInvariant_deleteById; apply state.2 ⟩

instance : Message (YjsOperation A) YjsId where
  messageId item := match item with
  | YjsOperation.insert item => item.val.id
  | YjsOperation.delete id _ => id

instance [DecidableEq A] : Operation (YjsOperation A) where
  State := { s : Array (YjsItem A) // YjsArrInvariant s.toList }
  Error := IntegrateError
  init := YjsEmptyArray
  effect item state := match item with
  | YjsOperation.insert item => integrateValid item state
  | YjsOperation.delete _id deletedId =>
    Except.ok <| deleteValid deletedId state

def IsValidMessage (state : YjsArray A) (item : YjsOperation A) : Prop :=
  match item with
  | YjsOperation.insert item =>
    ArrSet state.val.toList item.val.origin ∧
    ArrSet state.val.toList item.val.rightOrigin
  | YjsOperation.delete _ _ =>
    True

instance [DecidableEq A] : ValidMessage (YjsOperation A) where
  isValidMessage state item := IsValidMessage state item

def YjsOperation.UniqueId {A} (op : YjsOperation A) (state : YjsArray A) : Prop :=
    ∀x ∈ state.val, x.id.clientId = op.id.clientId → x.id.clock < op.id.clock

structure YjsOperationNetwork A [DecidableEq A] extends OperationNetwork (YjsOperation A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.id.clientId = i
  histories_UniqueId : forall {e i} {array : YjsArray A}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 Operation.init = Except.ok array → YjsOperation.UniqueId e array

theorem foldlM_foldr_effect_comp_eq {A} [DecidableEq A] {network : CausalNetwork (YjsOperation A)} (items : List (CausalNetworkElem (YjsOperation A) network)) (init : YjsArray A) :
  List.foldlM (fun acc item => Operation.effect item acc) init (List.map (fun item => item.elem) items) =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) init := by
  induction items generalizing init with
  | nil =>
    simp
    eq_refl
  | cons item items ih =>
    simp [effect_comp, bind, Except.bind]
    generalize h_init' : Operation.effect item.elem init = init' at *
    cases init' with
    | error err =>
      simp
    | ok state' =>
      simp
      rw [ih]

theorem interpDeliveredMessages_foldr_effect_comp_eq : forall {A} [DecidableEq A] {network : CausalNetwork (YjsOperation A)} (items : List (CausalNetworkElem (YjsOperation A) network)),
  interpDeliveredOps items Operation.init =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) YjsEmptyArray := by
  intros A _ network items
  simp [interpDeliveredOps, interpOps]
  rw [<-foldlM_foldr_effect_comp_eq]
  eq_refl

theorem Subtype_eq_of_val {α : Type} {P : α → Prop} {x y : { a : α // P a }} : x.val = y.val → x = y := by
  intros h
  cases x; cases y
  simp at h
  congr

theorem integrateValid_bind_integrateSafe {A} [DecidableEq A] (state : YjsArray A) (a b : YjsValidItem A) :
  (fun (x : YjsArray A) => x.val) <$> (do let arr ← integrateValid a state; integrateValid b arr) =
  (do let arr ← integrateSafe ↑a ↑state; integrateSafe ↑b arr) := by
  rw [map_bind]
  conv =>
    lhs
    enter [2]
    intro x
    rw [integrateValid_eq_integrateSafe]
    rfl
  have h_eq := bind_map_left (f := fun (x : YjsArray A) => x.val) (g := fun arr => integrateSafe ↑b arr)
  rw [<-h_eq, integrateValid_eq_integrateSafe]

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
  ¬hb_concurrent inferInstance (CausalNetworkElem.mk (network := network) a) (CausalNetworkElem.mk (network := network) b) := by
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
  {init : YjsArray A} {item : YjsValidItem A}
  {state' : YjsArray A} :
  (h_effect : integrateValid item init = Except.ok state') →
  ∃ i, state'.val = init.val.insertIdxIfInBounds i ↑item := by
  intro h_effect
  simp [integrateValid] at h_effect
  have h_init_inv : YjsArrInvariant init.val.toList := init.prop
  have h_eq : integrateSafe ↑item init.val = Except.ok state'.val := by
    generalize h_effect' : integrateSafe ↑item init.val = res
    cases res with
    | error err =>
      conv at h_effect =>
        lhs
        enter [3]
        rw [h_effect']
        rfl
      simp at h_effect
    | ok arr =>
      conv at h_effect =>
        lhs
        enter [3]
        rw [h_effect']
        rfl
      simp at h_effect
      subst state'
      simp

  have ⟨ i, _, h_eq, _ ⟩ := YjsArrInvariant_integrateSafe item.val init.val state'.val init.prop item.prop h_eq
  use i

theorem interpOps_ArrSet {A} [DecidableEq A] {items : List (Event (YjsOperation A))} {state init : Operation.State (YjsOperation A)} {x : YjsItem A}:
  interpHistory items init = Except.ok state →
  ArrSet state.val.toList x →
  (∃y, ArrSet init.val.toList (YjsPtr.itemPtr y) ∧ y.id = x.id) ∨
  (∃y, y.val.id = x.id ∧ Event.Deliver (YjsOperation.insert y) ∈ items) := by
  intros h_interp h_in_state
  induction items generalizing init state x with
  | nil =>
    simp [interpHistory, interpOps, pure] at h_interp
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
        simp [Operation.effect] at h_interp
        apply ih (x := x) h_interp at h_in_state
        cases h_in_state with
        | inl h =>
          obtain ⟨ y, h_mem, h_y_id ⟩ := h
          simp [ArrSet, deleteValid, deleteById] at h_mem
          obtain ⟨ a, h_a_mem, h_a_eq ⟩ := h_mem
          left; use a; constructor; simp [ArrSet]; assumption
          rw [<-h_y_id, <-h_a_eq, deleteItemById_id]
        | inr h =>
          obtain ⟨ y, h_y_val, h_y_mem ⟩ := h
          right; use y
          simp; constructor; assumption
          assumption
      | insert item =>
        simp at h_interp
        generalize h_effect : Operation.effect (YjsOperation.insert item) init = state' at *
        cases state' with
        | error err =>
          cases h_interp
        | ok state' =>
          rw [ok_bind] at h_interp
          apply ih h_interp at h_in_state
          cases h_in_state with
          | inl h_init_mem =>
            simp [Operation.effect] at h_effect
            have ⟨ _, h_insert ⟩ : ∃i, state'.val = init.val.insertIdxIfInBounds i item := by
              apply integrateValid_exists_insertIdxIfBounds h_effect
            rw [h_insert] at h_init_mem
            simp [Array.insertIdxIfInBounds] at h_init_mem
            split at h_init_mem
            . simp [ArrSet] at h_init_mem
              obtain ⟨ y, h_y_mem, h_y_id ⟩ := h_init_mem
              rw [List.mem_insertIdx (by assumption)] at h_y_mem
              cases h_y_mem with
              | inl h_mem =>
                right
                use item
                constructor
                grind only
                simp
              | inr h_eq =>
                left; use y; constructor; simp [ArrSet] at *; assumption
                assumption
            . left; assumption
          | inr h_in_state =>
            obtain ⟨ y, h_y_val, h_y_mem ⟩ := h_in_state
            right; use y
            simp; constructor; assumption
            right; assumption

theorem OriginReachable_HappensBefore {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {i : ClientId} {a b : CausalNetworkElem (YjsOperation A) network.toCausalNetwork} {item_a item_b : YjsValidItem A} :
  a ∈ network.toDeliverMessages i →
  b ∈ network.toDeliverMessages i →
  a.elem = YjsOperation.insert item_a →
  b.elem = YjsOperation.insert item_b →
  OriginReachable (YjsPtr.itemPtr item_a.val) (YjsPtr.itemPtr item_b.val) →
  b ≤ a := by
  intros h_a_mem h_b_mem h_item_a h_item_b h_reachable

  simp [CausalNetwork.toDeliverMessages] at h_b_mem h_a_mem
  replace ⟨ a, h_a_mem, h_a_eq ⟩ := h_a_mem
  have ⟨ a', h_a_eq ⟩ : ∃ a', Event.Deliver a' = a := by
    cases a with
    | Deliver it =>
      use it
    | Broadcast e =>
      simp at h_a_eq
  subst h_a_eq
  replace ⟨ b, h_b_mem, h_b_eq ⟩ := h_b_mem
  have ⟨ b', h_b_eq ⟩ : ∃ b', Event.Deliver b' = b := by
    cases b with
    | Deliver it =>
      use it
    | Broadcast e =>
      simp at h_b_eq
  subst h_b_eq
  have ⟨ j_a, h_a_mem_history_j_a ⟩ := network.deliver_has_a_cause h_a_mem
  have ⟨ j_b, h_b_mem_history_j_b  ⟩ := network.deliver_has_a_cause h_b_mem

  rw [List.mem_iff_append] at h_a_mem_history_j_a h_b_mem_history_j_b

  obtain ⟨ pre_a, post_a, h_a_history ⟩ := h_a_mem_history_j_a
  obtain ⟨ pre_b, post_b, h_b_history ⟩ := h_b_mem_history_j_b

  have ⟨ state_a, h_state_a, h_valid_message_a ⟩ : ∃state, interpHistory pre_a Operation.init = Except.ok state ∧ ValidMessage.isValidMessage state a' := by
    apply network.broadcast_only_valid_messages (pre := pre_a) (post := post_a) j_a
    rw [h_a_history]; simp

  have ⟨ state_b, h_state_b, h_valid_message_b ⟩ : ∃state, interpHistory pre_b Operation.init = Except.ok state ∧ ValidMessage.isValidMessage state b' := by
    apply network.broadcast_only_valid_messages (pre := pre_b) (post := post_b) j_b
    rw [h_b_history]; simp

  simp at h_a_eq h_b_eq
  subst h_a_eq h_b_eq

  simp at h_item_a h_item_b
  subst a' b'
  simp [ValidMessage.isValidMessage] at h_valid_message_a
  obtain ⟨ h_a_origin_in_state_a, h_a_rightOrigin_in_state_a ⟩ := h_valid_message_a

  generalize h_a_ptr_def : YjsPtr.itemPtr item_a.val = a_ptr at *

  have h_OriginReachableStep_ArrSet : ∀ x,
    OriginReachableStep a_ptr x → ArrSet state_a.val.toList x := by
    intros x h_step
    cases h_step with
    | reachable o r id c =>
      simp at h_a_ptr_def
      rw [h_a_ptr_def] at h_a_origin_in_state_a
      simp at h_a_origin_in_state_a
      assumption
    | reachable_right o r id c =>
      simp at h_a_ptr_def
      rw [h_a_ptr_def] at h_a_rightOrigin_in_state_a
      simp at h_a_rightOrigin_in_state_a
      assumption

  have h_b_in_state_a : ArrSet (state_a.val.toList) item_b.val := by
    cases h_reachable with
    | reachable_single _ _ h_step =>
      apply h_OriginReachableStep_ArrSet _ h_step
    | reachable_head _ y _ h_step h_reach_tail =>
      apply h_OriginReachableStep_ArrSet at h_step
      obtain ⟨ state_a_val, h_state_a_spec ⟩ := state_a
      simp at *
      have h_closed := h_state_a_spec.closed
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
    have h_b_id_eq : Message.messageId (YjsOperation.insert item_b') = Message.messageId (YjsOperation.insert item_b) := by
      assumption
    have h_item_b'_in_ja : Event.Deliver (YjsOperation.insert item_b') ∈ network.histories j_a := by
      rw [h_a_history, h_b_in_items_history]; simp
    apply network.deliver_has_a_cause at h_item_b'_in_ja
    obtain ⟨ j_b', h_item_b'_in_ja_history ⟩ := h_item_b'_in_ja
    apply network.msg_id_unique (i := j_b') (j := j_b) at h_b_id_eq
    . obtain ⟨ _, h_eq ⟩ := h_b_id_eq
      simp at h_eq
      subst item_b'
      rfl
    . assumption
    . rw [h_b_history]; simp

theorem hb_concurrent_diff_id {A : Type} [inst : DecidableEq A]
  (network : YjsOperationNetwork A) (i : ClientId)
  (a : CausalNetworkElem (YjsOperation A) network.toCausalNetwork)
  (h_a_mem : a ∈ network.toDeliverMessages i)
  (b : CausalNetworkElem (YjsOperation A) network.toCausalNetwork)
  (h_b_mem : b ∈ network.toDeliverMessages i)
  (h_a_b_happens_before : hb_concurrent inferInstance a b) :
  a.elem.id.clientId ≠ b.elem.id.clientId := by
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

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative inferInstance (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b h_a_mem h_b_mem h_a_b_happens_before
  funext s
  simp [Operation.State, Operation.Error] at *
  simp [effect_comp, effect]
  apply Except.map_eq_eq (f := fun (x : YjsArray A) => x.val)
  . intros x y h_eq
    apply Subtype_eq_of_val
    exact h_eq
  . obtain ⟨ a ⟩ := a
    obtain ⟨ b ⟩ := b
    cases a with
    | insert a =>
      cases b with
      | insert b =>
        conv =>
          lhs
          enter [2]
          simp [Operation.effect]
        rw [integrateValid_bind_integrateSafe]
        conv =>
          rhs
          enter [2]
          simp [Operation.effect]
        rw [integrateValid_bind_integrateSafe]
        apply integrate_commutative
        . obtain ⟨ s, h_s ⟩ := s
          simp; assumption
        . apply hb_concurrent_diff_id _ _
            (a := ⟨ YjsOperation.insert a ⟩) (b := ⟨YjsOperation.insert b ⟩) h_a_mem h_b_mem h_a_b_happens_before
        . intros h_reachable
          obtain ⟨ _, h_b_hb_a ⟩ := h_a_b_happens_before
          apply h_b_hb_a
          apply OriginReachable_HappensBefore h_a_mem h_b_mem rfl rfl h_reachable
        . intros h_reachable
          obtain ⟨ h_a_hb_b, _ ⟩ := h_a_b_happens_before
          apply h_a_hb_b
          apply OriginReachable_HappensBefore h_b_mem h_a_mem rfl rfl h_reachable
        . obtain ⟨ a, _ ⟩ := a
          assumption
        . obtain ⟨ b, _ ⟩ := b
          assumption
      | delete _ deletedId =>
        simp [Operation.State, Operation.Error, Operation.effect]
        simp [deleteValid]
        rw [<-bind_map_left (f := fun (x : YjsArray A) => x.val) (g := fun arr => Except.ok (deleteById arr deletedId)),
            integrateValid_eq_integrateSafe,
            integrateSafe_deleteById_commutative]
        simp [bind, Except.bind]
        rw [integrateValid_eq_integrateSafe]
    | delete _ deletedId =>
      cases b with
      | insert b =>
        simp [Operation.State, Operation.Error, Operation.effect]
        simp [deleteValid]
        rw [<-bind_map_left (f := fun (x : YjsArray A) => x.val) (g := fun arr => Except.ok (deleteById arr deletedId)),
            integrateValid_eq_integrateSafe,
            integrateSafe_deleteById_commutative]
        simp [bind, Except.bind]
        rw [integrateValid_eq_integrateSafe]
      | delete _ deletedId' =>
        simp [Operation.Error, Operation.effect, deleteValid, bind, Except.bind]
        apply deleteById_commutative

theorem YjsOperationNetwork_converge' : forall {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsArray A),
  let hist_i := network.toDeliverMessages i
  let hist_j := network.toDeliverMessages j
  interpDeliveredOps hist_i Operation.init = Except.ok res₀ →
  interpDeliveredOps hist_j Operation.init = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
  := by
  intros A _ network i j res₀ res₁ hist_i hist_j h_res₀ h_res₁ h_hist_mem

  subst hist_i hist_j

  let hb : CausalOrder (CausalNetworkElem (YjsOperation A) network.toCausalNetwork) := inferInstance
  have h_consistent_i : hb_consistent hb (network.toCausalNetwork.toDeliverMessages i) := by
    apply hb_consistent_local_history
  have h_consistent_j : hb_consistent hb (network.toCausalNetwork.toDeliverMessages j) := by
    apply hb_consistent_local_history

  have h_noDup_i : (network.toCausalNetwork.toDeliverMessages i).Nodup := by
    apply toDeliverMessages_Nodup

  have h_noDup_j : (network.toCausalNetwork.toDeliverMessages j).Nodup := by
    apply toDeliverMessages_Nodup

  have h_concurrent_commutative : concurrent_commutative hb (network.toCausalNetwork.toDeliverMessages i) := by
    apply YjsOperationNetwork_concurrentCommutative network i

  have h_effectt_eq :
    (List.map (fun a => Operation.effect a) (network.toCausalNetwork.toDeliverMessages i) |> List.foldr effect_comp (fun s => Except.ok s)) =
    (List.map (fun a => Operation.effect a) (network.toCausalNetwork.toDeliverMessages j) |> List.foldr effect_comp (fun s => Except.ok s)) := by
      apply hb_consistent_effect_convergent hb
        (network.toCausalNetwork.toDeliverMessages i)
        (network.toCausalNetwork.toDeliverMessages j)
        (fun s => Except.ok s)
        h_consistent_i
        h_consistent_j
        h_concurrent_commutative
        h_noDup_i
        h_noDup_j
        h_hist_mem

  rw [interpDeliveredMessages_foldr_effect_comp_eq] at h_res₀ h_res₁

  have h_res_ok_eq : Except.ok (ε := IntegrateError) res₀ = Except.ok res₁ := by
    rw [<-h_res₀, <-h_res₁]
    rw [h_effectt_eq]

  cases h_res_ok_eq
  simp
end YjsNetwork
