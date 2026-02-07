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

def YjsEmptyArray {A} : Array (YjsItem A) := #[]

def integrateValid {A} [DecidableEq A] (input : IntegrateInput A) (state : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) :=
  integrateSafe input state

theorem integrateValid_eq_integrateSafe {A} [DecidableEq A] (item : IntegrateInput A) (state : Array (YjsItem A)) :
  integrateValid item state = integrateSafe item state := by
  rfl

def deleteValid {A} [DecidableEq A] (id : YjsId) (state : Array (YjsItem A)) : Array (YjsItem A) :=
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

instance [DecidableEq A] : Operation (YjsOperation A) where
  State := Array (YjsItem A)
  Error := IntegrateError
  init := YjsEmptyArray
  effect item state := match item with
  | YjsOperation.insert item => integrateValid item state
  | YjsOperation.delete _id deletedId =>
    Except.ok <| deleteValid deletedId state
  isValidState op state := IsValidMessage state op
  StateInv state := YjsArrInvariant state.toList
  stateInv_init := by
    change YjsArrInvariant ([] : List (YjsItem A))
    exact YjsArrayInvariant_empty
  stateInv_effect := by
    intro op s s' h_inv h_valid h_effect
    cases op with
    | insert input =>
      simp [integrateValid, IsValidMessage] at h_effect h_valid
      obtain ⟨ item, hitem, hitem_valid ⟩ := h_valid
      have ⟨ _, _, _, h_inv' ⟩ :=
        YjsArrInvariant_integrateSafe input item s s' h_inv hitem hitem_valid h_effect
      exact h_inv'
    | delete _ deletedId =>
      have hs' : s' = deleteById s deletedId := by
        simpa [deleteValid] using h_effect.symm
      subst hs'
      exact YjsArrInvariant_deleteById s deletedId h_inv

instance [DecidableEq A] : ValidMessage (YjsOperation A) where
  isValidMessage state item := IsValidMessage state item

def YjsOperation.UniqueId {A} (op : YjsOperation A) (state : Array (YjsItem A)) : Prop :=
    ∀x ∈ state, x.id.clientId = op.id.clientId → x.id.clock < op.id.clock

structure YjsOperationNetwork A [DecidableEq A] extends OperationNetwork (YjsOperation A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.id.clientId = i
  histories_UniqueId : forall {e i} {array : Array (YjsItem A)}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 Operation.init = Except.ok array → YjsOperation.UniqueId e array

theorem Subtype_eq_of_val {α : Type} {P : α → Prop} {x y : { a : α // P a }} : x.val = y.val → x = y := by
  intros h
  cases x; cases y
  simp at h
  congr

theorem integrateValid_bind_integrateSafe {A} [DecidableEq A] (state : Array (YjsItem A)) (a b : IntegrateInput A) :
  (do let arr ← integrateValid a state; integrateValid b arr) =
  (do let arr ← integrateSafe a state; integrateSafe b arr) := by
  rfl

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
  {init : Array (YjsItem A)} {input : IntegrateInput A} {item : YjsItem A}
  {state' : Array (YjsItem A)} :
  (h_init_inv : YjsArrInvariant init.toList) →
  (h_effect : integrateValid input init = Except.ok state') →
  (hitem : input.toItem init = Except.ok item) →
  ∃ i, state' = init.insertIdxIfInBounds i item := by
  intro h_init_inv h_effect hitem
  have hvalid : item.isValid := by
    sorry

  have ⟨ i, _, h_eq, _ ⟩ :=
    YjsArrInvariant_integrateSafe input item init state' h_init_inv hitem hvalid
      (by simpa [integrateValid] using h_effect)
  use i

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
            simp [Operation.effect, integrateValid] at h_effect
            have ⟨ item, hitem ⟩ : ∃item, input.toItem init = Except.ok item := by
              sorry
            have h_init_inv : YjsArrInvariant init.toList := by
              sorry
            have ⟨ _, h_insert ⟩ : ∃i, state' = init.insertIdxIfInBounds i item := by
              apply integrateValid_exists_insertIdxIfBounds h_init_inv h_effect hitem
            rw [h_insert] at h_init_mem
            simp [Array.insertIdxIfInBounds] at h_init_mem
            split at h_init_mem
            . simp [ArrSet] at h_init_mem
              obtain ⟨ y, h_y_mem, h_y_id ⟩ := h_init_mem
              rw [List.mem_insertIdx (by assumption)] at h_y_mem
              cases h_y_mem with
              | inl h_mem =>
                right
                use input
                constructor
                sorry
                sorry
                -- grind only
                -- simp
              | inr h_eq =>
                left; use y; constructor; simp [ArrSet] at *; assumption
                assumption
            . left; assumption
          | inr h_in_state =>
            obtain ⟨ y, h_y_val, h_y_mem ⟩ := h_in_state
            right; use y
            simp; constructor; assumption
            right; assumption

def IsStateAt {A M} [DecidableEq A] [Operation A] [DecidableEq M] [Message A M] [ValidMessage A] {network : OperationNetwork A} (a : A) (arr : Operation.State A) : Prop :=
  ∃i hist1 hist2, network.histories i = hist1 ++ [Event.Broadcast a] ++ hist2 ∧
    interpHistory hist1 Operation.init = Except.ok arr ∧
    ValidMessage.isValidMessage arr a

theorem OriginReachable_HappensBefore {A : Type} [DecidableEq A]
  {network : YjsOperationNetwork A} {i : ClientId} {a b : YjsOperation A} {inputA inputB : IntegrateInput A} {itemA itemB : YjsItem A} {state_a state_b : Array (YjsItem A)}:
  IsStateAt (network := network.toOperationNetwork) a state_a →
  IsStateAt (network := network.toOperationNetwork) b state_b →
  a = YjsOperation.insert inputA →
  b = YjsOperation.insert inputB →
  inputA.toItem state_a = Except.ok itemA →
  inputB.toItem state_b = Except.ok itemB →
  OriginReachable (YjsPtr.itemPtr itemA) (YjsPtr.itemPtr itemB) →
  (instCausalNetworkElemCausalOrder network.toCausalNetwork).le b a := by
  intros hstateAtA hstateAtB h_item_a h_item_b htoItemA htoItemB h_reachable

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
      sorry
    | reachable_right o r id c =>
      simp at h_a_ptr_def
      sorry

  have h_b_in_state_a : ArrSet (state_a.toList) itemB := by
    cases h_reachable with
    | reachable_single _ _ h_step =>
      apply h_OriginReachableStep_ArrSet _ h_step
    | reachable_head _ y _ h_step h_reach_tail =>
      apply h_OriginReachableStep_ArrSet at h_step
      have h_closed : IsClosedItemSet (ArrSet state_a.toList) := by
        sorry
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
    have h_b_id_eq : Message.messageId (YjsOperation.insert item_b') = Message.messageId (YjsOperation.insert inputB) := by
      sorry
    have h_item_b'_in_ja : Event.Deliver (YjsOperation.insert item_b') ∈ network.histories j_a := by
      rw [h_a_history, h_b_in_items_history]; simp
    apply network.deliver_has_a_cause at h_item_b'_in_ja
    obtain ⟨ j_b', h_item_b'_in_ja_history ⟩ := h_item_b'_in_ja
    apply network.msg_id_unique (i := j_b') (j := j_b) at h_b_id_eq
    . obtain ⟨ _, h_eq ⟩ := h_b_id_eq
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

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b sa sb h_a_mem h_b_mem h_a_b_happens_before havalid hbvalid hab
  sorry
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

instance [DecidableEq A] {network : YjsOperationNetwork A} : MonotoneOperation (YjsOperation A) (hb := instCausalNetworkElemCausalOrder network.toCausalNetwork) YjsId where
  isValidState_mono := by sorry

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

  have h_concurrent_commutative : concurrent_commutative (hb := hb) (network.toCausalNetwork.toDeliverMessages i) := by
    apply YjsOperationNetwork_concurrentCommutative network i

  have h := hb_consistent_effect_convergent (s := res₀) (hb := hb)
    (network.toCausalNetwork.toDeliverMessages i)
    (network.toCausalNetwork.toDeliverMessages j)
    h_consistent_i
    h_consistent_j
    (by sorry)
    (by sorry)
    h_concurrent_commutative
    (by sorry)
    (by sorry)
    h_hist_mem
    h_res₀

  have h_res_ok_eq : Except.ok (ε := IntegrateError) res₀ = Except.ok res₁ := by
    rw [<-h_res₀, <-h_res₁]
    simp [interpOps] at *
    rw [h, h_res₀]

  cases h_res_ok_eq
  simp
end YjsNetwork
