import LeanYjs.Item
import LeanYjs.Algorithm.Integrate
import LeanYjs.Algorithm.IntegrateSpec
import LeanYjs.Algorithm.IntegrateCommutative
import LeanYjs.Network.CausalNetwork
import LeanYjs.Network.CausalOrder

section YjsNetwork

open NetworkModels

abbrev YjsValidItem A := { item : YjsItem A // item.isValid }

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
  (fun v => ↑v) <$> (integrateValid item state)  = integrateSafe item.val state.val := by
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

instance : Message (YjsValidItem A) YjsId where
  messageId item := item.val.id

instance [DecidableEq A] : Operation (YjsValidItem A) where
  State := { s : Array (YjsItem A) // YjsArrInvariant s.toList }
  Error := IntegrateError
  effect item state := integrateValid item state

def interpOps {A} [DecidableEq A] (items : List (YjsValidItem A)) : Except IntegrateError (YjsArray A) :=
  List.foldlM (init := YjsEmptyArray) (f := fun acc item => integrateValid item acc) items

def interpHistory {A} [DecidableEq A] (history : List (Event (YjsValidItem A))) : Except IntegrateError (YjsArray A) :=
  interpOps (history.filterMap (fun ev => match ev with | Event.Deliver it => some it | _ => none))

def interpDeliveredOps {A} [DecidableEq A] {network : CausalNetwork (YjsValidItem A)} (items : List (CausalNetworkElem (YjsValidItem A) network)) : Except IntegrateError (YjsArray A) :=
  let deliveredItems := items.map (fun item => item.elem)
  interpOps deliveredItems

structure YjsOperationNetwork A [DecidableEq A] extends CausalNetwork (YjsValidItem A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.val.id.clientId = i
  histories_InsertOk : forall {e i}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 = Except.ok array → UniqueId e.val array.val

theorem foldlM_foldr_effect_comp_eq {A} [DecidableEq A] {network : CausalNetwork (YjsValidItem A)} (items : List (CausalNetworkElem (YjsValidItem A) network)) (init : YjsArray A) :
  List.foldlM (fun acc item => integrateValid item acc) init (List.map (fun item => item.elem) items) =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) init := by
  induction items generalizing init with
  | nil =>
    simp
    eq_refl
  | cons item items ih =>
    simp [effect_comp, bind, Except.bind, Operation.effect]
    generalize h_init' : integrateValid item.elem init = init' at *
    cases init' with
    | error err =>
      simp
    | ok state' =>
      simp
      rw [ih]
      eq_refl

theorem interpDeliveredMessages_foldr_effect_comp_eq : forall {A} [DecidableEq A] {network : CausalNetwork (YjsValidItem A)} (items : List (CausalNetworkElem (YjsValidItem A) network)),
  interpDeliveredOps items =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) YjsEmptyArray := by
  intros A _ network items
  simp [interpDeliveredOps, interpOps]
  rw [foldlM_foldr_effect_comp_eq]

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

theorem same_history_not_hb_concurrent {A} [DecidableEq A] {network : CausalNetwork (YjsValidItem A)} {i : ClientId} {a b : YjsValidItem A} :
  Event.Broadcast a ∈ network.histories i →
  Event.Broadcast b ∈ network.histories i →
  ¬hb_concurrent inferInstance (CausalNetworkElem.mk (network := network) a) (CausalNetworkElem.mk (network := network) b) := by
  intros h_a_mem h_b_mem h_not_hb
  intro h_eq
  subst h_eq
  have h_a_hb_b : a ⪯ b ∨ b ⪯ a := by
    apply network.local_history_total_ordering i a b h_a_mem h_b_mem
  cases h_a_hb_b with
  | inl h_a_hb_b' =>
    contradiction
  | inr h_b_hb_a' =>
    contradiction

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative inferInstance (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b h_a_mem h_b_mem h_a_b_happens_before
  funext s
  simp [Operation.State, Operation.Error] at *
  simp [effect_comp, effect, Operation.effect]
  apply Except.map_eq_eq (f := fun (x : YjsArray A) => x.val)
  . intros x y h_eq
    apply Subtype_eq_of_val
    exact h_eq
  . rw [integrateValid_bind_integrateSafe]
    rw [integrateValid_bind_integrateSafe]
    apply integrate_commutative
    . obtain ⟨ s, h_s ⟩ := s
      simp; assumption
    . intros h_eq
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
        simp at *
        subst i_a i_b
        assumption

      subst i_a
      simp at *
      subst a b
      apply same_history_not_hb_concurrent h_a'_mem_hist h_b'_mem_hist h_a_b_happens_before
    . sorry
    . sorry
    . sorry
    . sorry

theorem YjsOperationNetwork_converge' : forall {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsArray A),
  let hist_i := network.toDeliverMessages i
  let hist_j := network.toDeliverMessages j
  interpDeliveredOps hist_i = Except.ok res₀ →
  interpDeliveredOps hist_j = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
  := by
  intros A _ network i j res₀ res₁ hist_i hist_j h_res₀ h_res₁ h_hist_mem

  subst hist_i hist_j

  let hb : CausalOrder (CausalNetworkElem (YjsValidItem A) network.toCausalNetwork) := inferInstance
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
