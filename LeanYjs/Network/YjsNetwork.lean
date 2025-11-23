import LeanYjs.Item
import LeanYjs.Algorithm.Integrate
import LeanYjs.Algorithm.IntegrateProof
import LeanYjs.Network.CausalNetwork
import LeanYjs.Network.CausalOrder

section YjsNetwork

open NetworkModels

abbrev YjsValidItem A := { item : YjsItem A // item.isValid }

abbrev YjsArray A := { array : Array (YjsItem A) // YjsArrInvariant array.toList }

def integrateValid {A} [DecidableEq A] (item : YjsValidItem A) (state : YjsArray A) : Except IntegrateError (YjsArray A) := by
  let integrated := integrate item.val state.val
  obtain ⟨ state, h_state ⟩ := state
  obtain ⟨ item, h_item ⟩ := item
  cases h_eq : integrated with
  | error e => exact Except.error e
  | ok arr =>
    have harrinv : YjsArrInvariant arr.toList := by
      have ⟨ _, _, _, h ⟩ := YjsArrInvariant_integrate item state arr h_state h_item _ (by subst integrated; apply h_eq)
      apply h
    exact Except.ok ⟨ arr, harrinv ⟩

instance : Message (YjsItem A) YjsId where
  messageId item := item.id

instance [DecidableEq A] : Operation (YjsItem A) where
  State := { s : Array (YjsItem A) // YjsArrInvariant s.toList }
  Error := IntegrateError
  effect item state := integrate item state

def interpOps {A} [DecidableEq A] (items : List (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) :=
  List.foldlM (init := #[]) (f := fun acc item => integrate item acc) items

def interpHistory {A} [DecidableEq A] (history : List (Event (YjsItem A))) : Except IntegrateError (Array (YjsItem A)) :=
  interpOps (history.filterMap (fun ev => match ev with | Event.Deliver it => some it | _ => none))

def interpDeliveredOps {A} [DecidableEq A] {network : CausalNetwork (YjsItem A)} (items : List (CausalNetworkElem (YjsItem A) network)) : Except IntegrateError (Array (YjsItem A)) :=
  let deliveredItems := items.map (fun item => item.elem)
  interpOps deliveredItems

structure YjsOperationNetwork A [DecidableEq A] extends CausalNetwork (YjsItem A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.id.clientId = i
  histories_InsertOk : forall {e i}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 = Except.ok array → InsertOk array e

theorem foldlM_foldr_effect_comp_eq {A} [DecidableEq A] {network : CausalNetwork (YjsItem A)} (items : List (CausalNetworkElem (YjsItem A) network)) (init : Array (YjsItem A)) :
  List.foldlM (fun acc item => integrate item acc) init (List.map (fun item => item.elem) items) =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) init := by
  induction items generalizing init with
  | nil =>
    simp
    eq_refl
  | cons item items ih =>
    simp [effect_comp, bind, Except.bind, Operation.effect]
    generalize h_init' : integrate item.elem init = init' at *
    cases init' with
    | error err =>
      simp
    | ok state' =>
      simp
      rw [ih]
      eq_refl

theorem interpDeliveredMessages_foldr_effect_comp_eq : forall {A} [DecidableEq A] {network : CausalNetwork (YjsItem A)} (items : List (CausalNetworkElem (YjsItem A) network)),
  interpDeliveredOps items =
  List.foldr effect_comp (fun s => Except.ok s) (items.map (fun a => Operation.effect a)) #[] := by
  intros A _ network items
  simp [interpDeliveredOps, interpOps]
  rw [foldlM_foldr_effect_comp_eq]

theorem YjsOperationNetwork_concurrentCommutative {A} [DecidableEq A] (network : YjsOperationNetwork A) (i : ClientId) :
  concurrent_commutative inferInstance (network.toCausalNetwork.toDeliverMessages i) := by
  intros a b h_a_mem h_b_mem h_a_b_happens_before
  funext s
  simp [Operation.State] at s
  simp [effect_comp, effect, Operation.effect]
  apply integrate_commutative
  generalize h_s_a : integrate a.elem s = s_a
  generalize h_s_b : integrate b.elem s = s_b
  sorry

theorem YjsOperationNetwork_converge' : forall {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : Array (YjsItem A)),
  let hist_i := network.toDeliverMessages i
  let hist_j := network.toDeliverMessages j
  interpDeliveredOps hist_i = Except.ok res₀ →
  interpDeliveredOps hist_j = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
  := by
  intros A _ network i j res₀ res₁ hist_i hist_j h_res₀ h_res₁ h_hist_mem

  subst hist_i hist_j

  let hb : CausalOrder (CausalNetworkElem (YjsItem A) network.toCausalNetwork) := inferInstance
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
