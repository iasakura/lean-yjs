import LeanYjs.Item
import LeanYjs.Integrate
import LeanYjs.IntegrateProof
import LeanYjs.Network.CausalNetwork
import LeanYjs.Network.CausalOrder

section YjsNetwork

open Network

instance [Message A]: Message (YjsItem A) where
  messageId item := Message.messageId item.content

instance [DecidableEq A] : Operation (YjsItem A) where
  State := Array (YjsItem A)
  Error := IntegrateError
  effect item state := integrate item state

def interpOps {A} [DecidableEq A] [Message A] (items : List (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) :=
  List.foldlM (init := #[]) (f := fun acc item => integrate item acc) items

def interpHistory {A} [DecidableEq A] [Message A] (history : List (Event (YjsItem A))) : Except IntegrateError (Array (YjsItem A)) :=
  interpOps (history.filterMap (fun ev => match ev with | Event.Deliver it => some it | _ => none))

structure YjsOperationNetwork A [DecidableEq A] [Message A] extends CausalNetwork (YjsItem A) where
  histories_client_id : forall {e i}, Event.Broadcast e ∈ histories i → e.id = i
  histories_InsertOk : forall {e i}, histories i = hist1 ++ [Event.Broadcast e] ++ hist2 →
    interpHistory hist1 = Except.ok array → InsertOk array e

theorem YjsOperationNetwork_converge : forall {A} [DecidableEq A] [Message A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : Array (YjsItem A)),
  let hist_i := network.toNodeHistories.histories i
  let hist_j := network.toNodeHistories.histories j
  interpHistory hist_i = Except.ok res₀ →
  interpHistory hist_j = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
  := by
  intros A _ _ network i j res₀ res₁ hist_i hist_j h_res₀ h_res₁ h_hist_mem

  subst hist_i
  subst hist_j

  generalize h_hist_i_eq : network.toNodeHistories.histories i = hist_i at *
  generalize h_hist_j_eq : network.toNodeHistories.histories j = hist_j at *

  generalize h_hist_i_len_eq : hist_i.length = len_hist_i at *

  revert i j network res₀ res₁ h_res₀ h_res₁ h_hist_mem h_hist_i_eq h_hist_j_eq h_hist_i_len_eq hist_i hist_j

  induction len_hist_i with
  | zero =>
    intros i j network res₀ res₁ hist_i h_hist_i_eq h_res₀ hist_j h_hist_j_eq h_res₁ h_hist_mem h_hist_i_len_eq
    rw [List.length_eq_zero_iff] at h_hist_i_len_eq
    subst h_hist_i_len_eq
    cases hist_j with
    | nil =>
      simp [interpHistory, interpOps] at h_res₀ h_res₁
      cases h_res₀
      cases h_res₁
      rfl
    | cons ev hist_j_tail =>
      simp at h_hist_mem
      obtain ⟨ h_mem, _ ⟩ := h_hist_mem ev
      contradiction
  | succ len_hist_i ih =>
    intros i j network res₀ res₁ hist_i h_hist_i_eq h_res₀ hist_j h_hist_j_eq h_res₁ h_hist_mem h_hist_i_len_eq
    have h_hist_i_pos : 0 < hist_i.length := by
      omega
    rw [List.length_pos_iff_exists_cons] at h_hist_i_pos
    replace ⟨ ev_i, hist_i, h_hist_i_eq' ⟩ := h_hist_i_pos
    subst h_hist_i_eq'
    cases hist_j with
    | nil =>
      simp at h_hist_mem
      obtain ⟨ h_mem, _ ⟩ := h_hist_mem ev_i
      contradiction
    | cons ev_j hist_j_tail =>
      sorry

end YjsNetwork
