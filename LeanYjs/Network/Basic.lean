import Init.Data.List

import LeanYjs.ClientId
import LeanYjs.Item
import LeanYjs.IntegrateProof

namespace Network

class Message (A : Type) where
  messageId : A → String

inductive Event (A : Type) : Type where
  | Broadcast : A → Event A
  | Deliver : A → Event A
  deriving Inhabited, Repr, BEq, DecidableEq, Hashable

def Event.id {A} [Message A] : Event A → String
  | Event.Broadcast a => Message.messageId a
  | Event.Deliver a => Message.messageId a

structure NodeHistories (E : Type) where
  histories : ClientId → List E
  event_distinct : forall i, (histories i).Nodup

def locallyOrdered {E} [DecidableEq E] (histories : NodeHistories E) (i : ClientId) (e1 e2 : E) : Prop :=
  e1 ∈ histories.histories i ∧ e2 ∈ histories.histories i ∧
  (histories.histories i).idxOf? e1 < (histories.histories i).idxOf? e2

structure NetworkBase A [DecidableEq A] [Message A] extends NodeHistories (Event A) where
  deliver_has_a_cause : forall {i e}, Event.Deliver e ∈ histories i → ∃ j, Event.Broadcast e ∈ histories j
  deliver_locally : forall {i e}, Event.Deliver e ∈ histories i →
    locallyOrdered toNodeHistories i (Event.Broadcast e) (Event.Deliver e)
  msg_id_unique : forall {mi mj i j}, Event.Broadcast mi ∈ histories i → Event.Broadcast mj ∈ histories j → Message.messageId mi = Message.messageId mj → i = j ∧ mi = mj

inductive HappensBefore {A} [DecidableEq A] [Message A] (network : NetworkBase A) : A → A → Prop
  | broadcast_broadcast_local : locallyOrdered network.toNodeHistories i (Event.Broadcast e1) (Event.Broadcast e2) → HappensBefore network e1 e2
  | broadcast_deliver_local : locallyOrdered network.toNodeHistories i (Event.Broadcast e1) (Event.Deliver e2) → HappensBefore network e1 e2
  | trans : HappensBefore network e1 e2 → HappensBefore network e2 e3 → HappensBefore network e1 e3

structure CausalNetwork A [DecidableEq A] [Message A] extends NetworkBase A where
  causal_delivery : forall {i e1 e2}, Event.Deliver e2 ∈ histories i → HappensBefore toNetworkBase e1 e2 → locallyOrdered toNodeHistories i (Event.Deliver e1) (Event.Deliver e2)
  -- This assumption is not assumed in the paper, but it is necessary for the ensuring total order of Yjs items and for my proof.
  -- It is also a reasonable assumption because in a real Yjs implementation, a client would apply item same time at the time of creation of the item by library API (e.g., insert).
  histories_deliver_broadcast_ordered : forall (e1 e2 : A) i,
    locallyOrdered toNodeHistories i (Event.Broadcast e1) (Event.Broadcast e2) →
    locallyOrdered toNodeHistories i (Event.Deliver e1) (Event.Broadcast e2)

instance [Message A]: Message (YjsItem A) where
  messageId item := Message.messageId item.content

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

end Network
