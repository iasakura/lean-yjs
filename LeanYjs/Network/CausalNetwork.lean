import Init.Data
import Init.Data.List.Basic

import LeanYjs.ListLemmas
import LeanYjs.ClientId
import LeanYjs.Network.CausalOrder

namespace CausalNetwork

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
  ∃ l1 l2 l3, histories.histories i = l1 ++ [e1] ++ l2 ++ [e2] ++ l3

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

structure CausalNetworkElem A [DecidableEq A] [Message A] (network : CausalNetwork A) where
  elem : A

instance instCausalNetworkElemCausalOrder [DecidableEq A] [Message A] (network : CausalNetwork A) : CausalOrder (CausalNetworkElem A network) where
  lt a b := HappensBefore network.toNetworkBase a.elem b.elem
  le a b := a = b ∨ HappensBefore network.toNetworkBase a.elem b.elem
  le_refl := fun a => Or.inl rfl
  le_trans := fun a b c h_ab h_bc => by
    cases h_ab with
    | inl h_eq =>
      subst h_eq
      assumption
    | inr h_hb_ab =>
      cases h_bc with
      | inl h_eq =>
        subst h_eq
        right; assumption
      | inr h_hb_bc =>
        right
        apply HappensBefore.trans h_hb_ab h_hb_bc
  le_antisymm := fun a b h_ab h_ba => by
    suffices HappensBefore network.toNetworkBase a.elem b.elem → HappensBefore network.toNetworkBase b.elem a.elem → False by
      cases h_ab with
      | inl h_eq => assumption
      | inr h_hb_ab =>
        cases h_ba with
        | inl h_eq =>
          subst h_eq
          simp
        | inr h_hb_ba =>
          exfalso
          apply this h_hb_ab h_hb_ba
    intros h_ab h_ba
    -- suppose a < a
    -- if a < a only consists of broadcast_deliver_local, then we can conclude a.idx < a.idx, which is a contradiction
    -- otherwise, if a < a is break down into a < b and b < a and a < b is broadcast_deliver_local, we now have
    -- D(a) <_i B(b) and b < a.
    -- so by causal_delivery, we have D(b) <_i D(a), but it followed by D(b) <_i B(b), it contradicts with deliver_locally.
    sorry
  lt_iff_le_not_ge := by sorry

section OperationNetwork

variable [Operation A] [Message A] [DecidableEq A]
variable (network : CausalNetwork A)

instance [Operation A] : Operation (CausalNetworkElem A network) where
  State := Operation.State A
  Error := Operation.Error A
  effect (a : CausalNetworkElem A network) : Operation.State A → Except (Operation.Error A) (Operation.State A) :=
    Operation.effect a.elem

def CausalNetwork.toDeliverMessages (network : CausalNetwork A) (i : ClientId) : List (CausalNetworkElem A network) :=
  network.toNodeHistories.histories i |>.filterMap (fun ev => match ev with
    | Event.Deliver a => some (CausalNetworkElem.mk a)
    | _ => none)

-- don't need induction because it is sufficient to use filterMap_eq_..._iff lemma
omit [Operation A] in theorem toDeliverMessages_histories (i : ClientId) :
  network.toDeliverMessages i = l1 ++ [m] ++ l2 ++ [m'] ++ l3 →
  ∃ l1 l2 l3,
    network.toNodeHistories.histories i = l1 ++ [Event.Deliver m.elem] ++ l2 ++ [Event.Deliver m'.elem] ++ l3 := by
  intro h_deliver_msgs
  simp [CausalNetwork.toDeliverMessages] at h_deliver_msgs
  generalize network.toNodeHistories.histories i = history at *
  induction history generalizing l1 m l2 m' l3 with
  | nil =>
    simp at h_deliver_msgs
  | cons ev history ih =>
    cases ev with
    | Broadcast a =>
      simp [List.filterMap_cons_none] at h_deliver_msgs
      obtain ⟨ l1', m'', l2', m''', l3', h_eq ⟩ := ih h_deliver_msgs
      use (Event.Broadcast a :: l1'), m'', l2'
      simp
    | Deliver a =>
      simp at h_deliver_msgs
      cases l1 with
      | cons x l1 =>
        simp at h_deliver_msgs
        replace ⟨ _, h_deliver_msgs ⟩ := h_deliver_msgs
        obtain ⟨ l1', m'', l2', m''', l3', h_eq ⟩ := ih h_deliver_msgs
        use (Event.Deliver a :: l1'), m'', l2'
        simp
      | nil =>
        simp at h_deliver_msgs
        obtain ⟨ h_m_eq, h_deliver_msgs ⟩ := h_deliver_msgs
        use []
        simp
        rw [List.filterMap_eq_append_iff] at h_deliver_msgs
        obtain ⟨ l2', l3', h_eq', h_eq2', h_eq3' ⟩ := h_deliver_msgs
        rw [List.filterMap_eq_cons_iff] at h_eq3'
        obtain ⟨ l3', y, h_eq3', l3'', h_none, h_some, h_filterMap ⟩ := h_eq3'
        subst history l3''
        constructor
        . subst m; simp
        . use (l2' ++ l3'), h_eq3'
          simp
          cases y with
          | Broadcast a' =>
            simp at h_some
          | Deliver a' =>
            simp at h_some
            subst m'
            simp

theorem hb_consistent_local_history_aux i ms ms' :
  ms ++ ms' = network.toDeliverMessages i →
  hb_consistent (hb := instCausalNetworkElemCausalOrder network) ms' := by
  intros h_ms
  -- simp [CausalNetwork.toDeliverMessages] at h_ms
  induction ms' generalizing ms with
  | nil =>
    simp [hb_consistent.nil]
  | cons h t ih =>
    conv at h_ms =>
      lhs
      rw [List.append_cons]
      rfl
    apply hb_consistent.cons
    . apply ih (ms ++ [h]) h_ms
    . intros m h_mem h_le
      cases h_le with
      | inr h_lt =>
        have ⟨ t1, t2, h_t_eq ⟩ : ∃ t1 t2, t = t1 ++ [m] ++ t2 := by
          rw [List.mem_iff_append] at h_mem
          simp
          assumption
        subst h_t_eq
        replace h_ms : network.toDeliverMessages i =  ms ++ [h] ++ t1 ++ [m] ++ t2 := by
          rw [←h_ms]
          simp
        obtain ⟨ l1, l2, l3, h_history_eq ⟩ := toDeliverMessages_histories network i h_ms
        have h_locally_ordered : locallyOrdered network.toNodeHistories i (Event.Deliver h.elem) (Event.Deliver m.elem) := by
          simp [locallyOrdered]
          use l1, l2, l3
          rw [h_history_eq]
          simp
        apply network.causal_delivery (i := i) at h_lt
        . -- need locallyOrdered asym
          sorry
        . sorry
      | inl h_eq =>
        sorry

theorem hb_consistent_local_history i :
  hb_consistent (hb := instCausalNetworkElemCausalOrder network) (network.toDeliverMessages i) := by
  apply hb_consistent_local_history_aux network i []
  simp
end OperationNetwork

theorem toDeliverMessages_Nodup [DecidableEq A] [Message A] (network : CausalNetwork A) : (network.toDeliverMessages i).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intros idx1 idx2 h_idx1_lt_length h_idx2_lt_length h_idx1_lt_idx2 h_eq
  rw [List.getElem_eq_iff_getElem?_eq] at h_eq
  let f := fun ev =>
    match ev with
    | Event.Deliver a => some $ CausalNetworkElem.mk (network := network) a
    | x => none
  have h_eq_f : network.toDeliverMessages i = List.filterMap f (network.histories i) := by
    simp [CausalNetwork.toDeliverMessages]
    congr

  obtain ⟨ map, h_map_eq, h_map_inj ⟩ := List.filterMap_getElem_index f (network.histories i)

  rw [h_eq_f] at h_idx1_lt_length h_idx2_lt_length h_eq
  obtain ⟨ a, h_a_mem, h_a_eq ⟩ := h_map_eq idx1 h_idx1_lt_length
  obtain ⟨ b, h_b_mem, h_b_eq ⟩ := h_map_eq idx2 h_idx2_lt_length

  have h_f_a_eq_f_b : f a = f b := by
    rw [h_a_mem, h_b_mem] at h_eq
    assumption

  have h_a_eq_b : a = b := by
    cases a with
    | Deliver a =>
      cases b with
      | Deliver b =>
        simp [f] at h_f_a_eq_f_b
        simp; assumption
      | Broadcast b =>
        simp [f] at h_f_a_eq_f_b
    | Broadcast a =>
      simp [f] at *
      omega

  have h_pairwise : List.Pairwise (fun x y => x ≠ y) (network.histories i) := by
    rw [<-List.nodup_iff_pairwise_ne]
    apply network.event_distinct

  rw [List.pairwise_iff_getElem] at h_pairwise

  -- rw [List.mem_iff_getElem] at h_a_mem_i h_b_mem_j
  -- obtain ⟨ idx1', h_idx1'_lt_length, h_a_eq' ⟩ := h_a_mem_i
  -- obtain ⟨ idx2', h_idx2'_lt_length, h_b_eq' ⟩ := h_b_mem_j

  have h_map_idx1_lt_length : map idx1 < (network.histories i).length := by
    cases Nat.lt_or_ge (map idx1) (network.histories i).length with
    | inl h_lt => assumption
    | inr h_ge =>
      rw [List.getElem?_eq_none (by omega)] at h_a_eq
      cases h_a_eq

  have h_map_idx2_lt_length : map idx2 < (network.histories i).length := by
    cases Nat.lt_or_ge (map idx2) (network.histories i).length with
    | inl h_lt => assumption
    | inr h_ge =>
      rw [List.getElem?_eq_none (by omega)] at h_b_eq
      cases h_b_eq

  generalize h_idx1'_eq : map idx1 = idx1' at h_a_mem h_a_eq h_map_idx1_lt_length
  generalize h_idx2'_eq : map idx2 = idx2' at h_b_mem h_b_eq h_map_idx2_lt_length

  cases Nat.lt_or_ge idx1' idx2' with
  | inl h_idx1'_lt_idx2' =>
    obtain h_neq := h_pairwise idx1' idx2' h_map_idx1_lt_length h_map_idx2_lt_length h_idx1'_lt_idx2'
    apply h_neq
    rw [List.getElem_eq_iff_getElem?_eq]
    rw [h_a_eq, h_b_eq, h_a_eq_b]
  | inr h_idx1'_ge_idx2' =>
    have h_idx'_le_idx2' : idx1' > idx2' ∨ idx1' = idx2' := by omega
    cases h_idx'_le_idx2' with
    | inl h_idx1'_lt_idx2' =>
      obtain h_neq := h_pairwise idx2' idx1' h_map_idx2_lt_length h_map_idx1_lt_length h_idx1'_lt_idx2'
      apply h_neq
      rw [List.getElem_eq_iff_getElem?_eq]
      rw [h_b_eq, h_a_eq, h_a_eq_b]
    | inr h_idx1'_eq_idx2' =>
      subst h_a_eq_b
      rw [<-h_idx1'_eq, <-h_idx2'_eq] at h_idx1'_eq_idx2'
      apply h_map_inj at h_idx1'_eq_idx2'
      . omega
      . assumption
      . assumption

end CausalNetwork
