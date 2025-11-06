import Init.Data
import Init.Data.List.Basic

import Mathlib.Tactic.Cases

import LeanYjs.ListLemmas
import LeanYjs.ClientId
import LeanYjs.Network.CausalOrder

namespace NetworkModels

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
  | broadcast_deliver_local : locallyOrdered network.toNodeHistories i (Event.Deliver e1) (Event.Broadcast e2) → HappensBefore network e1 e2
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

inductive HappensBeforeOnlyBroadcast {A} [DecidableEq A] [Message A] (network : NetworkBase A) : A → A → Prop
  | broadcast_broadcast_local : locallyOrdered network.toNodeHistories i (Event.Broadcast e1) (Event.Broadcast e2) → HappensBeforeOnlyBroadcast network e1 e2
  | trans : HappensBeforeOnlyBroadcast network e1 e2 → HappensBeforeOnlyBroadcast network e2 e3 → HappensBeforeOnlyBroadcast network e1 e3

abbrev HappensBeforeOrEqual {A} [DecidableEq A] [Message A] (network : NetworkBase A) (a b : A) : Prop :=
  a = b ∨ HappensBefore network a b

theorem HappensBefore.trans1 {A} [DecidableEq A] [Message A] {network : NetworkBase A} {a b c : A} :
  HappensBeforeOrEqual network a b →
  HappensBefore network b c →
  HappensBefore network a c := by
  intros h_ab h_bc
  cases h_ab with
  | inl h_eq =>
    subst h_eq
    assumption
  | inr h_hb_ab =>
    apply HappensBefore.trans h_hb_ab h_bc

theorem HappensBefore.trans2 {A} [DecidableEq A] [Message A] {network : NetworkBase A} {a b c : A} :
  HappensBefore network a b →
  HappensBeforeOrEqual network b c →
  HappensBefore network a c := by
  intros h_ab h_bc
  cases h_bc with
  | inl h_eq =>
    subst h_eq
    assumption
  | inr h_hb_bc =>
    apply HappensBefore.trans h_ab h_hb_bc

theorem HappensBeforeSame_HappensBeforeOnlyBroadcast_or_HappensBeforeDeliver_exists {A} [DecidableEq A] [Message A] {network : CausalNetwork A} (a b : A) :
  HappensBefore network.toNetworkBase a b →
  HappensBeforeOnlyBroadcast network.toNetworkBase a b ∨
  ∃ a' b' i,
    (HappensBeforeOrEqual network.toNetworkBase a a') ∧
    locallyOrdered network.toNodeHistories i (Event.Deliver a') (Event.Broadcast b') ∧
    (HappensBeforeOrEqual network.toNetworkBase b' b) := by
  intros h_a_hb_a
  induction h_a_hb_a with
  | broadcast_broadcast_local h_local =>
    left
    apply HappensBeforeOnlyBroadcast.broadcast_broadcast_local h_local
  | @broadcast_deliver_local i e1 e2 h_local =>
    right
    use e1, e2, i
    simp [HappensBeforeOrEqual]
    assumption
  | @trans e1 e2 e3 h_ab h_bc ih_ab ih_bc =>
    cases ih_ab with
    | inl h_e2_e2 =>
      cases ih_bc with
      | inl h_e3_e3 =>
        left
        apply HappensBeforeOnlyBroadcast.trans h_e2_e2 h_e3_e3
      | inr h_e2_e3 =>
        obtain ⟨ a', b', i, h_a_e2, h_local, h_b_e3 ⟩ := h_e2_e3
        right
        use a', b', i
        constructor
        . right
          apply HappensBefore.trans2 h_ab h_a_e2
        . constructor
          . assumption
          . assumption
    | inr h_e1_e2 =>
      obtain ⟨ a', b', i, h_a_e1, h_local, h_b_e2 ⟩ := h_e1_e2
      right
      use a', b', i
      constructor
      . assumption
      . constructor
        . assumption
        . right
          apply HappensBefore.trans1 h_b_e2 h_bc

theorem nodup_getElem_unique : forall {A} [DecidableEq A] {l : List A} {x idx},
  l.Nodup →
  idx < l.length →
  l[idx]? = some x →
  ∀ j : Nat, j < l.length → l[j]? = some x → j = idx := by
  intros A _ l x idx h_nodup h_idx_lt_length h_getElem_eq
  intros j hlt heq
  rw [List.nodup_iff_pairwise_ne] at h_nodup
  rw [List.pairwise_iff_getElem] at h_nodup
  have h_or : idx < j ∨ idx = j ∨ idx > j := by
    omega
  rcases h_or with h_lt | h_eq | h_lt
  . exfalso
    apply h_nodup idx j (by omega) (by omega) h_lt
    rw [List.getElem_eq_iff_getElem?_eq l idx j (by omega), heq, h_getElem_eq]
  . subst h_eq; simp
  . exfalso
    apply h_nodup j idx (by omega) (by omega) (by omega)
    rw [List.getElem_eq_iff_getElem?_eq l j  idx (by omega), heq, h_getElem_eq]

theorem nodup_prefix_unique {A} [DecidableEq A] {lp1 ls1 lp2 ls2 : List A} {x : A} :
  (lp1 ++ [x] ++ ls1).Nodup →
  lp1 ++ [x] ++ ls1 = lp2 ++ [x] ++ ls2 →
  lp1 = lp2 := by
  intros h_nodup h_eq
  have h_getElem_lp1_length : (lp1 ++ [x] ++ ls1)[lp1.length]? = some x := by
    rw [List.append_assoc, List.getElem?_append_right (by simp)]
    simp
  have h_getElem_lp2_length : (lp1 ++ [x] ++ ls1)[lp2.length]? = some x := by
    rw [h_eq, List.append_assoc, List.getElem?_append_right (by simp)]
    simp
  have h_lp2_length_eq_lp1_length : lp1.length = lp2.length := by
    apply nodup_getElem_unique h_nodup (by simp) at h_getElem_lp1_length
    apply h_getElem_lp1_length _ (by rw [h_eq]; simp) at h_getElem_lp2_length
    simp [h_getElem_lp2_length]
  rw [List.append_assoc] at h_eq
  rw [List.append_assoc] at h_eq
  obtain ⟨ h_eq1, h_eq2 ⟩ := List.append_inj h_eq h_lp2_length_eq_lp1_length
  assumption

theorem locallyOrdered_asymm {A} [DecidableEq A] [Message A] {network : NetworkBase A} {i : ClientId} {e1 e2 : Event A} :
  locallyOrdered network.toNodeHistories i e1 e2 →
  locallyOrdered network.toNodeHistories i e2 e1 →
  False := by
  intros h_e1_e2 h_e2_e1
  have h_nodup_i := network.toNodeHistories.event_distinct i
  obtain ⟨ l1, l2, l3, h_history_eq1 ⟩ := h_e1_e2
  obtain ⟨ l1', l2', l3', h_history_eq2 ⟩ := h_e2_e1

  have h_l1'_1_l2' : l1' ++ [e2] ++ l2' = l1 := by
    rw [h_history_eq1] at h_history_eq2 h_nodup_i
    have h_eq1 : l1 ++ [e1] ++ l2 ++ [e2] ++ l3 = l1 ++ [e1] ++ (l2 ++ [e2] ++ l3) := by simp
    rw [h_eq1] at h_history_eq2 h_nodup_i
    have h_eq := nodup_prefix_unique h_nodup_i h_history_eq2
    simp [h_eq]
  have h_l1_1_l2 : l1 ++ [e1] ++ l2 = l1' := by
    rw [h_history_eq2] at h_nodup_i
    rw [h_history_eq2] at h_history_eq1
    have h_eq1 : l1' ++ [e2] ++ l2' ++ [e1] ++ l3' = l1' ++ [e2] ++ (l2' ++ [e1] ++ l3') := by simp
    rw [h_eq1] at h_history_eq2 h_nodup_i h_history_eq1
    have h_eq := nodup_prefix_unique h_nodup_i h_history_eq1
    simp [h_eq]
  rw [<-h_l1'_1_l2'] at h_l1_1_l2
  simp at h_l1_1_l2

theorem locallyOrdered_trans {A} [DecidableEq A] [Message A] {network : NetworkBase A} {i : ClientId} {e1 e2 e3 : Event A} :
  locallyOrdered network.toNodeHistories i e1 e2 →
  locallyOrdered network.toNodeHistories i e2 e3 →
  locallyOrdered network.toNodeHistories i e1 e3 := by
  intros h_e1_e2 h_e2_e3
  obtain ⟨ l1, l2, l3, h_history_eq1 ⟩ := h_e1_e2
  obtain ⟨ l1', l2', l3', h_history_eq2 ⟩ := h_e2_e3
  use l1, (l2 ++ [e2] ++ l2'), l3'
  have h_nodup_i := network.toNodeHistories.event_distinct i
  have h_eq : l1 ++ [e1] ++ l2 = l1' := by
    rw [h_history_eq1] at h_history_eq2 h_nodup_i
    have h_eq2 : l1' ++ [e2] ++ l2' ++ [e3] ++ l3' = l1' ++ [e2] ++ (l2' ++ [e3] ++ l3') := by
      simp
    rw [h_eq2] at h_history_eq2
    have h_eq := nodup_prefix_unique h_nodup_i h_history_eq2
    simp [h_eq]
  have h_eq' : l1 ++ [e1] ++ (l2 ++ [e2] ++ l2') = (l1 ++ [e1] ++ l2) ++ [e2] ++ l2' := by
    simp
  rw [h_eq', h_eq]
  assumption

theorem HappensBeforeOnlyBroadcast_locallyOrdered {A} [DecidableEq A] [Message A] {network : NetworkBase A} {a b : A} :
  HappensBeforeOnlyBroadcast network a b →
  ∃i, locallyOrdered network.toNodeHistories i (Event.Broadcast a) (Event.Broadcast b) := by
  intro h_hb
  induction h_hb with
  | broadcast_broadcast_local h_local =>
    constructor; assumption
  | @trans e1 e2 e3 h_e1_e2 h_e2_e3 ih_e1_e2 ih_e2_e3 =>
    obtain ⟨ i, h_e1_e2_local ⟩ := ih_e1_e2
    obtain ⟨ j, h_e2_e3_local ⟩ := ih_e2_e3
    have h_i_eq_j : i = j := by
      obtain ⟨ l1, l2, l3, h_history_eq1 ⟩ := h_e1_e2_local
      obtain ⟨ l1', l2', l3', h_history_eq2 ⟩ := h_e2_e3_local
      have h_e2_mem_history_i : Event.Broadcast e2 ∈ network.toNodeHistories.histories i := by
        rw [h_history_eq1]
        simp
      have h_e2_mem_history_j : Event.Broadcast e2 ∈ network.toNodeHistories.histories j := by
        rw [h_history_eq2]
        simp
      obtain ⟨ h_eq, _ ⟩ := network.msg_id_unique h_e2_mem_history_i h_e2_mem_history_j rfl
      assumption
    subst h_i_eq_j
    exists i
    apply locallyOrdered_trans h_e1_e2_local h_e2_e3_local

-- suppose a < a
-- if a < a only consists of broadcast_broadcast_local, then we can conclude a.idx < a.idx, which is a contradiction
-- otherwise, if a < a is break down into a < b and b < a and a < b is broadcast_deliver_local, we now have
-- D(a) <_i B(b) and b < a.
-- so by causal_delivery, we have D(b) <_i D(a), but it followed by D(b) <_i B(b), it contradicts with deliver_locally.
lemma HappensBefore_assym [Message A] [DecidableEq A] {network : CausalNetwork A} a b :
  HappensBefore network.toNetworkBase a b →
  HappensBefore network.toNetworkBase b a → False := by
  intros h_ab h_ba
  have h_aa : HappensBefore network.toNetworkBase a a := by
    apply HappensBefore.trans h_ab h_ba
  apply HappensBeforeSame_HappensBeforeOnlyBroadcast_or_HappensBeforeDeliver_exists at h_aa
  cases h_aa with
  | inl h_broadcast_only =>
    apply HappensBeforeOnlyBroadcast_locallyOrdered at h_broadcast_only
    obtain ⟨ i, h_local ⟩ := h_broadcast_only
    apply locallyOrdered_asymm h_local h_local
  | inr h_deliver_exists =>
    obtain ⟨ a', b', i, h_a_a', h_local, h_b'_a ⟩ := h_deliver_exists
    have h_mem_deliver_a' : Event.Deliver a' ∈ network.toNetworkBase.histories i := by
      obtain ⟨ l1, l2, l3, h_history_eq ⟩ := h_local
      rw [h_history_eq]
      simp
    have h_lo_deliver_b_deliver_a : locallyOrdered network.toNodeHistories i (Event.Deliver b') (Event.Deliver a') := by
      apply network.causal_delivery h_mem_deliver_a'
      apply HappensBefore.trans1 h_b'_a
      apply HappensBefore.trans2 h_ab
      right; apply HappensBefore.trans2 h_ba
      assumption
    have h_lo_broadcast_b'_deliver_b' : locallyOrdered network.toNodeHistories i (Event.Broadcast b') (Event.Deliver b') := by
      have h_mem_deliver_b' : Event.Deliver b' ∈ network.toNetworkBase.histories i := by
        obtain ⟨ l1, l2, l3, h_history_eq ⟩ := h_lo_deliver_b_deliver_a
        rw [h_history_eq]
        simp
      apply network.deliver_locally h_mem_deliver_b'
    have h_lo_broadcast_b'_deliver_a' : locallyOrdered network.toNodeHistories i (Event.Broadcast b') (Event.Deliver a') := by
      apply locallyOrdered_trans h_lo_broadcast_b'_deliver_b' h_lo_deliver_b_deliver_a
    apply locallyOrdered_asymm h_lo_broadcast_b'_deliver_a' h_local

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
    apply HappensBefore_assym a.elem b.elem h_ab h_ba
  lt_iff_le_not_ge := by
    intros a b
    constructor
    . intros h_lt
      constructor
      . right; assumption
      . intro h_ge
        cases h_ge with
        | inl h_eq =>
          subst h_eq
          apply HappensBefore_assym b.elem b.elem h_lt h_lt
        | inr h_hb =>
          apply HappensBefore_assym a.elem b.elem h_lt h_hb
    . intros h_le_not_ge
      obtain ⟨ h_le, h_not_ge ⟩ := h_le_not_ge
      cases h_le with
      | inr h_hb =>
        assumption
      | inl h_eq =>
        subst a
        exfalso
        apply h_not_ge
        left; simp

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

omit [Operation A] in theorem hb_consistent_local_history_aux i ms ms' :
  ms ++ ms' = network.toDeliverMessages i →
  hb_consistent (hb := instCausalNetworkElemCausalOrder network) ms' := by
  intros h_ms
  -- simp [CausalNetwork.toDeliverMessages] at h_ms
  induction ms' generalizing ms with
  | nil =>
    simp [hb_consistent.nil]
  | cons h t ih =>
    rw [List.append_cons] at h_ms
    apply hb_consistent.cons
    . apply ih (ms ++ [h]) h_ms
    . intros m h_mem h_le
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
      cases h_le with
      | inr h_lt =>
        apply network.causal_delivery (i := i) at h_lt
        . apply locallyOrdered_asymm h_locally_ordered h_lt
        . rw [h_history_eq]
          simp
      | inl h_eq =>
        subst h_eq
        have h_m_idx_eq1 : (network.histories i)[l1.length]? = Event.Deliver m.elem := by
          rw [h_history_eq]
          simp

        have h_m_idx_eq2 : (network.histories i)[l1.length + 1 + l2.length]? = Event.Deliver m.elem := by
          rw [h_history_eq]
          simp
          rw [List.getElem?_append_right (by omega)]
          have h_idx_eq : l1.length + 1 + l2.length - l1.length = (l1.length + l2.length - l1.length) + 1 := by omega
          rw [h_idx_eq]
          rw [List.getElem?_cons_succ]
          simp

        rw [List.getElem?_eq_getElem] at h_m_idx_eq1 h_m_idx_eq2
        . have h_nodup_history := network.event_distinct i
          rw [List.nodup_iff_pairwise_ne] at h_nodup_history
          rw [List.pairwise_iff_getElem] at h_nodup_history
          rw [h_history_eq] at h_nodup_history
          apply h_nodup_history l1.length (l1.length + 1 + l2.length)
          . omega
          . suffices some (l1 ++ [Event.Deliver m.elem] ++ l2 ++ [Event.Deliver m.elem] ++ l3)[l1.length] = some (l1 ++ [Event.Deliver m.elem] ++ l2 ++ [Event.Deliver m.elem] ++ l3)[l1.length + 1 + l2.length] by
              rw [Option.some_inj] at this
              assumption
            rw [<-List.getElem?_eq_getElem]
            rw [<-List.getElem?_eq_getElem]
            simp
            have h_eq : l1.length + 1 + l2.length = l1.length + (l2.length + 1) := by omega
            rw [h_eq]
            rw [List.getElem?_append_right (by omega)]
            simp
        . rw [h_history_eq]
          simp
          omega
        . rw [h_history_eq]
          simp

omit [Operation A] in theorem hb_consistent_local_history i :
  hb_consistent (hb := instCausalNetworkElemCausalOrder network) (network.toDeliverMessages i) := by
  apply hb_consistent_local_history_aux network i []
  simp

omit [Operation A] in theorem toDeliverMessages_Nodup (network : CausalNetwork A) : (network.toDeliverMessages i).Nodup := by
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

end NetworkModels
