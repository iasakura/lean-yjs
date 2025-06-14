import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ItemOriginOrder
import LeanYjs.ActorId
import LeanYjs.ItemOrder

import Mathlib.Tactic.Set

variable {A : Type} [BEq A]

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : ClosedPredicate A)

def YjsLt' (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLt A P h x y

def YjsLeq' (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLeq A P h x y

structure ItemSetInvariant where
  origin_not_leq : ∀ (o r c id), P.val (YjsItem.item o r id c) -> ∀ h, ¬ YjsLeq P h r o
  origin_nearest_reachable : ∀ (o r c id x),
    P.val (YjsItem.item o r id c) ->
    OriginReachable A (YjsItem.item o r id c) x ->
    (∃ h, YjsLeq P h x o) ∨ (∃ h, YjsLeq P h r x)
  same_id_ordered : ∀ (x y : YjsItem A),
    P.val x -> P.val y ->
    x ≠ y ->
    x.id = y.id ->
    YjsLt' P x y.origin ∨
    YjsLt' P y x.origin ∨
    YjsLt' P x.rightOrigin y ∨
    YjsLt' P y.rightOrigin x


@[simp] lemma origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.origin := by
  intros x px
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  simp at *
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.origin] at *
  tauto

@[simp] lemma right_origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.rightOrigin := by
  intros x px
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  simp at *
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.rightOrigin] at *
  tauto

lemma not_item_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsItem A), ¬ @YjsLt A P h o YjsPtr.first := by
  intros hinv h o
  apply @Nat.strongRecOn' (P := fun h => ∀ (o : YjsItem A), ¬ @YjsLt A P h o YjsPtr.first)
  intros n ih o hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder o _ po pf hlt =>
    cases hlt with
    | lt_right o' _ id  c =>
      apply hinv.origin_not_leq _ _ _ _ po 0
      cases o' with
      | last =>
        right
        obtain ⟨ P, hP ⟩ := P
        apply YjsLt.ltOriginOrder <;> try assumption
        . apply hP.baseLast
        . apply OriginLt.lt_first_last
      | first =>
        left
        simp
      | itemPtr item =>
        right
        obtain ⟨ P, hP ⟩ := P
        apply YjsLt.ltOriginOrder <;> try assumption
        . simp at *
          apply hP.closedLeft; assumption
        . apply OriginLt.lt_first
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    have hlt_h2 : h2 < max h1 h2 + 1 := by
      omega
    apply ih _ hlt_h2 _ hlt2

lemma not_last_lt_item {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsItem A), ¬ @YjsLt A P h YjsPtr.last o := by
  intros hinv h o
  apply @Nat.strongRecOn' (P := fun h => ∀ (o : YjsItem A), ¬ @YjsLt A P h YjsPtr.last o)
  intros n ih o hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ _ hpo hlt =>
    have hlt2 : @OriginLt A o YjsPtr.last := by
      apply OriginLt.lt_last
    cases hlt with
    | lt_left o' r id c =>
      apply hinv.origin_not_leq _ _ _ _ hpo 0
      cases r with
      | last =>
        left
        simp
      | first =>
        right
        obtain ⟨ P, hP ⟩ := P
        apply YjsLt.ltOriginOrder <;> try assumption
        . apply hP.baseFirst
        . apply OriginLt.lt_first_last
      | itemPtr item =>
        right
        obtain ⟨ P, hP ⟩ := P
        apply YjsLt.ltOriginOrder <;> try assumption
        . simp at *
          apply hP.closedRight; assumption
        . apply OriginLt.lt_last
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    have hlt_h2 : h1 < max h1 h2 + 1 := by
      omega
    apply ih _ hlt_h2 _ hlt1

lemma not_last_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.first := by
  intros hinv h
  apply @Nat.strongRecOn' (P := fun h => ¬ @YjsLt A P h YjsPtr.last YjsPtr.first)
  intros n ih hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ _ _ hlt =>
    cases hlt
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    apply not_item_lt_first at hlt2 <;> assumption

lemma not_first_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.first YjsPtr.first := by
  intros hinv h hlt
  have h: OriginLt A YjsPtr.first YjsPtr.first := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_item_lt_first hinv at hlt2; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

lemma not_last_lt_last {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.last := by
  intros hinv h hlt
  have h: OriginLt A YjsPtr.last YjsPtr.last := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_last_lt_item hinv at hlt1; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

lemma not_ptr_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h o YjsPtr.first := by
  intros hinv h o
  cases o with
  | itemPtr item =>
    apply not_item_lt_first hinv
  | first =>
    apply not_first_lt_first hinv
  | last =>
    apply not_last_lt_first hinv

lemma not_last_lt_ptr {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h YjsPtr.last o := by
  intros hinv h o
  cases o with
  | itemPtr item =>
    apply not_last_lt_item hinv
  | first =>
    apply not_last_lt_first hinv
  | last =>
    apply not_last_lt_last hinv

lemma yjs_lt_p_trans {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  @YjsLt A P h1 x y -> @YjsLt A P h2 y z -> @YjsLt A P (max h1 h2 + 1) x z := by
  intros hlt1 hlt2
  cases y with
  | first =>
    apply not_ptr_lt_first inv at hlt1; contradiction
  | last =>
    apply not_last_lt_ptr inv at hlt2; contradiction
  | itemPtr y =>
    apply YjsLt.ltTrans <;> assumption

lemma yjs_leq_p_trans1 {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  @YjsLeq A P h1 x y -> @YjsLt A P h2 y z -> ∃ h, @YjsLt A P h x z := by
  intros hleq hlt
  cases hleq with
  | inl heq =>
    rw [heq]
    exists h2
  | inr hlt =>
    exists (max h1 h2 + 1)
    apply yjs_lt_p_trans <;> assumption

lemma yjs_leq_p_trans2 {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  @YjsLt A P h1 x y -> @YjsLeq A P h2 y z -> ∃ h, @YjsLt A P h x z := by
  intros hlt hleq
  cases hleq with
  | inl heq =>
    rw [<-heq]
    exists h1
  | inr hlt =>
    exists (max h1 h2 + 1)
    apply yjs_lt_p_trans <;> assumption

lemma yjs_leq_p_trans {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  @YjsLeq A P h1 x y -> @YjsLeq A P h2 y z -> ∃ h, @YjsLeq A P h x z := by
  intros hleq1 hleq2
  cases hleq1 with
  | inl heq =>
    rw [heq]
    exists h2
  | inr hlt =>
    cases hleq2 with
    | inl heq =>
      rw [<-heq]
      exists h1
      right
      assumption
    | inr hlt =>
      exists (max h1 h2 + 1)
      right
      apply yjs_lt_p_trans <;> assumption

-- lemma origin_lt_p1 {A} {P : @ClosedPredicate A} {x y : YjsPtr A} (h : OriginLt _ x y) : P.val x := by
--   sorry

-- lemma origin_lt_p2 {A} {P : @ClosedPredicate A} {x y : YjsPtr A} (h : OriginLt _ x y) : P.val y := by
--   cases h with
--   | ltOrigin  y hpx hpy hlt
--     assumption
--   -- | ltReachableOrigin o r id c t ho hr ht hreach hlt =>
--   --   assumption
--   -- | ltReachableRight o r id c t ho hr ht hreach hlt =>
--   --   assumption
--   | ltTrans x y z hx hy hz hlt1 hlt2 =>
--     assumption
