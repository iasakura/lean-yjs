import LeanYjs.Item
import LeanYjs.ItemOriginOrder
import LeanYjs.ActorId
import LeanYjs.ItemOrder

import Mathlib.Tactic.Set

variable {A : Type} [BEq A]

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : ClosedPredicate A)

def ItemSet := { i : YjsItem A // P.val i }

def OriginLeq' (x y : ItemSet P) : Prop :=
  x = y ∨ OriginLt A P (↑x.1) (↑y.1)

def YjsLt' (x y : ItemSet P) : Prop :=
  ∃ h, @YjsLt A P h (↑x.1) (↑y.1)

def YjsLeq' (x y : ItemSet P) : Prop :=
  ∃ h, @YjsLeq A P h (↑x.1) (↑y.1)

def YjsInvariant :=
  forall h (x y : YjsItem A),
    P.val x -> P.val y ->
    @YjsLt A P h x y ->
      (∃ h, @YjsLeq A P h x (y.origin)) ∨
      (∃ h,  @YjsLt A P h (y.origin) (x.origin)) ∨
      (x.origin = y.origin ∧ ((∃ h, @YjsLt A P h x.rightOrigin y) ∨ x.id < y.id))

def ItemSetInvariant :=
  P.val YjsPtr.first ∧
  P.val YjsPtr.last ∧
  (∀ (o : YjsPtr A) r id c, P.val (YjsItem.item o r id c) -> P.val o) ∧
  (∀ o (r : YjsPtr A) id c, P.val (YjsItem.item o r id c) -> P.val r) ∧
  (∀ (x y : YjsPtr A), P.val x -> P.val y -> OriginLt A P x y -> OriginLt A P y x -> False) ∧
  YjsInvariant P

lemma origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.origin := by
  intros x px
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  simp at *
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.origin] at *
  tauto

lemma right_origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.rightOrigin := by
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
  | ltOriginOrder _ _ hlt =>
    have hlt2 : @OriginLt A P YjsPtr.first o := by
      apply OriginLt.ltOrigin (x := YjsPtr.first) (y := YjsPtr.itemPtr o)
      . apply hinv.1
      . apply origin_lt_p1 at hlt; assumption
      . apply OriginLtStep.lt_first
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.first) (y := o) <;> try assumption
    apply origin_lt_p1 at hlt; assumption
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
  | ltOriginOrder _ _ hlt =>
    have hlt2 : @OriginLt A P o YjsPtr.last := by
      apply OriginLt.ltOrigin (x := YjsPtr.itemPtr o) (y := YjsPtr.last)
      . apply origin_lt_p2 at hlt; assumption
      . apply hinv.2.1
      . apply OriginLtStep.lt_last
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.last) (y := o) <;> try assumption
    apply origin_lt_p2 at hlt; assumption
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
  | ltOriginOrder _ _ hlt =>
    have hlt' : OriginLt _ P YjsPtr.first YjsPtr.last := by
      obtain ⟨ P, ⟨ a, b, c ⟩ ⟩ := P
      apply OriginLt.ltOrigin <;> try assumption
      apply OriginLtStep.lt_first_last
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.first) (y := YjsPtr.last) <;> assumption
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    apply not_item_lt_first at hlt2 <;> assumption

lemma not_first_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.first YjsPtr.first := by
  intros hinv h hlt
  have h: OriginLt A P YjsPtr.first YjsPtr.first := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_item_lt_first hinv at hlt2; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
  apply hanti (x := YjsPtr.first) (y := YjsPtr.first) <;> try assumption

lemma not_last_lt_last {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.last := by
  intros hinv h hlt
  have h: OriginLt A P YjsPtr.last YjsPtr.last := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_last_lt_item hinv at hlt1; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
  apply hanti (x := YjsPtr.last) (y := YjsPtr.last) <;> try assumption

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
