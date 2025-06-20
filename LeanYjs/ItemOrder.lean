import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder

import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Tauto
import Mathlib.Data.Nat.Basic

def max4 (x y z w : Nat) : Nat :=
  max (max x y) (max z w)

mutual
  inductive YjsLt {A : Type} (P : @ClosedPredicate A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltConflict h i1 i2 : ConflictLt P h i1 i2 -> YjsLt P (h + 1) i1 i2
    | ltOriginOrder i1 i2 : P.val i1 -> P.val i2 -> OriginLt _ i1 i2 -> YjsLt P 0 i1 i2
    | ltOrigin h x o r id c : P.val (YjsItem.item o r id c) -> YjsLt P h x o -> YjsLt P (h + 1) x (YjsItem.item o r id c)
    | ltRightOrigin h o r id c x : P.val (YjsItem.item o r id c) -> YjsLt P h r x -> YjsLt P (h + 1) (YjsItem.item o r id c) x

  inductive ConflictLt {A : Type} (P : @ClosedPredicate A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 :
      YjsLt P h1 l2 l1
      -> YjsLt P h2 (YjsItem.item l1 r1 id1 c1) r2
      -> YjsLt P h3 l1 (YjsItem.item l2 r2 id2 c2)
      -> YjsLt P h4 (YjsItem.item l2 r2 id2 c2) r1
      -> ConflictLt P (max4 h1 h2 h3 h4 + 1) (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
    | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) :
      YjsLt P h1 (YjsItem.item l r1 id1 c1) r2
      -> YjsLt P h2 (YjsItem.item l r2 id2 c2) r1
      -> id1 < id2
      -> ConflictLt P (max h1 h2 + 1) (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)
end

def YjsLt' {A} (P : ClosedPredicate A) (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLt A P h x y

lemma yjs_lt_p1_aux {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  (YjsLt P h x y -> P.val x) ∧ (ConflictLt P h x y -> P.val x) := by
    apply Nat.strongRecOn' (P := fun h => ∀ x y, (YjsLt P h x y -> P.val x) ∧ (ConflictLt P h x y -> P.val x))
    intros n ih x y
    constructor
    . intro hlt
      cases hlt with
      | ltConflict h x y hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, h ⟩ := ih h hlt_h x y
        apply h ; assumption
      | ltOriginOrder x y _ =>
        assumption
      | ltOrigin h x o r id c hval hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ ih, _ ⟩ := ih h hlt_h x o
        apply ih; assumption
      | ltRightOrigin h o r id c x hval hlt =>
        assumption
    . intro hlt
      cases hlt with
      | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
        have hlt_h : h2 < max4 h1 h2 h3 h4 + 1 := by
          unfold max4
          omega
        let ⟨ ih, _ ⟩ := ih h2 hlt_h (YjsPtr.itemPtr (YjsItem.item l1 r1 id1 c1)) r2
        apply ih hlt2
      | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
        have hlt_h : h1 < max h1 h2 + 1 := by
          omega
        let ⟨ ih, _ ⟩ := ih h1 hlt_h (YjsPtr.itemPtr (YjsItem.item l r1 id1 c1)) r2
        apply ih hlt1

lemma yjs_lt_p1 {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLt P h x y -> P.val x := by
    intros x y hlt
    let ⟨ h, _ ⟩ := @yjs_lt_p1_aux A P h x y
    tauto

lemma conflict_lt_p1 {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  ConflictLt P h x y -> P.val x := by
    intros x y hlt
    let ⟨ _, h ⟩ := @yjs_lt_p1_aux A P h x y
    tauto

lemma yjs_lt_p2_aux {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  (YjsLt P h x y -> P.val y) ∧ (ConflictLt P h x y -> P.val y) := by
    apply Nat.strongRecOn' (P := fun h => ∀ x y, (YjsLt P h x y -> P.val y) ∧ (ConflictLt P h x y -> P.val y))
    intros n ih x y
    constructor
    . intro hlt
      cases hlt with
      | ltConflict h x y hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, h ⟩ := ih h hlt_h x y
        apply h ; assumption
      | ltOriginOrder x y _ =>
        assumption
      | ltOrigin h x o r id c hval hlt =>
        assumption
      | ltRightOrigin h o r id c x hval hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ ih, _ ⟩ := ih h hlt_h r y
        apply ih hlt
    . intro hlt
      cases hlt with
      | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
        have hlt_h : h3 < max4 h1 h2 h3 h4 + 1 := by
          unfold max4
          omega
        let ⟨ _, ih ⟩ := ih h3 hlt_h l1 (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2))
        tauto
      | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
        apply yjs_lt_p1 hlt2

lemma yjs_lt_p2 {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLt P h x y -> P.val y := by
    intros x y hlt
    let ⟨ h, _ ⟩ := @yjs_lt_p2_aux A P h x y
    tauto

lemma conflict_lt_p2 {A : Type} {P : @ClosedPredicate A} {h : Nat} : forall {x y : YjsPtr A},
  ConflictLt P h x y -> P.val y := by
    intros x y hlt
    let ⟨ _, h ⟩ := @yjs_lt_p2_aux A P h x y
    tauto

def YjsLeq {A : Type} (P : @ClosedPredicate A) (h : Nat) (x y : YjsPtr A) : Prop :=
  x = y ∨ YjsLt P h x y

def YjsLeq' {A} (P : ClosedPredicate A) (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLeq A P h x y

def ConflictLt' {A} (P : ClosedPredicate A) (x y : YjsPtr A) : Prop :=
  ∃ h, ConflictLt P h x y

lemma yjs_lt_cases A P h (x y : YjsPtr A) :
  YjsLt P h x y ->
    (x = YjsPtr.first ∧ (y = YjsPtr.last ∨ ∃ i, y = YjsPtr.itemPtr i)) ∨
    (y = YjsPtr.last ∧ (x = YjsPtr.first ∨ ∃ i, x = YjsPtr.itemPtr i)) ∨
    (∃ x', x = YjsPtr.itemPtr x' ∧ YjsLeq' P x'.rightOrigin y) ∨
    (∃ y', y = YjsPtr.itemPtr y' ∧ YjsLeq' P x y'.origin) ∨
    ConflictLt' P x y := by
  intros hlt
  cases hlt with
  | ltConflict h x y hlt =>
    right; right; right; right
    apply Exists.intro h; assumption
  | ltOriginOrder x y px py hlt =>
    cases hlt with
    | lt_left o r id c =>
      right; right; right; left
      simp [YjsItem.origin]
      exists 0; left; simp
    | lt_right o r id c =>
      right; right; left
      simp [YjsItem.rightOrigin]
      exists 0; left; simp
    | lt_first_last =>
      left; simp
    | lt_first =>
      left; simp
    | lt_last =>
      right; left; simp
  | ltOrigin h x o r id c hval hlt =>
    right; right; right; left; simp
    exists h; right; simp [YjsItem.origin]; assumption
  | ltRightOrigin h o r id c x hval hlt =>
    right; right; left; simp
    exists h; right; simp [YjsItem.rightOrigin]; assumption

-- inductive LtSequence {A : Type} (P : @ClosedPredicate A) : YjsPtr A -> YjsPtr A -> List (YjsPtr A) -> Prop where
--   | base : forall x, LtSequence P x x []
--   | step1 : forall x y z is h, ConflictLt P h x y -> LtSequence P y z is -> LtSequence P x z (y :: is)
--   | step2 : forall x y z is, OriginLt _ x y -> LtSequence P y z is -> LtSequence P x z (y :: is)

-- lemma LtSequenceConcat {A : Type} {P : @ClosedPredicate A} {x y z : YjsPtr A} {is1 is2 : List (YjsPtr A)} :
--   LtSequence P x y is1 -> LtSequence P y z is2 -> LtSequence P x z (is1 ++ is2) := by
--     intro lt1
--     induction lt1 with
--     | base x =>
--       intros lt2
--       apply lt2
--     | step1 x y z is _ lt1 lt2 ih =>
--       intros lt
--       apply LtSequence.step1 <;> try assumption
--       apply ih
--       assumption
--     | step2 x y z is lt1 lt2 ih =>
--       intros lt
--       apply LtSequence.step2 <;> try assumption
--       apply ih
--       assumption

-- lemma YjsLtSequence (A : Type) (P : ClosedPredicate A): forall (x y : YjsPtr A) h, YjsLt P h x y ->
--   ∃ is : List (YjsPtr A), LtSequence P x y is := by
--     intros x y h
--     apply Nat.strongRecOn' (P := fun h => ∀ x y, YjsLt P h x y -> ∃ is : List (YjsPtr A), LtSequence P x y is)
--     intros h' ih x y lt
--     match lt with
--     | YjsLt.ltConflict h x y _ =>
--       apply Exists.intro [y]
--       apply LtSequence.step1 <;> try assumption
--       apply LtSequence.base
--     | YjsLt.ltOriginOrder x y hx hy hlt =>
--       apply Exists.intro [y]
--       apply LtSequence.step2 <;> try assumption
--       apply LtSequence.base
--     | YjsLt.ltOrigin h x o r id c hval hlt =>
--       have hlt_h : h < h + 1 := by
--         omega
--       let ⟨ is, ih ⟩ := ih h hlt_h x o hlt
--       apply Exists.intro (is ++ [o])
--       apply LtSequenceConcat ih
--       apply LtSequence.step1
