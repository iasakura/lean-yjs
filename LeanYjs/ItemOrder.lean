import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder

import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Nat.Basic

def max4 (x y z w : Nat) : Nat :=
  max (max x y) (max z w)

mutual
inductive YjsLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
  | ltConflict h i1 i2 : ConflictLt h i1 i2 -> YjsLt (h + 1) i1 i2
  | ltOriginOrder i1 i2 : OriginLt _ i1 i2 -> YjsLt 0 i1 i2
  | ltTrans h1 h2 x y z: YjsLt h1 x y -> YjsLt h2 y z -> YjsLt (max h1 h2 + 1) x z

inductive ConflictLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 :
    YjsLt h1 l2 l1
    -> YjsLt h2 (YjsItem.item l1 r1 id1 c1) r2
    -> YjsLt h3 l1 (YjsItem.item l2 r2 id2 c2)
    -> YjsLt h4 (YjsItem.item l2 r2 id2 c2) r1
    -> ConflictLt (max4 h1 h2 h3 h4 + 1) (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
  | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) :
    YjsLt h1 (YjsItem.item l r1 id1 c1) r2
    -> YjsLt h2 (YjsItem.item l r2 id2 c2) r1
    -> id1 < id2
    -> ConflictLt (max h1 h2 + 1) (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)
end

def YjsLeq {A : Type} (h : Nat) (x y : YjsPtr A) : Prop :=
  x = y ∨ YjsLt h x y

inductive LtSequence {A : Type} : YjsPtr A -> YjsPtr A -> List (YjsPtr A) -> Prop where
  | base : forall x, LtSequence x x []
  | step1 : forall x y z is h, ConflictLt h x y -> LtSequence y z is -> LtSequence x z (y :: is)
  | step2 : forall x y z is, OriginLt _ x y -> LtSequence y z is -> LtSequence x z (y :: is)

lemma LtSequenceConcat {A : Type} {x y z : YjsPtr A} {is1 is2 : List (YjsPtr A)} :
  LtSequence x y is1 -> LtSequence y z is2 -> LtSequence x z (is1 ++ is2) := by
    intro lt1
    induction lt1 with
    | base x =>
      intros lt2
      apply lt2
    | step1 x y z is _ lt1 lt2 ih =>
      intros lt
      apply LtSequence.step1 <;> try assumption
      apply ih
      assumption
    | step2 x y z is lt1 lt2 ih =>
      intros lt
      apply LtSequence.step2 <;> try assumption
      apply ih
      assumption

mutual
def YjsLtSequence (A : Type) : forall (x y : YjsPtr A) h, YjsLt h x y ->
  ∃ is : List (YjsPtr A), LtSequence x y is := by
    intros x y h
    apply Nat.strongRecOn' (P := fun h => ∀ x y, YjsLt h x y -> ∃ is : List (YjsPtr A), LtSequence x y is)
    intros h' ih x y lt
    match lt with
    | YjsLt.ltConflict h x y _ =>
      apply Exists.intro [y]
      apply LtSequence.step1 <;> try assumption
      apply LtSequence.base
    | YjsLt.ltOriginOrder x y _ =>
      apply Exists.intro [y]
      apply LtSequence.step2 <;> try assumption
      apply LtSequence.base
    | YjsLt.ltTrans h1 h2 _ z _  lt1 lt2 =>
      -- have h : lt1.height < (YjsLt.ltTrans x z _ lt1 lt2).height := by
      --   simp [YjsLt.height]
      --   omega
      have hlt1 : h1 < max h1 h2 + 1 := by
        omega
      match ih h1 hlt1 x z lt1 with
      | Exists.intro is1 lt1' =>
        -- have h : lt2.height < (YjsLt.ltTrans x z _ lt1 lt2).height := by
        --   simp [YjsLt.height]
        --   omega
        have hlt2 : h2 < max h1 h2 + 1 := by
          omega
        match ih h2 hlt2 z y lt2 with
        | Exists.intro is2 lt2 =>
          apply Exists.intro (is1 ++ is2)
          apply LtSequenceConcat <;> try assumption
end

lemma YjsInvariant A h (x y : YjsItem A) :
  @YjsLt A h x y -> ∃ h1, @YjsLeq A h1 x (y.origin) ∨ @YjsLeq A h1 (y.origin) (x.origin) := by
  sorry
