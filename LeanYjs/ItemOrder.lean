import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder

import Mathlib.Tactic.ApplyAt

mutual
inductive YjsLt {A : Type} : YjsPtr A -> YjsPtr A -> Type where
  | ltConflict i1 i2 : ConflictLt i1 i2 -> YjsLt i1 i2
  | ltOriginOrder i1 i2 : OriginLt _ i1 i2 -> YjsLt i1 i2
  | ltTrans x y z: YjsLt x y -> YjsLt y z -> YjsLt x z

inductive ConflictLt {A : Type} : YjsPtr A -> YjsPtr A -> Type where
  | ltOriginDiff : forall l1 l2 r1 r2 id1 id2 c1 c2,
    YjsLt l2 l1
    -> YjsLt (YjsItem.item l1 r1 id1 c1) r2
    -> YjsLt l1 (YjsItem.item l2 r2 id2 c2)
    -> YjsLt (YjsItem.item l2 r2 id2 c2) r1
    -> ConflictLt (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
  | ltOriginSame : forall l r1 r2 id1 id2 (c1 c2 : A),
    YjsLt (YjsItem.item l r1 id1 c1) r2
    -> YjsLt (YjsItem.item l r2 id2 c2) r1
    -> id1 < id2
    -> ConflictLt (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)
end

mutual
def YjsLt.height {A} {x y : YjsPtr A} : YjsLt x y -> Nat
  | YjsLt.ltConflict i1 i2 h => h.height
  | YjsLt.ltOriginOrder i1 i2 _ => 1
  | YjsLt.ltTrans x _ z lt1 lt2 => max (YjsLt.height lt1) (YjsLt.height lt2) + 1

def ConflictLt.height {A} {x y : YjsPtr A} : ConflictLt x y -> Nat
  | ConflictLt.ltOriginDiff l1 l2 r1 r2 id1 id2 c1 c2 h1 h2 h3 h4 =>
    max h1.height (max h2.height (max h3.height h4.height)) + 1
  | ConflictLt.ltOriginSame l r1 r2 id1 id2 c1 c2 h1 h2 h3 =>
    max h1.height h2.height + 1
end

inductive LtSequence {A : Type} : YjsPtr A -> YjsPtr A -> List (YjsPtr A) -> Prop where
  | base : forall x, LtSequence x x []
  | step1 : forall x y z is, ConflictLt x y -> LtSequence y z is -> LtSequence x z (y :: is)
  | step2 : forall x y z is, OriginLt _ x y -> LtSequence y z is -> LtSequence x z (y :: is)

lemma LtSequenceConcat {A : Type} {x y z : YjsPtr A} {is1 is2 : List (YjsPtr A)} :
  LtSequence x y is1 -> LtSequence y z is2 -> LtSequence x z (is1 ++ is2) := by
    intro lt1
    induction lt1 with
    | base x =>
      intros lt2
      apply lt2
    | step1 x y z is lt1 lt2 ih =>
      intros lt
      apply LtSequence.step1 <;> try assumption
      apply ih <;> assumption
    | step2 x y z is lt1 lt2 ih =>
      intros lt
      apply LtSequence.step2 <;> try assumption
      apply ih <;> assumption


def YjsLtSequence (A : Type) : forall (x y : YjsPtr A), YjsLt x y ->
  ∃ is : List (YjsPtr A), LtSequence x y is := fun x y lt =>
    match lt with
    | YjsLt.ltConflict x y _ => by
      apply Exists.intro [y]
      apply LtSequence.step1 <;> try assumption
      apply LtSequence.base
    | YjsLt.ltOriginOrder x y _ => by
      apply Exists.intro [y]
      apply LtSequence.step2 <;> try assumption
      apply LtSequence.base
    | YjsLt.ltTrans _ z _  lt1 lt2 =>
      have h : lt1.height < (YjsLt.ltTrans x z _ lt1 lt2).height := by
        simp [YjsLt.height]
        omega
      match YjsLtSequence A x z lt1 with
      | Exists.intro is1 lt1' =>
        have h : lt2.height < (YjsLt.ltTrans x z _ lt1 lt2).height := by
          simp [YjsLt.height]
          omega
        match YjsLtSequence A z y lt2 with
        | Exists.intro is2 lt2 => by
          apply Exists.intro (is1 ++ is2)
          apply LtSequenceConcat <;> try assumption
    termination_by x y lt => lt.height
