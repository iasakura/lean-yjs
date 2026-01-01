import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId

import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Nat.Basic

def max4 (x y z w : Nat) : Nat :=
  max (max x y) (max z w)

inductive OriginLt {A} : YjsPtr A -> YjsPtr A -> Prop where
  | lt_first : forall item, OriginLt YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, OriginLt (YjsPtr.itemPtr item) YjsPtr.last
  | lt_first_last : OriginLt YjsPtr.first YjsPtr.last

inductive OriginReachableStep {A} : YjsPtr A -> YjsPtr A -> Prop where
  | reachable : forall o r id c d, OriginReachableStep (YjsItem.mk o r id c d) o
  | reachable_right : forall o r id c d, OriginReachableStep (YjsItem.mk o r id c d) r

inductive OriginReachable {A} : YjsPtr A -> YjsPtr A -> Prop where
  | reachable_single : forall x y, OriginReachableStep x y -> OriginReachable x y
  | reachable_head : forall x y z, OriginReachableStep x y -> OriginReachable y z -> OriginReachable x z

mutual
  inductive YjsLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltConflict h i1 i2 : ConflictLt h i1 i2 -> YjsLt (h + 1) i1 i2
    | ltOriginOrder i1 i2 : OriginLt i1 i2 -> YjsLt 0 i1 i2
    | ltOrigin h x o r id c d : YjsLeq h x o -> YjsLt (h + 1) x (YjsItem.mk o r id c d)
    | ltRightOrigin h o r id c d x : YjsLeq h r x -> YjsLt (h + 1) (YjsItem.mk o r id c d) x

  inductive YjsLeq {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | leqSame x : YjsLeq h x x
    | leqLt h x y : YjsLt h x y -> YjsLeq (h + 1) x y

  inductive ConflictLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 d1 d2 :
      YjsLt h1 l2 l1
      -> YjsLt h2 (YjsItem.mk l1 r1 id1 c1 d1) r2
      -> YjsLt h3 l1 (YjsItem.mk l2 r2 id2 c2 d2)
      -> YjsLt h4 (YjsItem.mk l2 r2 id2 c2 d2) r1
      -> ConflictLt (max4 h1 h2 h3 h4 + 1) (YjsItem.mk l1 r1 id1 c1 d1) (YjsItem.mk l2 r2 id2 c2 d2)
    | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) (d1 d2 : Bool) :
      YjsLt h1 (YjsItem.mk l r1 id1 c1 d1) r2
      -> YjsLt h2 (YjsItem.mk l r2 id2 c2 d2) r1
      -> id1 < id2
      -> ConflictLt (max h1 h2 + 1) (YjsItem.mk l r1 id1 c1 d1) (YjsItem.mk l r2 id2 c2 d2)
end

def ConflictLt' {A} (i1 i2 : YjsPtr A) : Prop :=
  ∃ h, ConflictLt h i1 i2

def YjsLt' {A} (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLt A h x y

def YjsLeq' {A} (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLeq A h x y

theorem ConflictLt'.ltOriginDiff {A : Type} (l1 l2 r1 r2 : YjsPtr A) (id1 id2 : YjsId) (c1 c2 : A) :
  YjsLt' l2 l1
  -> YjsLt' (YjsItem.mk l1 r1 id1 c1 d1) r2
  -> YjsLt' l1 (YjsItem.mk l2 r2 id2 c2 d2)
  -> YjsLt' (YjsItem.mk l2 r2 id2 c2 d2) r1
  -> ConflictLt' (A := A) (YjsItem.mk l1 r1 id1 c1 d1) (YjsItem.mk l2 r2 id2 c2 d2) := by
  intros hlt1 hlt2 hlt3 hlt4
  obtain ⟨ h1, hlt1 ⟩ := hlt1
  obtain ⟨ h2, hlt2 ⟩ := hlt2
  obtain ⟨ h3, hlt3 ⟩ := hlt3
  obtain ⟨ h4, hlt4 ⟩ := hlt4
  constructor
  apply ConflictLt.ltOriginDiff <;> try assumption

theorem ConflictLt'.ltOriginSame {A : Type} (l r1 r2 : YjsPtr A) (id1 id2 : YjsId) (c1 c2 : A) (d1 d2 : Bool) :
  YjsLt' (YjsItem.mk l r1 id1 c1 d1) r2
  -> YjsLt' (YjsItem.mk l r2 id2 c2 d2) r1
  -> id1 < id2
  -> ConflictLt' (A := A) (YjsItem.mk l r1 id1 c1 d1) (YjsItem.mk l r2 id2 c2 d2) := by
  intros hlt1 hlt2 hlt3
  obtain ⟨ h1, hlt1 ⟩ := hlt1
  obtain ⟨ h2, hlt2 ⟩ := hlt2
  constructor
  apply ConflictLt.ltOriginSame <;> try assumption

theorem YjsLt'.ltConflict {A : Type} (i1 i2 : YjsPtr A) : ConflictLt' i1 i2 -> YjsLt' i1 i2 := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  constructor
  apply YjsLt.ltConflict
  assumption

theorem YjsLt'.ltOriginOrder {A : Type} (i1 i2 : YjsPtr A) : OriginLt i1 i2 -> YjsLt' i1 i2 := by
  intros hor
  constructor
  apply YjsLt.ltOriginOrder; assumption

theorem YjsLt'.ltOrigin {A : Type} (x o r : YjsPtr A) id c d : YjsLeq' x o -> YjsLt' x (YjsItem.mk o r id c d) := by
  intros hleq
  obtain ⟨ h, hleq ⟩ := hleq
  constructor
  apply YjsLt.ltOrigin <;> try assumption

theorem YjsLt'.ltRightOrigin {A : Type} (o r : YjsPtr A) id c d x : YjsLeq' r x -> YjsLt' (YjsItem.mk o r id c d) x := by
  intros hleq
  obtain ⟨ h, hleq ⟩ := hleq
  constructor
  apply YjsLt.ltRightOrigin <;> try assumption

theorem YjsLeq'.leqSame {A : Type} (x : YjsPtr A) : YjsLeq' x x := by
  exists 0
  apply YjsLeq.leqSame

theorem YjsLeq'.leqLt {A : Type} (x y : YjsPtr A) : YjsLt' x y -> YjsLeq' x y := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  exists h + 1
  apply YjsLeq.leqLt
  assumption

def yjs_leq'_imp_eq_or_yjs_lt' {A : Type} {x y : YjsPtr A} :
  YjsLeq' x y -> x = y ∨ YjsLt' x y := by
    intros hleq
    obtain ⟨ h, hleq ⟩ := hleq
    cases hleq with
    | leqSame _ => left; rfl
    | leqLt _ _ _ hlt => right; constructor; assumption

theorem yjs_lt_cases A h (x y : YjsPtr A) :
  YjsLt h x y ->
    (x = YjsPtr.first ∧ (y = YjsPtr.last ∨ ∃ i, y = YjsPtr.itemPtr i)) ∨
    (y = YjsPtr.last ∧ (x = YjsPtr.first ∨ ∃ i, x = YjsPtr.itemPtr i)) ∨
    (∃ x', x = YjsPtr.itemPtr x' ∧ YjsLeq' x'.rightOrigin y) ∨
    (∃ y', y = YjsPtr.itemPtr y' ∧ YjsLeq' x y'.origin) ∨
    ConflictLt' x y := by
  intros hlt
  cases hlt with
  | ltConflict h x y hlt =>
    right; right; right; right
    apply Exists.intro h; assumption
  | ltOriginOrder x y hlt =>
    cases hlt with
    | lt_first_last =>
      left; simp
    | lt_first =>
      left; simp
    | lt_last =>
      right; left; simp
  | ltOrigin h x o r id c d hlt =>
    right; right; right; left; simp
    constructor; assumption
  | ltRightOrigin h o r id c d x hlt =>
    right; right; left; simp
    constructor; assumption

theorem yjs_lt'_cases A (x y : YjsPtr A) :
  YjsLt' x y ->
    (x = YjsPtr.first ∧ (y = YjsPtr.last ∨ ∃ i, y = YjsPtr.itemPtr i)) ∨
    (y = YjsPtr.last ∧ (x = YjsPtr.first ∨ ∃ i, x = YjsPtr.itemPtr i)) ∨
    (∃ x', x = YjsPtr.itemPtr x' ∧ YjsLeq' x'.rightOrigin y) ∨
    (∃ y', y = YjsPtr.itemPtr y' ∧ YjsLeq' x y'.origin) ∨
    ConflictLt' x y := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  apply yjs_lt_cases A h x y hlt
