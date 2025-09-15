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
  | reachable : forall o r id c, OriginReachableStep (YjsItem.item o r id c) o
  | reachable_right : forall o r id c, OriginReachableStep (YjsItem.item o r id c) r

inductive OriginReachable {A} : YjsPtr A -> YjsPtr A -> Prop where
  | reachable_single : forall x y, OriginReachableStep x y -> OriginReachable x y
  | reachable_head : forall x y z, OriginReachableStep x y -> OriginReachable y z -> OriginReachable x z

mutual
  inductive YjsLt {A : Type} (P : ItemSet A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltConflict h i1 i2 : ConflictLt P h i1 i2 -> YjsLt P (h + 1) i1 i2
    | ltOriginOrder i1 i2 : P i1 -> P i2 -> OriginLt i1 i2 -> YjsLt P 0 i1 i2
    | ltOrigin h x o r id c : P (YjsItem.item o r id c) -> YjsLeq P h x o -> YjsLt P (h + 1) x (YjsItem.item o r id c)
    | ltRightOrigin h o r id c x : P (YjsItem.item o r id c) -> YjsLeq P h r x -> YjsLt P (h + 1) (YjsItem.item o r id c) x

  inductive YjsLeq {A : Type} (P : ItemSet A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | leqSame x : P x -> YjsLeq P h x x
    | leqLt h x y : YjsLt P h x y -> YjsLeq P (h + 1) x y

  inductive ConflictLt {A : Type} (P : ItemSet A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
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

def ConflictLt' {A} (P : ItemSet A) (i1 i2 : YjsPtr A) : Prop :=
  ∃ h, ConflictLt P h i1 i2

def YjsLt' {A} (P : ItemSet A) (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLt A P h x y

def YjsLeq' {A} (P : ItemSet A) (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLeq A P h x y

theorem ConflictLt'.ltOriginDiff {A : Type} (P : ItemSet A) l1 l2 r1 r2 id1 id2 c1 c2 :
  YjsLt' P l2 l1
  -> YjsLt' P (YjsItem.item l1 r1 id1 c1) r2
  -> YjsLt' P l1 (YjsItem.item l2 r2 id2 c2)
  -> YjsLt' P (YjsItem.item l2 r2 id2 c2) r1
  -> ConflictLt' P (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2) := by
  intros hlt1 hlt2 hlt3 hlt4
  obtain ⟨ h1, hlt1 ⟩ := hlt1
  obtain ⟨ h2, hlt2 ⟩ := hlt2
  obtain ⟨ h3, hlt3 ⟩ := hlt3
  obtain ⟨ h4, hlt4 ⟩ := hlt4
  constructor
  apply ConflictLt.ltOriginDiff <;> try assumption

theorem ConflictLt'.ltOriginSame {A : Type} (P : ItemSet A) l r1 r2 id1 id2 c1 c2 :
  YjsLt' P (YjsItem.item l r1 id1 c1) r2
  -> YjsLt' P (YjsItem.item l r2 id2 c2) r1
  -> id1 < id2
  -> ConflictLt' P (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2) := by
  intros hlt1 hlt2 hlt3
  obtain ⟨ h1, hlt1 ⟩ := hlt1
  obtain ⟨ h2, hlt2 ⟩ := hlt2
  constructor
  apply ConflictLt.ltOriginSame <;> try assumption

theorem YjsLt'.ltConflict {A : Type} (P : ItemSet A) i1 i2 : ConflictLt' P i1 i2 -> YjsLt' P i1 i2 := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  constructor
  apply YjsLt.ltConflict
  assumption

theorem YjsLt'.ltOriginOrder {A : Type} (P : ItemSet A) i1 i2 : P i1 -> P i2 -> OriginLt i1 i2 -> YjsLt' P i1 i2 := by
  intros hpi1 hpi2 hor
  constructor
  apply YjsLt.ltOriginOrder <;> try assumption

theorem YjsLt'.ltOrigin {A : Type} (P : ItemSet A) x o r id c : P (YjsItem.item o r id c) -> YjsLeq' P x o -> YjsLt' P x (YjsItem.item o r id c) := by
  intros hpi hleq
  obtain ⟨ h, hleq ⟩ := hleq
  constructor
  apply YjsLt.ltOrigin <;> try assumption

theorem YjsLt'.ltRightOrigin {A : Type} (P : ItemSet A) o r id c x : P (YjsItem.item o r id c) -> YjsLeq' P r x -> YjsLt' P (YjsItem.item o r id c) x := by
  intros hpi hleq
  obtain ⟨ h, hleq ⟩ := hleq
  constructor
  apply YjsLt.ltRightOrigin <;> try assumption

theorem YjsLeq'.leqSame {A : Type} (P : ItemSet A) x : P x -> YjsLeq' P x x := by
  intros hpx
  exists 0
  apply YjsLeq.leqSame
  assumption

theorem YjsLeq'.leqLt {A : Type} (P : ItemSet A) x y : YjsLt' P x y -> YjsLeq' P x y := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  exists h + 1
  apply YjsLeq.leqLt
  assumption

theorem yjs_lt_p1_aux {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  (YjsLt P h x y -> P x) ∧ (ConflictLt P h x y -> P x) ∧ (YjsLeq P h x y -> P x) := by
    apply Nat.strongRecOn' (P := fun h => ∀ x y, (YjsLt P h x y -> P x) ∧ (ConflictLt P h x y -> P x) ∧ (YjsLeq P h x y -> P x))
    intros n ih x y
    constructor
    . intro hlt
      cases hlt with
      | ltConflict h x y hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, h, _ ⟩ := ih h hlt_h x y
        apply h ; assumption
      | ltOriginOrder x y _ =>
        assumption
      | ltOrigin h x o r id c hval hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, _, ih ⟩ := ih h hlt_h x o
        apply ih; assumption
      | ltRightOrigin h o r id c x hval hlt =>
        assumption
    . constructor
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
      . intros hlt
        cases hlt with
        | leqSame hpx x =>
          assumption
        | leqLt h x y hlt =>
          obtain ⟨ ih, _, _ ⟩ := ih h (by omega) x y
          apply ih; assumption

@[simp] theorem yjs_lt_p1 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLt P h x y -> P x := by
    intros x y hlt
    let ⟨ h, _ ⟩ := @yjs_lt_p1_aux A P h x y
    tauto

theorem yjs_lt'_p1 {A : Type} {P : @ItemSet A} : forall {x y : YjsPtr A},
  YjsLt' P x y -> P x := by
    intros x y hlt
    obtain ⟨ h, hlt ⟩ := hlt
    apply yjs_lt_p1; assumption

theorem conflict_lt_p1 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  ConflictLt P h x y -> P x := by
    intros x y hlt
    let ⟨ _, h ⟩ := @yjs_lt_p1_aux A P h x y
    tauto

theorem yjs_lt_p2_aux {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  (YjsLt P h x y -> P y) ∧ (ConflictLt P h x y -> P y) ∧ (YjsLeq P h x y -> P y) := by
    apply Nat.strongRecOn' (P := fun h => ∀ x y, (YjsLt P h x y -> P y) ∧ (ConflictLt P h x y -> P y) ∧ (YjsLeq P h x y -> P y))
    intros n ih x y
    constructor
    . intro hlt
      cases hlt with
      | ltConflict h x y hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, h, _ ⟩ := ih h hlt_h x y
        apply h ; assumption
      | ltOriginOrder x y _ =>
        assumption
      | ltOrigin h x o r id c hval hlt =>
        assumption
      | ltRightOrigin h o r id c x hval hlt =>
        have hlt_h : h < h + 1 := by
          omega
        let ⟨ _, _, ih ⟩ := ih h hlt_h r y
        apply ih; assumption
    . constructor
      . intro hlt
        cases hlt with
        | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
          have hlt_h : h3 < max4 h1 h2 h3 h4 + 1 := by
            unfold max4
            omega
          let ⟨ ih, _ ⟩ := ih h3 hlt_h l1 (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2))
          apply ih hlt3
        | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
          apply yjs_lt_p1; assumption
      . intros hlt
        cases hlt with
        | leqSame hpx x =>
          assumption
        | leqLt h x y hlt =>
          obtain ⟨ ih, _, _ ⟩ := ih h (by omega) x y
          apply ih; assumption

theorem yjs_lt_p2 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLt P h x y -> P y := by
    intros x y hlt
    let ⟨ h, _ ⟩ := @yjs_lt_p2_aux A P h x y
    tauto

theorem yjs_lt'_p2 {A : Type} {P : @ItemSet A} : forall {x y : YjsPtr A},
  YjsLt' P x y -> P y := by
    intros x y hlt
    obtain ⟨ h, hlt ⟩ := hlt
    apply yjs_lt_p2; assumption

theorem conflict_lt_p2 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  ConflictLt P h x y -> P y := by
    intros x y hlt
    let ⟨ _, h ⟩ := @yjs_lt_p2_aux A P h x y
    tauto

theorem yjs_leq_p1 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLeq P h x y -> P y -> P x := by
    intros x y hleq hpy
    cases hleq with
    | leqSame => assumption
    | leqLt _ _ _  hlt => apply yjs_lt_p1 hlt

theorem yjs_leq_p2 {A : Type} {P : @ItemSet A} {h : Nat} : forall {x y : YjsPtr A},
  YjsLeq P h x y -> P x -> P y := by
    intros x y hleq hpy
    cases hleq with
    | leqSame => assumption
    | leqLt _ _ _ hlt => apply yjs_lt_p2 hlt

def yjs_leq'_imp_eq_or_yjs_lt' {A : Type} {P : @ItemSet A} {x y : YjsPtr A} :
  YjsLeq' P x y -> x = y ∨ YjsLt' P x y := by
    intros hleq
    obtain ⟨ h, hleq ⟩ := hleq
    cases hleq with
    | leqSame _ => left; rfl
    | leqLt _ _ _ hlt => right; constructor; assumption

theorem yjs_leq'_p1 {A : Type} {P : @ItemSet A} : forall {x y : YjsPtr A},
  YjsLeq' P x y -> P y -> P x := by
    intros x y hleq hpy
    obtain ⟨ h, hleq ⟩ := hleq
    apply yjs_leq_p1 hleq hpy

theorem yjs_leq'_p2 {A : Type} {P : @ItemSet A} : forall {x y : YjsPtr A},
  YjsLeq' P x y -> P x -> P y := by
    intros x y hleq hpy
    obtain ⟨ h, hleq ⟩ := hleq
    apply yjs_leq_p2 hleq hpy

theorem yjs_lt_cases A P h (x y : YjsPtr A) :
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
    | lt_first_last =>
      left; simp
    | lt_first =>
      left; simp
    | lt_last =>
      right; left; simp
  | ltOrigin h x o r id c hval hlt =>
    right; right; right; left; simp
    constructor; assumption
  | ltRightOrigin h o r id c x hval hlt =>
    right; right; left; simp
    constructor; assumption

theorem yjs_lt'_cases A P (x y : YjsPtr A) :
  YjsLt' P x y ->
    (x = YjsPtr.first ∧ (y = YjsPtr.last ∨ ∃ i, y = YjsPtr.itemPtr i)) ∨
    (y = YjsPtr.last ∧ (x = YjsPtr.first ∨ ∃ i, x = YjsPtr.itemPtr i)) ∨
    (∃ x', x = YjsPtr.itemPtr x' ∧ YjsLeq' P x'.rightOrigin y) ∨
    (∃ y', y = YjsPtr.itemPtr y' ∧ YjsLeq' P x y'.origin) ∨
    ConflictLt' P x y := by
  intros hlt
  obtain ⟨ h, hlt ⟩ := hlt
  apply yjs_lt_cases A P h x y hlt

-- inductive LtSequence {A : Type} (P : @ItemSet A) : YjsPtr A -> YjsPtr A -> List (YjsPtr A) -> Prop where
--   | base : forall x, LtSequence P x x []
--   | step1 : forall x y z is h, ConflictLt P h x y -> LtSequence P y z is -> LtSequence P x z (y :: is)
--   | step2 : forall x y z is, OriginLt _ x y -> LtSequence P y z is -> LtSequence P x z (y :: is)

-- theorem LtSequenceConcat {A : Type} {P : @ItemSet A} {x y z : YjsPtr A} {is1 is2 : List (YjsPtr A)} :
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

-- theorem YjsLtSequence (A : Type) (P : ItemSet A): forall (x y : YjsPtr A) h, YjsLt P h x y ->
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
