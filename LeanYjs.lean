-- This module serves as the root of the `LeanYjs` library.
-- Import modules here that should be built as part of the library.
import LeanYjs.Basic

def ActorId := Nat

instance : LT ActorId where
  lt x y := Nat.lt x y

inductive YjsItem (A : Type): Type where
| item: (origin: YjsItem A) -> (rightOrigin: YjsItem A) -> ActorId -> A -> YjsItem A
| first: YjsItem A
| last: YjsItem A

def YjsItem.origin {A : Type}: YjsItem A -> Option (YjsItem A)
| YjsItem.item origin _  _ _ => origin
| _ => none

def YjsItem.rightOrigin {A : Type}: YjsItem A -> Option (YjsItem A)
| YjsItem.item _ rightOrigin _ _ => rightOrigin
| _ => none

inductive YjsLessThan1 (A : Type): YjsItem A -> YjsItem A -> Prop where
| ltFirst: forall (left right: YjsItem A) (c: A), YjsLessThan1 A YjsItem.first (YjsItem.item left right _ c)
| ltLast: forall (left right: YjsItem A) (c: A), YjsLessThan1 A (YjsItem.item left right _ c) YjsItem.last
| ltOrigin: forall (item right: YjsItem A) (id: ActorId) (c: A), YjsLessThan1 A item (YjsItem.item item right id c)
| ltRightOrigin: forall (item left: YjsItem A) (id: ActorId) (c: A), YjsLessThan1 A (YjsItem.item left item id c) item

/- transitive closure -/
inductive YjsLessThanTr {a : Type}: YjsItem a -> YjsItem a -> Prop where
| base: forall (item1 item2: YjsItem a), YjsLessThan1 a item1 item2 -> YjsLessThanTr item1 item
| trans: forall (item1 item2 item3: YjsItem a), YjsLessThanTr item1 item2 -> YjsLessThan1 a item2 item3 -> YjsLessThanTr item1 item3

inductive YjsLessThan {a : Type}: YjsItem a -> YjsItem a -> Prop where
| ltOrigin: forall item1 item2, YjsLessThanTr item1 item2 -> YjsLessThan item1 item2
| ltTr: forall item1 item2 item3, YjsLessThanTr item1 item2 -> YjsLessThanTr item2 item3 -> YjsLessThan item1 item3
| lt1: forall (left1 left2 right1 right2: YjsItem a) (id1 id2: ActorId) (c1 c2: a),
    item1 = YjsItem.item left1 right1 id1 c1
    -> item2 = YjsItem.item left2 right2 id2 c2
    /- left1 < item2 < right1 -/
    -> YjsLessThanTr left1 item2 -> YjsLessThanTr item2 right1
    /- left1 < left2 -/
    -> YjsLessThanTr left1 left2
    /- left2 < item1 -/
    -> YjsLessThan left2 item1
    -> YjsLessThan item2 item1
| lt2: forall (left1 left2 right1 right2: YjsItem a) (id1 id2: ActorId) (c1 c2: a),
    item1 = YjsItem.item left1 right1 id1 c1
    -> item2 = YjsItem.item left2 right2 id2 c2
    /- left1 < item2 < right1 -/
    -> YjsLessThanTr left1 item2 -> YjsLessThanTr item2 right1
    /- left2 < left1 -/
    -> YjsLessThanTr left2 left1
    -> YjsLessThan item1 item2
| ltSame1: forall (left right: YjsItem a) (id1 id2: ActorId) (c1 c2: a),
    item1 = YjsItem.item left right id1 c1
    -> item2 = YjsItem.item left right id2 c2
    -> id1 < id2
    -> YjsLessThan item1 item2
| ltSame2: forall (left right: YjsItem a) (id1 id2: ActorId) (c1 c2: a),
    item1 = YjsItem.item left right id1 c1
    -> item2 = YjsItem.item left right id2 c2
    -> id2 < id1
    -> YjsLessThan item2 item1
/- ????????????????????? -/
| ltSame3: forall (left right1 right2: YjsItem a) (id1 id2: ActorId) (c1 c2: a),
    item1 = YjsItem.item left right id1 c1
    -> item2 = YjsItem.item left right id2 c2
    /- item2 < right1 -/
    -> YjsLessThan item2 right1
    -> YjsLessThan item1 right2

    -> YjsLessThan item1 item2


#check YjsLessThan.lt1
