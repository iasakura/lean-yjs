import LeanYjs.ActorId
import LeanYjs.Item
import Mathlib.Order.Defs.Unbundled

open Relation

variable (A : Type) [BEq A]

def IsItemClosed (P : YjsPtr A -> Prop) : Prop :=
  P YjsPtr.first ∧
  P YjsPtr.last ∧
  (∀ (o : YjsPtr A) r id c, P (YjsItem.item o r id c) -> P o) ∧
  (∀ o (r : YjsPtr A) id c, P (YjsItem.item o r id c) -> P r)

def ClosedPredicate := { P : YjsPtr A -> Prop // IsItemClosed A P }

inductive OriginLtStep : YjsPtr A -> YjsPtr A -> Prop where
  | lt_left : forall o r id c, OriginLtStep o (YjsItem.item o r id c)
  | lt_right : forall o r id c, OriginLtStep (YjsItem.item o r id c) r
  | lt_first : forall item, OriginLtStep YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, OriginLtStep (YjsPtr.itemPtr item) YjsPtr.last
  | lt_first_last : OriginLtStep YjsPtr.first YjsPtr.last

inductive OriginReachableStep : YjsPtr A -> YjsPtr A -> Prop where
  | reachable : forall o r id c, OriginReachableStep (YjsItem.item o r id c) o
  | reachable_right : forall o r id c, OriginReachableStep (YjsItem.item o r id c) r

def OriginReachable := TransGen (r := @OriginReachableStep A)

inductive OriginLt (P : @ClosedPredicate A): YjsPtr A -> YjsPtr A -> Prop where
  | ltOrigin x y : P.val x -> P.val y -> OriginLtStep A x y -> OriginLt P x y
  /-
    if t is reachable, then t isn't between o and r
    This means that (YjsItem.item o r id c) is neightbor of l and r at least when inserted.
  -/
  | ltReachableOrigin o r id c t :
    P.val o -> P.val r -> P.val t ->
    @OriginReachable A (YjsItem.item o r id c) t ->
    OriginLt P t r ->
    OriginLt P t o
  | ltReachableRight o r id c t :
    P.val o -> P.val r -> P.val t ->
    @OriginReachable A (YjsItem.item o r id c) t ->
    OriginLt P o t ->
    OriginLt P r t
  | ltTrans : forall x y z,
    P.val x -> P.val y -> P.val z ->
    OriginLt P x y -> OriginLt P y z -> OriginLt P x z

lemma origin_lt_p1 {A} {P : @ClosedPredicate A} {x y : YjsPtr A} (h : OriginLt _ P x y) : P.val x := by
  cases h with
  | ltOrigin x y hpx hpy hlt =>
    assumption
  | ltReachableOrigin o r id c t ho hr ht hreach hlt =>
    assumption
  | ltReachableRight o r id c t ho hr ht hreach hlt =>
    assumption
  | ltTrans x y z hx hy hz hlt1 hlt2 =>
    assumption

lemma origin_lt_p2 {A} {P : @ClosedPredicate A} {x y : YjsPtr A} (h : OriginLt _ P x y) : P.val y := by
  cases h with
  | ltOrigin  y hpx hpy hlt
    assumption
  | ltReachableOrigin o r id c t ho hr ht hreach hlt =>
    assumption
  | ltReachableRight o r id c t ho hr ht hreach hlt =>
    assumption
  | ltTrans x y z hx hy hz hlt1 hlt2 =>
    assumption
