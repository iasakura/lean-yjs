import LeanYjs.ActorId
import LeanYjs.Item
import Mathlib.Order.Defs.Unbundled

open Relation

variable (A : Type) [BEq A]

inductive OriginLtStep : YjsPtr A -> YjsPtr A -> Prop where
  | lt_left : forall o r id c, OriginLtStep o (YjsItem.item o r id c)
  | lt_right : forall o r id c, OriginLtStep (YjsItem.item o r id c) r
  | lt_first : forall item, OriginLtStep YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, OriginLtStep (YjsPtr.itemPtr item) YjsPtr.last

inductive OriginReachableStep : YjsPtr A -> YjsPtr A -> Prop where
  | reachable : forall o r id c, OriginReachableStep (YjsItem.item o r id c) o
  | reachable_right : forall o r id c, OriginReachableStep (YjsItem.item o r id c) r

def OriginReachable := TransGen (r := OriginReachableStep A)

inductive OriginLt : YjsPtr A -> YjsPtr A -> Prop where
  | ltOrigin x y : OriginLtStep A x y -> OriginLt x y
  /-
    if t is reachable, then t isn't between o and r
    This means that (YjsItem.item o r id c) is neightbor of l and r at least when inserted.
  -/
  | ltReachableOrigin o r id c t :
    OriginReachable A (YjsItem.item o r id c) t ->
    OriginLt t r ->
    OriginLt t o
  | ltReachableRight o r id c t :
    OriginReachable A (YjsItem.item o r id c) t ->
    OriginLt o t ->
    OriginLt r t
  | ltTrans : forall x y z,
    OriginLt x y -> OriginLt y z -> OriginLt x z

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : YjsItem A -> Prop)

def YjsItemSubset := { i : YjsItem A // P i }

def YjsItemSubsetLt (x y : YjsItemSubset _ P) : Prop :=
  x = y ∨ OriginLt A (↑x.1) (↑y.1)

def ValidYjsSubsetPred :=
  (∀ (o : YjsItem A) r id c, P (YjsItem.item o r id c) -> P o) ∧
  (∀ o (r : YjsItem A) id c, P (YjsItem.item o r id c) -> P r) ∧
  IsPartialOrder (YjsItemSubset _ P ) (YjsItemSubsetLt _ _)
