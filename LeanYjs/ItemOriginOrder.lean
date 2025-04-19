import LeanYjs.ActorId
import LeanYjs.Item
import Mathlib.Order.Defs.Unbundled

open Relation

variable (A : Type) [BEq A]

inductive YjsPtrLtOrigin : YjsPtr A -> YjsPtr A -> Prop where
  | lt_left : forall o r id c, YjsPtrLtOrigin o (YjsItem.item o r id c)
  | lt_right : forall o r id c, YjsPtrLtOrigin (YjsItem.item o r id c) r
  | lt_first : forall item, YjsPtrLtOrigin YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, YjsPtrLtOrigin (YjsPtr.itemPtr item) YjsPtr.last

inductive YjsReanchableOne : YjsPtr A -> YjsPtr A -> Prop where
  | reachable : forall o r id c, YjsReanchableOne (YjsItem.item o r id c) o
  | reachable_right : forall o r id c, YjsReanchableOne (YjsItem.item o r id c) r

def YjsReanchable := TransGen (r := YjsReanchableOne A)

inductive YjsPtrLt2 : YjsPtr A -> YjsPtr A -> Prop where
  | lt_origin x y : YjsPtrLtOrigin A x y -> YjsPtrLt2 x y
  /-
    if t is reachable, then t isn't between o and r
    This means that (YjsItem.item o r id c) is neightbor of l and r at least when inserted.
  -/
  | lt_reachable1 o r id c t :
    YjsReanchable A (YjsItem.item o r id c) t ->
    YjsPtrLt2 t r ->
    YjsPtrLt2 t o
  | lt_reachable2 o r id c t :
    YjsReanchable A (YjsItem.item o r id c) t ->
    YjsPtrLt2 o t ->
    YjsPtrLt2 r t
  | lt_trans : forall x y z,
    YjsPtrLt2 x y -> YjsPtrLt2 y z -> YjsPtrLt2 x z

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : YjsItem A -> Prop)

def YjsItemSubset := { i : YjsItem A // P i }

def YjsItemSubsetLeq (x y : YjsItemSubset _ P) : Prop :=
  x = y ∨ YjsPtrLt2 A (↑x.1) (↑y.1)

def ValidYjsSubsetPred :=
  (∀ (o : YjsItem A) r id c, P (YjsItem.item o r id c) -> P o) ∧
  (∀ o (r : YjsItem A) id c, P (YjsItem.item o r id c) -> P r) ∧
  IsPartialOrder (YjsItemSubset _ P ) (YjsItemSubsetLeq _ _)

