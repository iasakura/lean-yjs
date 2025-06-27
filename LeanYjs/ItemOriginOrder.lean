import LeanYjs.ActorId
import LeanYjs.Item
import Mathlib.Order.Defs.Unbundled

open Relation

variable (A : Type) [BEq A]
inductive OriginLt : YjsPtr A -> YjsPtr A -> Prop where
  | lt_left : forall o r id c, OriginLt o (YjsItem.item o r id c)
  | lt_right : forall o r id c, OriginLt (YjsItem.item o r id c) r
  | lt_first : forall item, OriginLt YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, OriginLt (YjsPtr.itemPtr item) YjsPtr.last
  | lt_first_last : OriginLt YjsPtr.first YjsPtr.last

def OriginLeq (x y : YjsPtr A) : Prop :=
  x = y ∨ OriginLt A x y

inductive OriginReachableStep : YjsPtr A -> YjsPtr A -> Prop where
  | reachable : forall o r id c, OriginReachableStep (YjsItem.item o r id c) o
  | reachable_right : forall o r id c, OriginReachableStep (YjsItem.item o r id c) r

def OriginReachable := TransGen (r := @OriginReachableStep A)

-- inductive OriginLt (P : @ItemSet A): YjsPtr A -> YjsPtr A -> Prop where
--   | ltOrigin x y : P.val x -> P.val y -> OriginLtStep A x y -> OriginLt P x y
--   /-
--     if t is reachable, then t isn't between o and r
--     This means that (YjsItem.item o r id c) is neightbor of l and r at least when inserted.
--   -/
--   -- | ltReachableOrigin o r id c t :
--   --   P.val o -> P.val r -> P.val t ->
--   --   @OriginReachable A (YjsItem.item o r id c) t ->
--   --   OriginLt P t r ->
--   --   OriginLt P t o
--   -- | ltReachableRight o r id c t :
--   --   P.val o -> P.val r -> P.val t ->
--   --   @OriginReachable A (YjsItem.item o r id c) t ->
--   --   OriginLt P o t ->
--   --   OriginLt P r t
--   | ltTrans : forall x y z,
--     P.val x -> P.val y -> P.val z ->
--     OriginReachable A x y -> OriginReachable A z y ->
--     OriginLt P x y -> OriginLt P y z -> OriginLt P x z
