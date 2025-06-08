import LeanYjs.Item
import LeanYjs.ItemOriginOrder
import LeanYjs.ActorId

import Mathlib.Tactic.Set

variable (A : Type) [BEq A]

structure IsClosedItemPredicate (P : YjsPtr A -> Prop) : Prop where
  baseFirst : P YjsPtr.first
  baseLast : P YjsPtr.last
  closedLeft : (∀ (o : YjsPtr A) r id c, P (YjsItem.item o r id c) -> P o)
  closedRight : (∀ o (r : YjsPtr A) id c, P (YjsItem.item o r id c) -> P r)

def ClosedPredicate := { P : YjsPtr A -> Prop // IsClosedItemPredicate A P }

def ItemSet (P : ClosedPredicate A) := { i : YjsPtr A // P.val i }
