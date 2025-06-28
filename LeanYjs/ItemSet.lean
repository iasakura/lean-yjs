import LeanYjs.Item
import LeanYjs.ActorId

import Mathlib.Data.Set.Basic

variable (A : Type) [BEq A]

def ItemSet := Set (YjsPtr A)

structure IsClosedItemSet {A} (P : YjsPtr A -> Prop) : Prop where
  baseFirst : P YjsPtr.first
  baseLast : P YjsPtr.last
  closedLeft : (∀ (o : YjsPtr A) r id c, P (YjsItem.item o r id c) -> P o)
  closedRight : (∀ o (r : YjsPtr A) id c, P (YjsItem.item o r id c) -> P r)
