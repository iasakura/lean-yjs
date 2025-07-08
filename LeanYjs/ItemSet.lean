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

theorem IsClosedItemSet.eq_set {A} (P Q : YjsPtr A -> Prop) :
  IsClosedItemSet P ->
  (∀ x, P x ↔ Q x) ->
  IsClosedItemSet Q := by
  intro hP hPQ
  constructor
  . rw [<-hPQ]
    apply hP.baseFirst
  . rw [<-hPQ]
    apply hP.baseLast
  . intros o r id c hp
    rw [<-hPQ] at *
    apply hP.closedLeft <;> assumption
  . intros o r id c hp
    rw [<-hPQ] at *
    apply hP.closedRight <;> assumption
