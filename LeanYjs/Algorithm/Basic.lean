import LeanYjs.Item
import Std.Data.ExtTreeSet

inductive IntegrateError where
| error : IntegrateError

instance : Ord ClientId := inferInstanceAs (Ord Nat)
instance : Std.TransOrd ClientId := inferInstanceAs (Std.TransOrd Nat)
instance : Std.LawfulEqOrd ClientId := inferInstanceAs (Std.LawfulEqOrd Nat)

abbrev YjsIdCmp : YjsId → YjsId → Ordering :=
  compareLex (compareOn YjsId.clientId) (compareOn YjsId.clock)

instance : Std.LawfulEqCmp YjsIdCmp where
  eq_of_compare := by
    intro a b h
    cases a with
    | mk aClient aClock =>
      cases b with
      | mk bClient bClock =>
        simp [YjsIdCmp, compareLex_eq_eq, compareOn] at h
        rcases h with ⟨hClient, hClock⟩
        subst hClient
        subst hClock
        rfl

abbrev DeletedIdSet := Std.ExtTreeSet YjsId YjsIdCmp

structure YjsState (A : Type) where
  items : Array (YjsItem A)
  deletedIds : DeletedIdSet

instance : Coe (YjsState A) (Array (YjsItem A)) where
  coe state := state.items

instance : Coe (Array (YjsItem A)) (YjsState A) where
  coe items := { items := items, deletedIds := ∅ }

@[simp] theorem coeArrayToState_items (items : Array (YjsItem A)) :
    ((items : YjsState A)).items = items := rfl

@[simp] theorem coeArrayToState_deletedIds (items : Array (YjsItem A)) :
    ((items : YjsState A)).deletedIds = ∅ := rfl

instance : Coe (Except IntegrateError (YjsState A)) (Except IntegrateError (Array (YjsItem A))) where
  coe state := state.map YjsState.items

namespace YjsState

def empty : YjsState A := {
  items := #[]
  deletedIds := ∅
}

def toList (state : YjsState A) : List (YjsItem A) :=
  state.items.toList

def find? (state : YjsState A) (p : YjsItem A → Bool) : Option (YjsItem A) :=
  state.items.find? p

def addDeletedId (state : YjsState A) (id : YjsId) : YjsState A :=
  { state with deletedIds := state.deletedIds.insert id }

end YjsState

def YjsEmptyState {A} : YjsState A :=
  YjsState.empty
