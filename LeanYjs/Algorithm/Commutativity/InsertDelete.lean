import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Delete.Basic

theorem integrateSafe_deleteById_commutative [DecidableEq A] {newItem : IntegrateInput A} {arr : YjsState A} {id : YjsId}:
  (do
    let newArr <- arr.insert newItem
    Except.ok (deleteById newArr id)) = ((deleteById arr id).insert newItem) := by
  sorry
