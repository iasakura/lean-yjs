import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Delete.Basic

theorem integrateSafe_deleteById_commutative [DecidableEq A] {newItem : IntegrateInput A} {arr : Array (YjsItem A)} {id : YjsId}:
  (do
    let newArr <- integrateSafe newItem arr
    Except.ok (deleteById newArr id)) = (deleteById arr id |> integrateSafe newItem) := by
  sorry
