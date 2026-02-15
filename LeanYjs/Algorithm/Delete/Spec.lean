import LeanYjs.Algorithm.Delete.Basic
import LeanYjs.Algorithm.Invariant.Basic
import LeanYjs.Algorithm.Invariant.YjsArray

theorem YjsStateInvariant_deleteById (state : YjsState A) (id : YjsId) :
  YjsStateInvariant state →
  YjsStateInvariant (deleteById state id) := by
  simp [YjsStateInvariant, deleteById]
