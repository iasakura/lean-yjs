import LeanYjs.Algorithm.Delete.Basic
import Std.Data.ExtTreeSet.Basic

theorem deleteById_commutative (state : YjsState A) (id1 id2 : YjsId) :
  deleteById (deleteById state id1) id2 = deleteById (deleteById state id2) id1 := by
  obtain ⟨ items, deletedIds ⟩ := state
  simp [deleteById]
  rw [Std.ExtTreeSet.ext_mem_iff]; simp
  grind
