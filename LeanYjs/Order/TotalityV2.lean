import LeanYjs.ClientId
import LeanYjs.Order.MeasureV2

variable {A : Type}

theorem YjsId_lt_total {x y : YjsId} :
    x < y ∨ y < x ∨ x = y := by
  obtain ⟨ xClientId, xClock ⟩ := x
  obtain ⟨ yClientId, yClock ⟩ := y
  simp only [LT.lt]
  unfold ClientId at *
  split
  · rw [beq_iff_eq] at *
    subst xClientId
    rw [beq_self_eq_true]
    simp
    omega
  · rw [Bool.beq_comm]
    split
    · contradiction
    · simp
      have h : (xClientId == yClientId) = false := by
        generalize hEq : (xClientId == yClientId) = eqb at *
        cases eqb <;> simp at *
      rw [beq_eq_false_iff_ne] at h
      omega

namespace YjsLtV2'

theorem first_lt_last {S : ItemSetV2 A} :
    YjsLtV2' S .first .last := by
  exact ⟨ 0, YjsLtV2.ltOriginOrder OriginLtV2.lt_first_last ⟩

theorem first_lt_idRef {S : ItemSetV2 A} {id : YjsId} :
    S.IdIn id ->
    YjsLtV2' S .first (.idRef id) := by
  intro hId
  exact ⟨ 0, YjsLtV2.ltOriginOrder (OriginLtV2.lt_first hId) ⟩

theorem idRef_lt_last {S : ItemSetV2 A} {id : YjsId} :
    S.IdIn id ->
    YjsLtV2' S (.idRef id) .last := by
  intro hId
  exact ⟨ 0, YjsLtV2.ltOriginOrder (OriginLtV2.lt_last hId) ⟩

end YjsLtV2'

namespace YjsLeqV2'

theorem first_leq_of_refIn {S : ItemSetV2 A} {x : ItemRef} :
    S.RefIn x ->
    YjsLeqV2' S .first x := by
  intro hRef
  cases x with
  | first =>
      exact YjsLeqV2'.leqSame _
  | last =>
      exact YjsLeqV2'.leqLt YjsLtV2'.first_lt_last
  | idRef id =>
      exact YjsLeqV2'.leqLt (YjsLtV2'.first_lt_idRef hRef)

theorem leq_last_of_refIn {S : ItemSetV2 A} {x : ItemRef} :
    S.RefIn x ->
    YjsLeqV2' S x .last := by
  intro hRef
  cases x with
  | first =>
      exact YjsLeqV2'.leqLt YjsLtV2'.first_lt_last
  | last =>
      exact YjsLeqV2'.leqSame _
  | idRef id =>
      exact YjsLeqV2'.leqLt (YjsLtV2'.idRef_lt_last hRef)

end YjsLeqV2'

namespace YjsItemSetInvariantV2

theorem pairDepth_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> Prop}
    (step : forall x y,
      (forall x' y', inv.pairDepth x' y' < inv.pairDepth x y -> motive x' y') ->
      motive x y) :
    forall x y, motive x y := by
  let P : Nat -> Prop := fun n => forall x y, inv.pairDepth x y = n -> motive x y
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y hEq
    apply step x y
    intro x' y' hLt
    have hLt' : inv.pairDepth x' y' < n := by
      simpa [hEq] using hLt
    exact ih (inv.pairDepth x' y') hLt' x' y' rfl
  intro x y
  exact hP (inv.pairDepth x y) x y rfl

theorem tripleDepth_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> ItemRef -> Prop}
    (step : forall x y z,
      (forall x' y' z', inv.tripleDepth x' y' z' < inv.tripleDepth x y z -> motive x' y' z') ->
      motive x y z) :
    forall x y z, motive x y z := by
  let P : Nat -> Prop := fun n => forall x y z, inv.tripleDepth x y z = n -> motive x y z
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y z hEq
    apply step x y z
    intro x' y' z' hLt
    have hLt' : inv.tripleDepth x' y' z' < n := by
      simpa [hEq] using hLt
    exact ih (inv.tripleDepth x' y' z') hLt' x' y' z' rfl
  intro x y z
  exact hP (inv.tripleDepth x y z) x y z rfl

end YjsItemSetInvariantV2
