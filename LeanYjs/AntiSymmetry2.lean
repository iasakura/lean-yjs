import LeanYjs.ActorId
import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality

lemma yjs_lt_origin_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), P.val x -> P.val y -> OriginLt _ x y -> OriginLt _ y x ->
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros inv x y hpx hpy hltxy hltyx
  cases hltxy with
  | lt_left _ r id c =>
    cases hltyx with
    | lt_right =>
      obtain hlt := inv.origin_not_leq _ _ _ _ hpy
      exists x, x
      constructor
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> assumption
    | lt_last =>
      have hpr : P.val r := by
        obtain ⟨ P, hP ⟩ := P
        apply hP.closedRight; assumption
      obtain ⟨ h, hlt ⟩ := inv.origin_not_leq _ _ _ _ hpy
      apply not_last_lt_ptr inv at hlt
      cases hlt
  | lt_right o _ id c =>
    cases hltyx with
    | lt_left =>
      obtain hlt := inv.origin_not_leq _ _ _ _ hpx
      exists y, y
      constructor
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> assumption
    | lt_first =>
      obtain ⟨ h, hlt ⟩ := inv.origin_not_leq _ _ _ _ hpx
      apply not_ptr_lt_first inv at hlt
      cases hlt
  | lt_first x =>
    cases hltyx with
    | lt_right o r id c =>
      obtain ⟨ h, hlt ⟩ := inv.origin_not_leq _ _ _ _ hpy
      apply not_ptr_lt_first inv at hlt
      cases hlt
  | lt_last x =>
    cases hltyx with
    | lt_left o r id c =>
      obtain ⟨ h, hlt ⟩ := inv.origin_not_leq _ _ _ _ hpx
      apply not_last_lt_ptr inv at hlt
      cases hlt
  | lt_first_last =>
    cases hltyx

lemma yjs_lt_conflict_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A) h1 h2, ConflictLt P h1 x y -> ConflictLt P h2 y x -> False := by
  intros inv x y h1 h2 hltxy hltyx
  sorry

theorem yjs_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt' P x y -> YjsLt' P y x -> False := by
  intros inv x y hltxy hltyx
  obtain ⟨ h1, hltxy ⟩ := hltxy
  obtain ⟨ h2, hltyx ⟩ := hltyx
  generalize hsize : x.size + y.size = size
  revert x y
  revert h1 h2
  apply Nat.strongRecOn' (P := fun size =>
    ∀ (h1 h2 : ℕ) (x y : YjsPtr A), YjsLt P h1 x y → YjsLt P h2 y x → x.size + y.size = size → False)
  intros size ih h1 h2 x y hltxy hltyx hsize
  cases hltxy with
  | ltTrans h1' h2' x t y hltxy hltyz =>
    have hltxy' : YjsLt P (max h1' (h2' + 1) + 1) x t := by
      apply yjs_lt_p_trans _ _ y _ <;> try assumption

  | ltConflict h1' x' y' hltx'y' =>
    cases hltyx with
    | ltConflict h2' x'' y'' hlty'x''y'' =>
      apply yjs_lt_conflict_lt_anti_symm inv _ _ h1' h2' hltx'y' hlty'x''y''
    | ltTrans h2' h3' x'' t y'' hltxy' hltyx'' =>
      have hltxy' : YjsLt P (max h3' (h1' + 1) + 1) t y := by
        apply yjs_lt_p_trans _ _ x _ <;> try assumption
        apply YjsLt.ltConflict; assumption
      apply ih h1' _ x'' t hltxy' _ hltyx'' <;> try assumption

    | ltOriginOrder x' y' hpx' hpy' hltyx'o =>
