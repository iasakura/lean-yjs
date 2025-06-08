import LeanYjs.ActorId
import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemSet

def YjsLt1 {A : Type} (P : ClosedPredicate A) (x y : YjsPtr A) : Prop :=
  ∃ h, @YjsLt A P h x y

lemma yjs_lt_origin_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), OriginLt _ P x y -> OriginLt _ P y x -> False := by
  intros inv x y hltxy hltyx
  unfold ItemSetInvariant at inv
  obtain ⟨ h1, h2, h3, h4, h5 ⟩ := inv
  apply h5 _ _ _ _ hltxy hltyx
  apply origin_lt_p1; assumption
  apply origin_lt_p1; assumption

lemma yjs_lt_conflict_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A) h1 h2, ConflictLt P h1 x y -> ConflictLt P h2 y x -> False := by
  intros inv x y h1 h2 hltxy hltyx

theorem yjs_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt1 P x y -> YjsLt1 P y x -> False := by
  intros inv x y hltxy hltyx
  obtain ⟨ h1, hltxy ⟩ := hltxy
  obtain ⟨ h2, hltyx ⟩ := hltyx
  revert x y h2
  apply Nat.strongRecOn' (P := fun h => ∀ x y, YjsLt P h x y -> ∀ h2, YjsLt P h2 y x -> False) h1
  intros h1 ih x y hltxy h2 hltyx
  cases hltxy with
  | ltTrans h1' h2' x t y hltxy hltyz =>
    have hltty : YjsLt P (max h2' h2 + 1) t x := by
      apply yjs_lt_p_trans (y := y) <;> assumption
    apply ih h1' _ x t hltxy _ hltty <;> try assumption
    omega
  | ltConflict h x y hltxy =>
    cases hltxy with
    | ltOriginSame h1' h2' l r1 r2 id1 id2 c1 c2 hltxy1 hltxy2 hltid =>
