import LeanYjs.ActorId
import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity

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

lemma yjs_lt_conflict_lt_decreases {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), ConflictLt' P x y -> ConflictLt' P y x ->
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros inv x y hltxy hltyx
  obtain ⟨ _, hltxy ⟩ := hltxy
  obtain ⟨ _, hltyx ⟩ := hltyx
  cases hltxy with
  | ltOriginDiff _ _ _ _ o1 o2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    cases hltyx with
    | ltOriginDiff _ _ _ _ _ _ _ _ _ _ _ _ hlt1' _ _ _ =>
      exists o1, o2
      constructor;
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
    | ltOriginSame _ _ _ _ o r id c =>
      exists o1, o1
      constructor;
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
  | ltOriginSame _ _ o r1 r2 id1 id2 c1 c2 hlt1 hlt2 hidlt =>
    cases hltyx with
    | ltOriginDiff _ _ _ _ o1 o2 r1' r2' id1' id2' c1' c2' hlt1' hlt2' hlt3' hlt4' =>
      exists o, o
      constructor;
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
    | ltOriginSame _ _ _ _ o r id c =>
      unfold ActorId at *
      omega

lemma yjs_leq_right_origin_decreases {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x : YjsItem A) (y : YjsPtr A) :
  YjsLeq' P x.rightOrigin y →
  YjsLt' P y x →
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros hxrleq hxy
  have hpx : P.val x := by
    apply yjs_lt'_p2 hxy
  have hpy : P.val y := by
    apply yjs_lt'_p1 hxy
  obtain ⟨ o, r, id, c ⟩ := x
  have hyxr : YjsLt' P y r := by
    apply yjs_lt_trans (y := (YjsItem.item o r id c)) <;> try assumption
    . apply P.property.closedRight
      apply yjs_lt'_p2
      assumption
    . constructor; apply YjsLt.ltOriginOrder <;> try assumption
      apply P.property.closedRight; assumption
      apply OriginLt.lt_right
  have hrylt : YjsLt' P r y := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | inl heq =>
      subst heq
      assumption
    | inr hlt =>
      constructor; assumption
  exists r, y
  constructor
  . simp [YjsPtr.size, YjsItem.size]; omega
  constructor <;> assumption

lemma yjs_leq_origin_decreases {A} {P : ClosedPredicate A} (inv : ItemSetInvariant P) (x : YjsPtr A) (y : YjsItem A) :
  YjsLeq' P x y.origin →
  YjsLt' P y x →
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros hxrleq hxy
  have hpx : P.val x := by
    apply yjs_lt'_p2 hxy
  have hpy : P.val y := by
    apply yjs_lt'_p1 hxy
  obtain ⟨ o, r, id, c ⟩ := y
  have hyxr : YjsLt' P o x := by
    apply yjs_lt_trans (y := (YjsItem.item o r id c)) <;> try assumption
    . apply P.property.closedLeft
      apply yjs_lt'_p1
      assumption
    . constructor; apply YjsLt.ltOriginOrder <;> try assumption
      apply P.property.closedLeft; assumption
      apply OriginLt.lt_left
  have hrylt : YjsLt' P x o := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | inl heq =>
      subst heq
      assumption
    | inr hlt =>
      constructor; assumption
  exists x, o
  constructor
  . simp [YjsPtr.size, YjsItem.size]; omega
  constructor <;> assumption

theorem yjs_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt' P x y -> YjsLt' P y x -> False := by
  intros inv x y hltxy hltyx
  generalize hsize : x.size + y.size = size
  revert x y
  apply Nat.strongRecOn' (P := fun size =>
    ∀ (x y : YjsPtr A), YjsLt' P x y → YjsLt' P y x → x.size + y.size = size → False)
  intros size ih x y hltxy hltyx hsize

  have hpx : P.val x := by
    apply yjs_lt'_p1 hltxy
  have hpy : P.val y := by
    apply yjs_lt'_p2 hltxy

  obtain hltxy' := yjs_lt'_cases _ _ _ _ hltxy
  rcases hltxy' with
  ⟨ hyfirst, _ ⟩ |
  ⟨ hxlast, _ ⟩ |
  ⟨ x, hxeq, hxrleq ⟩ |
  ⟨ y, hyeq, hyoleq ⟩ |
  hltxy'
  . subst hyfirst
    obtain ⟨ h, hltyx ⟩ := hltyx
    apply not_ptr_lt_first inv
    assumption
  . subst hxlast
    obtain ⟨ h, hltyx ⟩ := hltyx
    apply not_last_lt_ptr inv
    assumption
  . subst hxeq
    obtain ⟨ x', y', hsize', hltxy', hltyx' ⟩ :=
      yjs_leq_right_origin_decreases inv x y hxrleq hltyx
    apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize'])
    simp [YjsPtr.size, YjsItem.size] at hsize
    omega
  . subst hyeq
    obtain ⟨ x', y', hsize', hltxy', hltyx ⟩ :=
      yjs_leq_origin_decreases inv x y hyoleq hltyx
    apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx (by simp [hsize'])
    simp [YjsPtr.size, YjsItem.size] at hsize
    omega
  . obtain hltyx' := yjs_lt'_cases _ _ _ _ hltyx
    rcases hltyx' with
    ⟨ hxfirst, _ ⟩ |
    ⟨ hylast, _ ⟩ |
    ⟨ y, hyeq, hyrleq ⟩ |
    ⟨ x, hxeq, hxoleq ⟩ |
    hltyx'
    . subst hxfirst
      obtain ⟨ h, hltxy ⟩ := hltxy
      apply not_ptr_lt_first inv
      assumption
    . subst hylast
      obtain ⟨ h, hltxy ⟩ := hltxy
      apply not_last_lt_ptr inv
      assumption
    . subst hyeq
      obtain ⟨ x', y', hsize', hltxy', hltyx' ⟩ :=
        yjs_leq_right_origin_decreases inv y x hyrleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize'])
      simp [YjsPtr.size, YjsItem.size] at hsize
      omega
    . subst hxeq
      obtain ⟨ x', y', hsize', hltxy', hltyx ⟩ :=
        yjs_leq_origin_decreases inv y x hxoleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx (by simp [hsize])
      simp [YjsPtr.size, YjsItem.size] at hsize
      omega
    . obtain ⟨ x', y', hsize', hltxy', hltyx' ⟩ :=
        yjs_lt_conflict_lt_decreases inv x y hltxy' hltyx'
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize])
      omega
