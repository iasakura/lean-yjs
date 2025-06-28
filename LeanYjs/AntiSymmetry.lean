import LeanYjs.ActorId
import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity

lemma yjs_lt_conflict_lt_decreases {A} {P : ItemSet A} :
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

lemma yjs_leq_right_origin_decreases {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x : YjsItem A) (y : YjsPtr A) :
  IsClosedItemSet P ->
  YjsLeq' P x.rightOrigin y →
  YjsLt' P y x →
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros hP hxrleq hxy
  have hpx : P x := by
    apply yjs_lt'_p2 hxy
  have hpy : P y := by
    apply yjs_lt'_p1 hxy
  obtain ⟨ o, r, id, c ⟩ := x
  have hyxr : YjsLt' P y r := by
    apply yjs_lt_trans (y := (YjsItem.item o r id c)) <;> try assumption
    . apply hP.closedRight
      apply yjs_lt'_p2
      assumption
    . constructor; apply YjsLt.ltRightOrigin <;> try assumption
      left
      apply hP.closedRight; assumption
  have hrylt : YjsLt' P r y := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | leqSame =>
      assumption
    | leqLt h _ _ hlt =>
      constructor; assumption
  exists r, y
  constructor
  . simp [YjsPtr.size, YjsItem.size]; omega
  constructor <;> assumption

lemma yjs_leq_origin_decreases {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x : YjsPtr A) (y : YjsItem A) :
  IsClosedItemSet P ->
  YjsLeq' P x y.origin →
  YjsLt' P y x →
  ∃ x' y', x'.size + y'.size < x.size + y.size ∧ YjsLt' P x' y' ∧ YjsLt' P y' x' := by
  intros hP hxrleq hxy
  have hpx : P x := by
    apply yjs_lt'_p2 hxy
  have hpy : P y := by
    apply yjs_lt'_p1 hxy
  obtain ⟨ o, r, id, c ⟩ := y
  have hyxr : YjsLt' P o x := by
    apply yjs_lt_trans (y := (YjsItem.item o r id c)) <;> try assumption
    . apply hP.closedLeft
      apply yjs_lt'_p1
      assumption
    . constructor; apply YjsLt.ltOrigin <;> try assumption
      left
      apply hP.closedLeft; assumption
  have hrylt : YjsLt' P x o := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | leqSame heq =>
      assumption
    | leqLt h _ _ hlt =>
      constructor; assumption
  exists x, o
  constructor
  . simp [YjsPtr.size, YjsItem.size]; omega
  constructor <;> assumption

theorem yjs_lt_anti_symm {A} {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt' P x y -> YjsLt' P y x -> False := by
  intros hP inv x y hltxy hltyx
  generalize hsize : x.size + y.size = size
  revert x y
  apply Nat.strongRecOn' (P := fun size =>
    ∀ (x y : YjsPtr A), YjsLt' P x y → YjsLt' P y x → x.size + y.size = size → False)
  intros size ih x y hltxy hltyx hsize

  have hpx : P x := by
    apply yjs_lt'_p1 hltxy
  have hpy : P y := by
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
      yjs_leq_right_origin_decreases inv x y hP hxrleq hltyx
    apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize'])
    simp [YjsPtr.size, YjsItem.size] at hsize
    omega
  . subst hyeq
    obtain ⟨ x', y', hsize', hltxy', hltyx ⟩ :=
      yjs_leq_origin_decreases inv x y hP hyoleq hltyx
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
        yjs_leq_right_origin_decreases inv y x hP hyrleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize'])
      simp [YjsPtr.size, YjsItem.size] at hsize
      omega
    . subst hxeq
      obtain ⟨ x', y', hsize', hltxy', hltyx ⟩ :=
        yjs_leq_origin_decreases inv y x hP hxoleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx (by simp [hsize])
      simp [YjsPtr.size, YjsItem.size] at hsize
      omega
    . obtain ⟨ x', y', hsize', hltxy', hltyx' ⟩ :=
        yjs_lt_conflict_lt_decreases inv x y hltxy' hltyx'
      apply ih (x'.size + y'.size) _ x' y' hltxy' hltyx' (by simp [hsize])
      omega
