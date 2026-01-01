import LeanYjs.ClientId
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity

theorem YjsId_lt_asymm {id1 id2 : YjsId} :
  id1 < id2 -> ¬ (id2 < id1) := by
  intro hlt hlt2
  obtain ⟨ clientId1, clock1 ⟩ := id1
  obtain ⟨ clientId2, clock2 ⟩ := id2
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hlt
  . split at hlt2
    . omega
    . omega
  . split at hlt2
    . omega
    . omega

theorem yjs_lt_conflict_lt_decreases {A} {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), P x -> P y -> ConflictLt' x y -> ConflictLt' y x ->
  ∃ (x' y' : YjsPtr A), P x' ∧ P y' ∧ x'.size + y'.size < x.size + y.size ∧ YjsLt' x' y' ∧ YjsLt' y' x' := by
  intros hP inv x y hpx hpy hltxy hltyx
  obtain ⟨ _, hltxy ⟩ := hltxy
  obtain ⟨ _, hltyx ⟩ := hltyx
  cases hltxy with
  | ltOriginDiff h1 h2 h3 h4 o1 o2 r1 r2 id1 id2 c1 c2 d1 d2 hlt1 hlt2 hlt3 hlt4 =>
    cases hltyx with
    | ltOriginDiff h1' h2' h3' h4' _ _ _ _ _ _ _ _ _ _ hlt1' hlt2' hlt3' hlt4' =>
      exists o1, o2
      constructor
      . apply hP.closedLeft at hpx; assumption
      constructor
      . apply hP.closedLeft at hpy; assumption
      constructor
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
    | ltOriginSame h1' h2' _ _ o r id c d1' d2' =>
      exists o1, o1
      constructor
      . apply hP.closedLeft at hpx; assumption
      constructor
      . apply hP.closedLeft at hpy; assumption
      constructor;
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
  | ltOriginSame h1 h2 o r1 r2 id1 id2 c1 c2 d1 d2 hlt1 hlt2 hidlt =>
    cases hltyx with
    | ltOriginDiff h5 h6 h7 h8 o1 o2 r1' r2' id1' id2' c1' c2' d1' d2' hlt1' hlt2' hlt3' hlt4' =>
      exists o, o
      constructor;
      . apply hP.closedLeft at hpx; assumption
      constructor;
      . apply hP.closedLeft at hpy; assumption
      constructor
      . simp [YjsPtr.size, YjsItem.size]; omega
      constructor <;> (constructor; assumption)
    | ltOriginSame h5 h6 _ _ o r id c d3 d4 =>
      unfold ClientId at *
      obtain h := YjsId_lt_asymm hidlt
      contradiction

theorem yjs_leq_right_origin_decreases {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x : YjsItem A) (y : YjsPtr A) :
  P x -> P y ->
  IsClosedItemSet P ->
  YjsLeq' x.rightOrigin y →
  YjsLt' y x →
  ∃ (x' y' : YjsPtr A), P x' ∧ P y' ∧ x'.size + y'.size < x.size + y.size ∧ YjsLt' x' y' ∧ YjsLt' y' x' := by
  intros hpx hpy hP hxrleq hxy
  obtain ⟨ o, r, id, c, d ⟩ := x
  have hyxr : YjsLt' y r := by
    apply yjs_lt_trans hP (y := (YjsItem.mk o r id c d)) <;> try assumption
    . apply hP.closedRight at hpx; assumption
    . use 1; apply YjsLt.ltRightOrigin; try assumption
      left
  have hrylt : YjsLt' r y := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | leqSame =>
      assumption
    | leqLt h _ _ hlt =>
      constructor; assumption
  exists r, y
  constructor
  . apply hP.closedRight at hpx; assumption
  constructor
  . assumption
  constructor
  . simp [YjsItem.size]; omega
  constructor <;> assumption

theorem yjs_leq_origin_decreases {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x : YjsPtr A) (y : YjsItem A) :
  P x -> P y ->
  IsClosedItemSet P ->
  YjsLeq' x y.origin →
  YjsLt' y x →
  ∃ (x' y' : YjsPtr A), P x' ∧ P y' ∧ x'.size + y'.size < x.size + y.size ∧ YjsLt' x' y' ∧ YjsLt' y' x' := by
  intros hpx hpy hP hxrleq hxy
  obtain ⟨ o, r, id, c, d ⟩ := y
  have hyxr : YjsLt' o x := by
    apply yjs_lt_trans hP (y := (YjsItem.mk o r id c d)) <;> try assumption
    . apply hP.closedLeft at hpy; assumption
    . use 1; apply YjsLt.ltOrigin; try assumption
      left
  have hrylt : YjsLt' x o := by
    obtain ⟨ h, hxrleq ⟩ := hxrleq
    cases hxrleq with
    | leqSame heq =>
      assumption
    | leqLt h _ _ hlt =>
      constructor; assumption
  exists x, o
  constructor
  . assumption
  constructor
  . apply hP.closedLeft at hpy; assumption
  constructor
  . simp [YjsItem.size]; omega
  constructor <;> assumption

theorem yjs_lt_asymm {A} [DecidableEq A] {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), P x -> P y -> YjsLt' x y -> YjsLt' y x -> False := by
  intros hP inv x y hpx hpy hltxy hltyx
  generalize hsize : x.size + y.size = size
  revert x y
  apply Nat.strongRecOn' (P := fun size =>
    ∀ (x y : YjsPtr A), P x -> P y -> YjsLt' x y → YjsLt' y x → x.size + y.size = size → False)
  intros size ih x y hpx hpy hltxy hltyx hsize

  obtain hltxy' := yjs_lt'_cases _ _ _ hltxy
  rcases hltxy' with
  ⟨ hyfirst, _ ⟩ |
  ⟨ hxlast, _ ⟩ |
  ⟨ x, hxeq, hxrleq ⟩ |
  ⟨ y, hyeq, hyoleq ⟩ |
  hltxy'
  . subst hyfirst
    obtain ⟨ h, hltyx ⟩ := hltyx
    apply not_ptr_lt_first hP inv (o := y) <;> assumption
  . subst hxlast
    obtain ⟨ h, hltyx ⟩ := hltyx
    apply not_last_lt_ptr hP inv (o := x) <;> assumption
  . subst hxeq
    obtain ⟨ x', y', hpx', hpy', hsize', hltxy', hltyx' ⟩ :=
      yjs_leq_right_origin_decreases inv x y hpx hpy hP hxrleq hltyx
    apply ih (x'.size + y'.size) _ x' y' hpx' hpy' hltxy' hltyx' (by simp)
    simp [YjsPtr.size] at hsize
    omega
  . subst hyeq
    obtain ⟨ x', y', hpx', hpy', hsize', hltxy', hltyx ⟩ :=
      yjs_leq_origin_decreases inv x y hpx hpy hP hyoleq hltyx
    apply ih (x'.size + y'.size) _ x' y' hpx' hpy' hltxy' hltyx (by simp)
    simp [YjsPtr.size] at hsize
    omega
  . obtain hltyx' := yjs_lt'_cases _ _ _ hltyx
    rcases hltyx' with
    ⟨ hxfirst, _ ⟩ |
    ⟨ hylast, _ ⟩ |
    ⟨ y, hyeq, hyrleq ⟩ |
    ⟨ x, hxeq, hxoleq ⟩ |
    hltyx'
    . subst hxfirst
      obtain ⟨ h, hltxy ⟩ := hltxy
      apply not_ptr_lt_first hP inv (o := x) <;> assumption
    . subst hylast
      obtain ⟨ h, hltxy ⟩ := hltxy
      apply not_last_lt_ptr hP inv (o := y) <;> assumption
    . subst hyeq
      obtain ⟨ x', y', hpx', hpy', hsize', hltxy', hltyx' ⟩ :=
        yjs_leq_right_origin_decreases inv y x hpy hpx hP hyrleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hpx' hpy' hltxy' hltyx' (by simp)
      simp [YjsPtr.size] at hsize
      omega
    . subst hxeq
      obtain ⟨ x', y', hpx', hpy', hsize', hltxy', hltyx ⟩ :=
        yjs_leq_origin_decreases inv y x hpy hpx hP hxoleq hltxy
      apply ih (x'.size + y'.size) _ x' y' hpx' hpy' hltxy' hltyx (by simp)
      simp [YjsPtr.size] at hsize
      omega
    . obtain ⟨ x', y', hpx', hpy', hsize', hltxy', hltyx' ⟩ :=
        yjs_lt_conflict_lt_decreases hP inv x y hpx hpy hltxy' hltyx'
      apply ih (x'.size + y'.size) _ x' y' hpx' hpy' hltxy' hltyx' (by simp)
      omega

theorem yjs_lt_of_not_leq {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y : YjsPtr A) :
  IsClosedItemSet P ->
  P x -> P y ->
  YjsLt' x y → ¬ YjsLeq' y x := by
  intros hP hpx hpy hltxy
  by_contra hltyx
  have hlt : YjsLt' y x := by
    obtain ⟨ h, hltyx ⟩ := hltyx
    cases hltyx with
    | leqSame =>
      assumption
    | leqLt h _ _ hlt =>
      constructor; assumption
  apply yjs_lt_asymm hP inv x y hpx hpy hltxy hlt
