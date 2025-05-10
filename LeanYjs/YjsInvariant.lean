import LeanYjs.Item
import LeanYjs.ItemOriginOrder
import LeanYjs.ActorId
import LeanYjs.ItemOrder

import Mathlib.Tactic.Set

variable {A : Type} [BEq A]

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : ClosedPredicate A)

def ItemSet := { i : YjsItem A // P.val i }

def OriginLeq' (x y : ItemSet P) : Prop :=
  x = y ∨ OriginLt A P (↑x.1) (↑y.1)

def YjsLt' (x y : ItemSet P) : Prop :=
  ∃ h, @YjsLt A P h (↑x.1) (↑y.1)

def YjsLeq' (x y : ItemSet P) : Prop :=
  ∃ h, @YjsLeq A P h (↑x.1) (↑y.1)

def YjsInvariant :=
  forall h (x y : YjsItem A),
    P.val x -> P.val y ->
    @YjsLt A P h x y ->
      (∃ h, @YjsLeq A P h x (y.origin)) ∨
      (∃ h,  @YjsLt A P h (y.origin) (x.origin)) ∨
      (x.origin = y.origin ∧ ((∃ h, @YjsLt A P h x.rightOrigin y) ∨ x.id < y.id))

def ItemSetInvariant :=
  P.val YjsPtr.first ∧
  P.val YjsPtr.last ∧
  (∀ (o : YjsPtr A) r id c, P.val (YjsItem.item o r id c) -> P.val o) ∧
  (∀ o (r : YjsPtr A) id c, P.val (YjsItem.item o r id c) -> P.val r) ∧
  (∀ (x y : YjsPtr A), P.val x -> P.val y -> OriginLt A P x y -> OriginLt A P y x -> False) ∧
  YjsInvariant P

lemma not_item_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsItem A), ¬ @YjsLt A P h o YjsPtr.first := by
  intros hinv h o
  apply @Nat.strongRecOn' (P := fun h => ∀ (o : YjsItem A), ¬ @YjsLt A P h o YjsPtr.first)
  intros n ih o hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ hlt =>
    have hlt2 : @OriginLt A P YjsPtr.first o := by
      apply OriginLt.ltOrigin (x := YjsPtr.first) (y := YjsPtr.itemPtr o)
      . apply hinv.1
      . apply origin_lt_p1 at hlt; assumption
      . apply OriginLtStep.lt_first
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.first) (y := o) <;> try assumption
    apply origin_lt_p1 at hlt; assumption
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    have hlt_h2 : h2 < max h1 h2 + 1 := by
      omega
    apply ih _ hlt_h2 _ hlt2

lemma not_last_lt_item {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsItem A), ¬ @YjsLt A P h YjsPtr.last o := by
  intros hinv h o
  apply @Nat.strongRecOn' (P := fun h => ∀ (o : YjsItem A), ¬ @YjsLt A P h YjsPtr.last o)
  intros n ih o hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ hlt =>
    have hlt2 : @OriginLt A P o YjsPtr.last := by
      apply OriginLt.ltOrigin (x := YjsPtr.itemPtr o) (y := YjsPtr.last)
      . apply origin_lt_p2 at hlt; assumption
      . apply hinv.2.1
      . apply OriginLtStep.lt_last
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.last) (y := o) <;> try assumption
    apply origin_lt_p2 at hlt; assumption
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    have hlt_h2 : h1 < max h1 h2 + 1 := by
      omega
    apply ih _ hlt_h2 _ hlt1

lemma not_last_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.first := by
  intros hinv h
  apply @Nat.strongRecOn' (P := fun h => ¬ @YjsLt A P h YjsPtr.last YjsPtr.first)
  intros n ih hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ hlt =>
    have hlt' : OriginLt _ P YjsPtr.first YjsPtr.last := by
      obtain ⟨ P, ⟨ a, b, c ⟩ ⟩ := P
      apply OriginLt.ltOrigin <;> try assumption
      apply OriginLtStep.lt_first_last
    obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
    apply hanti (x := YjsPtr.first) (y := YjsPtr.last) <;> assumption
  | ltTrans h1 h2 x y z hlt1 hlt2 =>
    apply not_item_lt_first at hlt2 <;> assumption


lemma not_first_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.first YjsPtr.first := by
  intros hinv h hlt
  have h: OriginLt A P YjsPtr.first YjsPtr.first := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_item_lt_first hinv at hlt2; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
  apply hanti (x := YjsPtr.first) (y := YjsPtr.first) <;> try assumption

lemma not_last_lt_last {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.last := by
  intros hinv h hlt
  have h: OriginLt A P YjsPtr.last YjsPtr.last := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltTrans h1 h2 x y z hlt1 hlt2 =>
      apply not_last_lt_item hinv at hlt1; contradiction
    | ltOriginOrder _ _ hlt =>
      assumption
  obtain ⟨ hfirst, hlast, hleft, hright, hanti, hinv ⟩ := hinv
  apply hanti (x := YjsPtr.last) (y := YjsPtr.last) <;> try assumption

lemma not_ptr_lt_first {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h o YjsPtr.first := by
  intros hinv h o
  cases o with
  | itemPtr item =>
    apply not_item_lt_first hinv
  | first =>
    apply not_first_lt_first hinv
  | last =>
    apply not_last_lt_first hinv

lemma not_last_lt_ptr {A} {P : ClosedPredicate A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h YjsPtr.last o := by
  intros hinv h o
  cases o with
  | itemPtr item =>
    apply not_last_lt_item hinv
  | first =>
    apply not_last_lt_first hinv
  | last =>
    apply not_last_lt_last hinv

lemma origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.origin := by
  intros x px
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  simp at *
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.origin] at *
  tauto

lemma right_origin_p_valid {A} {P : ClosedPredicate A} : forall (x : YjsItem A), P.val x -> P.val x.rightOrigin := by
  intros x px
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  simp at *
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.rightOrigin] at *
  tauto

lemma yjs_item_subset_anti_symmetry_lemma1 {A} {P : ClosedPredicate A} (inv: ItemSetInvariant P) :
  ∀ (x y : YjsItem A) (h1 h2 h3 : Nat),
    P.val x →
    P.val y →
    YjsLt P h1 x y ->
    YjsLt P h2 y x ->
    YjsLeq P h3 (YjsPtr.itemPtr x) y.origin →
    ∃ (x' y' : YjsItem A) (h1' h2' : Nat),
      P.val x' ∧ P.val y' ∧
      YjsLt P h1' x' y' ∧ YjsLt P h2' y' x' ∧ x'.size + y'.size < x.size + y.size := by
  intro x y h1 h2 h3 hx hy hltxy hltyx hleq
  have hpxo : P.val x.origin := by
    apply origin_p_valid; assumption
  have hpyo : P.val y.origin := by
    apply origin_p_valid; assumption

  have ⟨ h'', hlt' ⟩ : ∃ h'', YjsLt P h'' y.origin x := by
    exists max 0 h2 + 1
    apply YjsLt.ltTrans (y := y) <;> try assumption
    apply YjsLt.ltOriginOrder
    apply OriginLt.ltOrigin <;> try assumption
    . obtain ⟨ o, r, id, c ⟩ := y
      apply OriginLtStep.lt_left

  have ⟨ h''', hlt'' ⟩ : ∃ h''', YjsLt P h''' x y.origin := by
    cases hleq with
    | inl heq =>
      rw [<-heq]
      rw [<-heq] at hlt'
      exists h''
    | inr hlt =>
      exists h3

  generalize heq : y.origin = yo at hlt' hlt'' hpxo hpyo
  cases yo with
  | first =>
    apply not_item_lt_first inv at hlt''; contradiction
  | last =>
    apply not_last_lt_item inv at hlt'; contradiction
  | itemPtr yo =>
    exists x, yo, h''', h''
    constructor; assumption
    constructor; assumption
    constructor; assumption
    constructor; assumption
    obtain ⟨ o, r, id, c ⟩ := y
    simp [YjsItem.size, YjsItem.origin] at *
    rw [heq] at *
    simp [YjsPtr.size] at *
    omega

lemma yjs_item_subset_anti_symmetry_lemma2 {A} {P : ClosedPredicate A} (inv: ItemSetInvariant P) :
  ∀ (x y : YjsItem A) (h1 h2 h3 h4 : Nat),
    P.val x →
    P.val y →
    YjsLt P h1 x y ->
    YjsLt P h2 y x ->
    YjsLt P h3 y.origin x.origin →
    YjsLeq P h4 x.origin y.origin →
    ∃ (x' y' : YjsItem A) (h1' h2' : Nat),
      P.val x' ∧ P.val y' ∧
      YjsLt P h1' x' y' ∧ YjsLt P h2' y' x' ∧ x'.size + y'.size < x.size + y.size := by
  intro x y h1 h2 h3 h4 hx hy hltxy hltyx hltyoxo hleqxoyo
  have hpxo : P.val x.origin := by
    apply origin_p_valid; assumption
  have hpyo : P.val y.origin := by
    apply origin_p_valid; assumption
  have ⟨ h2', hlt2' ⟩ : ∃ h', YjsLt P h' x.origin y.origin := by
    cases hleqxoyo with
    | inl heq =>
      rw [heq] at hltyoxo
      rw [heq]
      exists h3
    | inr heq =>
      exists h4
  generalize heqxo : x.origin = xo at *
  generalize heqyo : y.origin = yo at *
  cases xo with
  | first =>
    apply not_ptr_lt_first inv at hltyoxo; contradiction
  | last =>
    apply not_last_lt_ptr inv at hlt2'; contradiction
  | itemPtr xo =>
    cases yo with
    | first =>
      apply not_item_lt_first inv at hlt2'; contradiction
    | last =>
      apply not_last_lt_item inv at hltyoxo; contradiction
    | itemPtr yo =>
      exists xo, yo, h2', h3
      constructor; assumption
      constructor; assumption
      constructor; assumption
      constructor; assumption
      obtain ⟨ o, r, id, c ⟩ := x
      obtain ⟨ yo, yr, yid, yc ⟩ := y

      simp [YjsItem.size, YjsItem.origin] at *
      rw [heqyo, heqxo] at *
      simp [YjsPtr.size] at *
      omega

lemma yjs_item_subset_anti_symmetry_lemma3 {A} {P : ClosedPredicate A} (inv: ItemSetInvariant P) :
  ∀ (x y : YjsItem A) (h1 h2 h3 : Nat),
    P.val x →
    P.val y →
    YjsLt P h1 x y ->
    YjsLt P h2 y x ->
    YjsLt P h3 x.rightOrigin y ->
    ∃ (x' y' : YjsItem A) (h1' h2' : Nat),
      P.val x' ∧ P.val y' ∧
      YjsLt P h1' x' y' ∧ YjsLt P h2' y' x' ∧ x'.size + y'.size < x.size + y.size := by
  intro x y h1 h2 h3 hx hy hltxy hltyx hlt
  have hpxro : P.val x.rightOrigin := by
    apply right_origin_p_valid; assumption

  have ⟨ h'', hlt' ⟩ : ∃ h'', YjsLt P h'' y x.rightOrigin := by
    exists max h2 0 + 1
    apply YjsLt.ltTrans
    . apply hltyx
    . apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try assumption
      obtain ⟨ o, r, id, c ⟩ := x
      apply OriginLtStep.lt_right

  generalize heq : x.rightOrigin = xro at *
  cases xro with
  | first =>
    apply not_item_lt_first inv at hlt'; contradiction
  | last =>
    apply not_last_lt_item inv at hlt; contradiction
  | itemPtr xro =>
    exists xro, y, h3, h''
    constructor; assumption
    constructor; assumption
    constructor; assumption
    constructor; assumption
    obtain ⟨ o, r, id, c ⟩ := x
    simp [YjsItem.size, YjsItem.rightOrigin] at *
    rw [heq] at *
    simp [YjsPtr.size] at *
    omega

lemma YjsItemSubsetAntiSymmetry' {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : ItemSet P), YjsLt' _ x y -> YjsLt' _ y x -> False := by
  intro inv x y lt1 lt2
  obtain ⟨ x, hx ⟩ := x
  obtain ⟨ y, hy ⟩ := y
  generalize hsize : x.size + y.size = size
  revert x y
  unfold YjsLt'; simp
  apply Nat.strongRecOn' (P := fun size => ∀ (x : YjsItem A), P.val x -> ∀ (y : YjsItem A), P.val y -> ∀ h, @YjsLt A P h x y -> ∀ h', @YjsLt A P h' y x ->
    x.size + y.size = size -> False) (n := size)
  intros size ih x hx y hy h1 hltxy h2 hltyx hsize
  cases size with
  | zero =>
    have hx : x.size = 0 := by omega
    cases x with
    | item o r id c =>
      unfold YjsItem.size at hx
      omega
  | succ size =>
    have hpx : P.val x := by
      apply yjs_lt_p1 at hltyx; assumption
    have hpy : P.val y := by
      apply yjs_lt_p2 at hltyx; assumption
    have hlt :
      (∃ h, YjsLeq P h (YjsPtr.itemPtr x) y.origin) ∨
      (∃ h, YjsLt P h y.origin x.origin) ∨
      x.origin = y.origin ∧ ((∃ h, YjsLt P h x.rightOrigin (YjsPtr.itemPtr y)) ∨ x.id < y.id) := by
      exact inv.2.2.2.2.2 h1 x y hpx hpy hltxy

    have hlt2 :
      (∃ h, YjsLeq P h (YjsPtr.itemPtr y) x.origin) ∨
      (∃ h, YjsLt P h x.origin y.origin) ∨
      y.origin = x.origin ∧ ((∃ h, YjsLt P h y.rightOrigin (YjsPtr.itemPtr x)) ∨ y.id < x.id) := by
      exact inv.2.2.2.2.2 h2 y x hpy hpx hltyx

    cases hlt with
    | inl hlt =>
      obtain ⟨ h', hlt ⟩ := hlt
      obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma1 inv x y _ _ _ hpx hpy hltxy hltyx hlt
      apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
    | inr hlt =>
      cases hlt2 with
      | inl hlt2 =>
        obtain ⟨ h', hlt2 ⟩ := hlt2
        obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma1 inv y x _ _ _ hpy hpx hltyx hltxy hlt2
        apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
      | inr hlt2 =>
        have ⟨ h', hleq ⟩ : ∃ h', YjsLeq P h' y.origin x.origin := by
          unfold YjsLeq
          cases hlt with
          | inl hlt =>
            obtain ⟨ h, hp ⟩ := hlt
            exists h
            right
            assumption
          | inr hlt =>
            obtain ⟨ heq, _ ⟩ := hlt
            exists 0
            left
            simp [heq]
        have ⟨ h'', hleq2 ⟩ : ∃ h', YjsLeq P h' x.origin y.origin := by
          unfold YjsLeq
          cases hlt2 with
          | inl hlt =>
            obtain ⟨ h, hp ⟩ := hlt
            exists h
            right
            assumption
          | inr hlt =>
            obtain ⟨ heq, _ ⟩ := hlt
            exists 0
            left
            simp [heq]
        cases hlt with
        | inl hlt =>
          obtain ⟨ h', hlt ⟩ := hlt
          obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma2 inv x y _ _ _ _ hpx hpy hltxy hltyx hlt hleq2
          apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
        | inr hlt =>
          cases hlt2 with
          | inl hlt2 =>
            obtain ⟨ h', hlt2 ⟩ := hlt2
            obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma2 inv y x _ _ _ _ hpy hpx hltyx hltxy hlt2 hleq
            apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
          | inr hlt2 =>
            obtain ⟨ heq, hlt ⟩ := hlt
            obtain ⟨ _, hlt2 ⟩ := hlt2
            cases hlt with
            | inl hlt =>
              obtain ⟨ h', hlt ⟩ := hlt
              obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma3 inv x y _ _ _ hpx hpy hltxy hltyx hlt
              apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
            | inr hlt =>
              cases hlt2 with
              | inl hlt2 =>
                obtain ⟨ h', hlt2 ⟩ := hlt2
                obtain ⟨ x', y', h1', h2', hpx', hpy', hltxy', hltyx', hltsize ⟩ := yjs_item_subset_anti_symmetry_lemma3 inv y x _ _ _ hpy hpx hltyx hltxy hlt2
                apply ih (x'.size + y'.size) _ x' hpx' y' hpy' h1' hltxy' h2' hltyx' <;> omega
              | inr hlt2 =>
                unfold ActorId at *
                omega
