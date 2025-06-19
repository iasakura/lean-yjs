import LeanYjs.ActorId
import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality

lemma yjs_lt_origin_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), P.val x -> P.val y -> OriginLt _ x y -> OriginLt _ y x -> False := by
  intros inv x y hpx hpy hltxy hltyx
  cases hltxy with
  | lt_left _ r id c =>
    cases hltyx with
    | lt_right =>
      apply inv.origin_not_leq _ _ _ _ hpy 0
      left
      eq_refl
    | lt_last =>
      have hpr : P.val r := by
        obtain ⟨ P, hP ⟩ := P
        apply hP.closedRight; assumption
      apply inv.origin_not_leq _ _ _ _ hpy
      cases r with
      | last =>
        left
        eq_refl
      | first =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        apply OriginLt.lt_first_last
      | itemPtr item =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        apply OriginLt.lt_last
  | lt_right o _ id c =>
    cases hltyx with
    | lt_left =>
      apply inv.origin_not_leq _ _ _ _ hpx 0
      left
      eq_refl
    | lt_first =>
      have hpo : P.val o := by
        obtain ⟨ P, hP ⟩ := P
        apply hP.closedLeft; assumption
      apply inv.origin_not_leq _ _ _ _ hpx
      cases o with
      | first =>
        left
        eq_refl
      | last =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        apply OriginLt.lt_first_last
      | itemPtr item =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        apply OriginLt.lt_first
  | lt_first x =>
    cases hltyx with
    | lt_right o r id c =>
      apply inv.origin_not_leq _ _ _ _ hpy 0
      cases o with
      | first =>
        left
        eq_refl
      | last =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        simp
        apply OriginLt.lt_first_last
      | itemPtr item =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        simp at *
        obtain ⟨ P, hP ⟩ := P
        apply hP.closedLeft; assumption
        apply OriginLt.lt_first
  | lt_last x =>
    cases hltyx with
    | lt_left o r id c =>
      apply inv.origin_not_leq _ _ _ _ hpx 0
      cases r with
      | last =>
        left
        eq_refl
      | first =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        simp
        apply OriginLt.lt_first_last
      | itemPtr item =>
        right
        apply YjsLt.ltOriginOrder <;> try assumption
        simp at *
        obtain ⟨ P, hP ⟩ := P
        apply hP.closedRight; assumption
        apply OriginLt.lt_last
  | lt_first_last =>
    cases hltyx

structure Conflicts {A} (P : ClosedPredicate A) (x y : YjsItem A) where
  x_origin_y : YjsLt' P x.origin y
  y_origin_x : YjsLt' P y.origin x
  x_y_right : YjsLt' P x y.rightOrigin
  y_x_right : YjsLt' P y x.rightOrigin

lemma conflict_lt_conflicts {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A) h, ConflictLt P h x y ->
    ∃ (x' y' : YjsItem A),
      x = x' ∧ y = y' ∧ Conflicts P x' y' := by
  intros inv x y h hltxy
  cases hltxy with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 l3 l4 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    exists (YjsItem.item l1 l3 id1 c1), (YjsItem.item l2 l4 id2 c2)
    constructor; simp
    constructor; simp
    constructor <;> (unfold YjsLt'; simp [YjsItem.origin, YjsItem.rightOrigin])
    . constructor; assumption
    . constructor
      apply yjs_lt_p_trans inv _ l1 _ _ _ hlt1
      apply YjsLt.ltOriginOrder
      apply yjs_lt_p2 hlt1
      apply yjs_lt_p1 hlt2
      apply OriginLt.lt_left
    . constructor; assumption
    . constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 hid =>
    exists (YjsItem.item l r1 id1 c1), (YjsItem.item l r2 id2 c2)
    have hpl : P.val l := by
      obtain ⟨ P, hP ⟩ := P
      apply hP.closedLeft
      apply yjs_lt_p1 hlt1
    have hpr1 : P.val r1 := by
      obtain ⟨ P, hP ⟩ := P
      apply hP.closedRight
      apply yjs_lt_p1 hlt1
    have hpr2 : P.val r2 := by
      obtain ⟨ P, hP ⟩ := P
      apply hP.closedRight
      apply yjs_lt_p1 hlt2
    constructor; simp
    constructor; simp
    constructor <;> (unfold YjsLt'; simp [YjsItem.origin, YjsItem.rightOrigin])
    . constructor
      apply YjsLt.ltOriginOrder <;> try assumption
      apply yjs_lt_p1 hlt2
      apply OriginLt.lt_left
    . constructor
      apply YjsLt.ltOriginOrder <;> try assumption
      apply yjs_lt_p1 hlt1
      apply OriginLt.lt_left
    . constructor; assumption
    . constructor; assumption

lemma yjs_lt_conflict_lt_anti_symm {A} {P : ClosedPredicate A} :
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A) h1 h2, ConflictLt P h1 x y -> ConflictLt P h2 y x ->
    ∃ (x' y' : YjsPtr A) (h1' h2' : ℕ),
      YjsLt P h1' x' y' ∧ YjsLt P h2' y' x' ∧ x'.size + y'.size < x.size + y.size := by
  intros inv x y h1 h2 hltxy hltyx
  cases hltxy with
  | ltOriginDiff h1' h2' h3' h4' l1 l2 l3 l4 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    cases hltyx with
    | ltOriginDiff h1'' h2'' h3'' h4'' l1' l2' l3' l4' id1' id2' c1' c2' hlt1' hlt2' hlt3' hlt4' =>
      exists l1, l2
      constructor
      constructor
      constructor; assumption
      constructor; assumption
      simp [YjsPtr.size]
      simp [YjsItem.size]
      omega
    | ltOriginSame h1'' h2'' l r1 r2 id1' id2' c1' c2' hlt1' hlt2' hid =>
      exists l1, l1
      constructor
      constructor
      constructor; assumption
      constructor; assumption
      simp [YjsPtr.size]
      simp [YjsItem.size]
      omega
  | ltOriginSame h1' h2' l r1 r2 id1 id2 c1 c2 hlt1 hlt2 hid =>
    cases hltyx with
    | ltOriginDiff h1'' h2'' h3'' h4'' l1' l2' l3' l4' id1' id2' c1' c2' hlt1' hlt2' hlt3' hlt4' =>
      exists l, l
      constructor
      constructor
      constructor; assumption
      constructor; assumption
      simp [YjsPtr.size]
      simp [YjsItem.size]
      omega
    | ltOriginSame h1'' h2'' l r1 r2 id1' id2' c1' c2' hlt1' hlt2' hid =>
      unfold ActorId at *
      omega

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
