import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity
import LeanYjs.Order.Asymmetry
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Lemmas

variable {A : Type}
variable [DecidableEq A]

def ArrSet (arr : List (YjsItem A)) : YjsPtr A -> Prop :=
  fun a => match a with
  | YjsPtr.itemPtr item => item ∈ arr
  | YjsPtr.first => True
  | YjsPtr.last => True

def ArrSetClosed (arr : List (YjsItem A)) : Prop :=
  IsClosedItemSet (ArrSet arr)

omit [DecidableEq A] in theorem arr_set_closed_push (arr : List (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr ->
  ArrSet arr item.origin ->
  ArrSet arr item.rightOrigin ->
  ArrSetClosed (item :: arr) := by
  intros hclosed horigin hright
  constructor
  . simp [ArrSet]
  . simp [ArrSet]
  . intros o r id c d hor
    cases o with
    | itemPtr item' =>
      simp [ArrSet] at hor
      cases hor with
      | inr hitem =>
        right
        apply hclosed.closedLeft at hitem
        assumption
      | inl heq =>
        subst heq
        right
        assumption
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
  . intros o r id c d hor
    cases r with
    | itemPtr item' =>
      simp [ArrSet] at hor
      cases hor with
      | inr hitem =>
        right
        apply hclosed.closedRight at hitem
        assumption
      | inl heq =>
        subst heq
        right
        assumption
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]

omit [DecidableEq A] in theorem arr_set_item_exists_index (arr arr' : List (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr' ->
  ArrSet arr item ->
  (∃ l, l ++ arr = arr') ->
  ∃ i : Fin arr.length, arr[i] = item := by
  intros hclosed hitem hsublist
  induction arr with
  | nil =>
    simp [ArrSet] at hitem
  | cons head arr ih =>
    simp [ArrSet] at hitem
    cases hitem with
    | inl heq =>
      subst heq
      have zero_lt_len : 0 < (item :: arr).length := by simp
      exists Fin.mk 0 zero_lt_len
    | inr hin =>
      have hsublist' : ∃ l', l' ++ arr = arr' := by
        obtain ⟨ l, heq ⟩ := hsublist
        exists (l ++ [head])
        rw [List.append_assoc]
        simp; assumption
      obtain ⟨ i, hi ⟩ := ih hin hsublist'
      let i' : Fin ((head :: arr).length) := by
        simp
        apply Fin.addNat i 1
      exists i'

omit [DecidableEq A] in theorem arr_set_closed_exists_index_for_origin :
  ∀ (arr : List (YjsItem A)) (item : YjsItem A),
  ArrSetClosed arr ->
  ArrSet arr item ->
  item.origin = YjsPtr.first ∨ item.origin = YjsPtr.last ∨ ∃ i : Fin arr.length, arr[i] = item.origin := by
  intros arr item hclosed hitem
  obtain ⟨ o, r, id, c, d ⟩ := item
  apply hclosed.closedLeft at hitem
  simp
  cases o with
  | first =>
    left; simp
  | last =>
    right; left; simp
  | itemPtr o =>
    right; right
    obtain ⟨ i, h ⟩ := arr_set_item_exists_index arr arr o hclosed hitem (by exists [])
    exists i
    simp
    assumption

omit [DecidableEq A] in theorem arr_set_closed_exists_index_for_right_origin :
  ∀ (arr : List (YjsItem A)) (item : YjsItem A),
  ArrSetClosed arr ->
  ArrSet arr item ->
  item.rightOrigin = YjsPtr.first ∨ item.rightOrigin = YjsPtr.last ∨ ∃ i : Fin arr.length, arr[i] = item.rightOrigin := by
  intros arr item hclosed hitem
  obtain ⟨ o, r, id, c, d ⟩ := item
  apply hclosed.closedRight at hitem
  simp
  cases r with
  | first =>
    left; simp
  | last =>
    right; left; simp
  | itemPtr o =>
    right; right
    obtain ⟨ i, h ⟩ := arr_set_item_exists_index arr arr o hclosed hitem (by exists [])
    exists i
    simp
    assumption

-- omit [DecidableEq A] in theorem yjs_lt_mono (P Q : ItemSet A) (x y : YjsPtr A) :
--   IsClosedItemSet P ->
--   ItemSetInvariant P ->
--   (∀ a, P a -> Q a) ->
--   YjsLt h x y ->
--   YjsLt h x y := by
--   intros hclosedP hinvP hsubset
--   intros hlt
--   revert hlt x y
--   apply Nat.strongRec' (p := fun h => ∀ x y, YjsLt h x y → YjsLt h x y)
--   intros n ih x y hlt
--   cases hlt with
--   | ltOriginOrder _  _ hlt =>
--     apply YjsLt.ltOriginOrder
--     . assumption
--   | ltConflict _ _ _ hlt =>
--     cases hlt with
--     | ltOriginDiff =>
--       apply YjsLt.ltConflict
--       apply ConflictLt.ltOriginDiff
--       all_goals (apply ih; unfold max4; omega)
--       all_goals (assumption)
--     | ltOriginSame =>
--       apply YjsLt.ltConflict
--       apply ConflictLt.ltOriginSame <;> try assumption
--   | ltOrigin _ _ _ _ _ _ hlt =>
--     apply YjsLt.ltOrigin
--     . cases hlt with
--       | leqSame =>
--         apply YjsLeq.leqSame
--       | leqLt =>
--         apply YjsLeq.leqLt
--         apply ih <;> try assumption
--         omega
--   | ltRightOrigin _ _ _ _ _ _ hlt =>
--     apply YjsLt.ltRightOrigin
--     . cases hlt with
--       | leqSame =>
--         apply YjsLeq.leqSame
--       | leqLt =>
--         apply YjsLeq.leqLt
--         apply ih <;> try assumption
--         omega

-- omit [DecidableEq A] in theorem yjs_lt'_mono :
--   ∀ (P Q : ItemSet A) (x y : YjsPtr A),
--   IsClosedItemSet P ->
--   ItemSetInvariant P ->
--   (∀ a, P a -> Q a) ->
--   YjsLt' x y -> YjsLt' x y := by
--   intros P Q x y hclosedP hinvP hsubset hlt
--   obtain ⟨ _, hlt ⟩ := hlt
--   constructor
--   apply yjs_lt_mono P Q x y hclosedP hinvP hsubset hlt

-- omit [DecidableEq A] in theorem yjs_leq'_mono :
--   ∀ (P Q : ItemSet A) (x y : YjsPtr A),
--   IsClosedItemSet P ->
--   ItemSetInvariant P ->
--   (∀ a, P a -> Q a) ->
--   YjsLeq' x y -> YjsLeq' x y := by
--   intros P Q x y hclosedP hinvP hsubset hleq
--   obtain ⟨ _, hleq ⟩ := hleq
--   cases hleq with
--   | leqSame =>
--     exists 0
--     apply YjsLeq.leqSame
--   | leqLt =>
--     constructor
--     apply YjsLeq.leqLt
--     apply yjs_lt_mono P Q x y hclosedP hinvP hsubset
--     assumption

theorem push_subset {A} (arr : List (YjsItem A)) (a : YjsItem A) :
  ∀ x, ArrSet arr x -> ArrSet (a :: arr) x := by
  intros x hin
  unfold ArrSet at *
  simp
  cases x <;> (simp at *)
  right; assumption

theorem reachable_in {A} (arr : List (YjsItem A)) (a : YjsPtr A) :
  IsClosedItemSet (ArrSet arr) ->
  ∀ x, OriginReachable a x -> ArrSet arr a -> ArrSet arr x := by
  intros hclosed x hreach hin
  induction hreach with
  | reachable_head x a y step h ih =>
    cases step with
    | reachable =>
      simp [ArrSet] at hin
      apply hclosed.closedLeft at hin
      apply ih
      assumption
    | reachable_right =>
      simp [ArrSet] at hin
      apply hclosed.closedRight at hin
      apply ih
      assumption
  | reachable_single _ _ hstep =>
    cases hstep with
    | reachable =>
      simp [ArrSet] at hin
      apply hclosed.closedLeft at hin
      assumption
    | reachable_right =>
      simp [ArrSet] at hin
      apply hclosed.closedRight at hin
      assumption

omit [DecidableEq A] in theorem item_set_invariant_push (arr : List (YjsItem A)) (item : YjsItem A) :
  ItemSetInvariant (ArrSet arr) ->
  ArrSetClosed arr ->
  YjsLt' item.origin item.rightOrigin ->
  (∀ x, OriginReachable item x -> YjsLeq' x item.origin ∨ YjsLeq' item.rightOrigin x) ->
  (∀ x : YjsItem A, ArrSet arr x -> x.id = item.id -> x = item) ->
  ItemSetInvariant (ArrSet (item :: arr)) := by
  intros hinv hclosed horigin hreach hsameid
  apply ItemSetInvariant.mk
  . intros o r c id d hitem
    simp [ArrSet] at hitem
    cases hitem with
    | inr hin =>
      apply hinv.origin_not_leq at hin; assumption
    | inl heq =>
      subst heq
      assumption
  . intros o r c id d x hin hreachable h_x_deleted
    simp [ArrSet] at hin
    cases hin with
    | inr hin =>
      apply hinv.origin_nearest_reachable _ _ _ _ _ _ hin hreachable h_x_deleted
    | inl heq =>
      subst heq
      simp at *
      apply hreach _ hreachable
  . intros x y h_id_eq h_set_x h_set_y
    simp [ArrSet] at *
    cases h_set_x with
    | inr hinx =>
      cases h_set_y with
      | inr hiny =>
        apply hinv.id_unique _ _ h_id_eq hinx hiny
      | inl hleq =>
        subst hleq
        apply hsameid _ hinx h_id_eq
    | inl hinx =>
      subst hinx
      cases h_set_y with
      | inr hiny =>
        obtain h := hsameid y hiny (by rw [h_id_eq])
        subst h; simp
      | inl heqy =>
        subst heqy
        simp
