import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ActorId
import LeanYjs.ItemOrder
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity
import LeanYjs.AntiSymmetry
import LeanYjs.Integrate

variable {A : Type}
variable [BEq A]

def ArrSet (arr : List (YjsItem A)) : YjsPtr A -> Prop :=
  fun a => match a with
  | YjsPtr.itemPtr item => item ∈ arr
  | YjsPtr.first => True
  | YjsPtr.last => True

def ArrSetClosed (arr : List (YjsItem A)) : Prop :=
  IsClosedItemSet (ArrSet arr)

omit [BEq A] in lemma arr_set_closed_push (arr : List (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr ->
  ArrSet arr item.origin ->
  ArrSet arr item.rightOrigin ->
  ArrSetClosed (item :: arr) := by
  intros hclosed horigin hright
  constructor <;> try simp [ArrSet, IsClosedItemSet]
  . intros o r id c hor
    cases o with
    | itemPtr item' =>
      simp
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
      simp
    | last =>
      simp
  . intros o r id c hor
    cases r with
    | itemPtr item' =>
      simp
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
      simp
    | last =>
      simp

omit [BEq A] in lemma arr_set_item_exists_index (arr arr' : List (YjsItem A)) (item : YjsItem A) :
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

lemma arr_set_closed_exists_index_for_origin :
  ∀ (arr : List (YjsItem A)) (item : YjsItem A),
  ArrSetClosed arr ->
  ArrSet arr item ->
  item.origin = YjsPtr.first ∨ item.origin = YjsPtr.last ∨ ∃ i : Fin arr.length, arr[i] = item.origin := by
  intros arr item hclosed hitem
  obtain ⟨ o, r, id, c ⟩ := item
  apply hclosed.closedLeft at hitem
  simp [YjsItem.origin]
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

lemma arr_set_closed_exists_index_for_right_origin :
  ∀ (arr : List (YjsItem A)) (item : YjsItem A),
  ArrSetClosed arr ->
  ArrSet arr item ->
  item.rightOrigin = YjsPtr.first ∨ item.rightOrigin = YjsPtr.last ∨ ∃ i : Fin arr.length, arr[i] = item.rightOrigin := by
  intros arr item hclosed hitem
  obtain ⟨ o, r, id, c ⟩ := item
  apply hclosed.closedRight at hitem
  simp [YjsItem.rightOrigin]
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

omit [BEq A] in lemma yjs_lt_mono (P Q : ItemSet A) (x y : YjsPtr A) :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  (∀ a, P a -> Q a) ->
  YjsLt P h x y ->
  YjsLt Q h x y := by
  intros hclosedP hinvP hsubset
  intros hlt
  revert hlt x y
  apply Nat.strongRec' (p := fun h => ∀ x y, YjsLt P h x y → YjsLt Q h x y)
  intros n ih x y hlt
  cases hlt with
  | ltOriginOrder _  _ _ _ hlt =>
    apply YjsLt.ltOriginOrder
    . apply hsubset ; assumption
    . apply hsubset ; assumption
    . assumption
  | ltConflict _ _ _ hlt =>
    cases hlt with
    | ltOriginDiff =>
      apply YjsLt.ltConflict
      apply ConflictLt.ltOriginDiff
      all_goals (apply ih; unfold max4; omega)
      all_goals (assumption)
    | ltOriginSame =>
      apply YjsLt.ltConflict
      apply ConflictLt.ltOriginSame <;> try assumption
      all_goals (apply ih; omega)
      all_goals (assumption)
  | ltOrigin _ _ _ _ _ _ _ hlt =>
    apply YjsLt.ltOrigin
    . apply hsubset ; assumption
    . cases hlt with
      | leqSame =>
        apply YjsLeq.leqSame
        apply hsubset ; assumption
      | leqLt =>
        apply YjsLeq.leqLt
        apply ih <;> try assumption
        omega
  | ltRightOrigin _ _ _ _ _ _ _ hlt =>
    apply YjsLt.ltRightOrigin
    . apply hsubset ; assumption
    . cases hlt with
      | leqSame =>
        apply YjsLeq.leqSame
        apply hsubset ; assumption
      | leqLt =>
        apply YjsLeq.leqLt
        apply ih <;> try assumption
        omega

lemma yjs_lt'_mono :
  ∀ (P Q : ItemSet A) (x y : YjsPtr A),
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  (∀ a, P a -> Q a) ->
  YjsLt' P x y -> YjsLt' Q x y := by
  intros P Q x y hclosedP hinvP hsubset hlt
  obtain ⟨ _, hlt ⟩ := hlt
  constructor
  apply yjs_lt_mono P Q x y hclosedP hinvP hsubset hlt

lemma yjs_leq'_mono :
  ∀ (P Q : ItemSet A) (x y : YjsPtr A),
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  (∀ a, P a -> Q a) ->
  YjsLeq' P x y -> YjsLeq' Q x y := by
  intros P Q x y hclosedP hinvP hsubset hleq
  obtain ⟨ _, hleq ⟩ := hleq
  cases hleq with
  | leqSame =>
    exists 0
    apply YjsLeq.leqSame
    apply hsubset; assumption
  | leqLt =>
    constructor
    apply YjsLeq.leqLt
    apply yjs_lt_mono P Q x y hclosedP hinvP hsubset
    assumption

lemma push_subset {A} (arr : List (YjsItem A)) (a : YjsItem A) :
  ∀ x, ArrSet arr x -> ArrSet (a :: arr) x := by
  intros x hin
  unfold ArrSet at *
  simp
  cases x <;> (simp at *)
  right; assumption

lemma reachable_in {A} (arr : List (YjsItem A)) (a : YjsPtr A) :
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

lemma item_set_invariant_push (arr : List (YjsItem A)) (item : YjsItem A) :
  ItemSetInvariant (ArrSet arr) ->
  ArrSetClosed arr ->
  YjsLt' (ArrSet arr) item.origin item.rightOrigin ->
  (∀ x, OriginReachable item x -> YjsLeq' (ArrSet arr) x item.origin ∨ YjsLeq' (ArrSet arr) item.rightOrigin x) ->
  (∀ x : YjsItem A, ArrSet arr x -> x.id = item.id -> YjsLeq' (ArrSet arr) x item.origin ∨ YjsLeq' (ArrSet arr) item.rightOrigin x) ->
  ItemSetInvariant (ArrSet (item :: arr)) := by
  intros hinv hclosed horigin hreach hsameid
  apply ItemSetInvariant.mk
  . intros o r c id hitem
    simp [ArrSet] at hitem
    cases hitem with
    | inr hin =>
      apply hinv.origin_not_leq at hin
      apply yjs_lt'_mono _ _ _ _  hclosed hinv _ hin
      . intros a hlt
        simp [ArrSet] at *
        cases a <;> simp at *
        right; assumption
    | inl heq =>
      subst heq
      simp [YjsItem.origin, YjsItem.rightOrigin] at horigin
      apply yjs_lt'_mono _ _ _ _  hclosed hinv _ horigin
      . intros a hlt
        simp [ArrSet] at *
        cases a <;> simp at *
        right; assumption
  . intros o r c id x hin hreachable
    simp [ArrSet] at hin
    cases hin with
    | inr hin =>
      obtain hor := hinv.origin_nearest_reachable _ _ _ _ _ hin hreachable
      cases hor with
      | inl hor =>
        left
        apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hor
        intros
        apply push_subset; assumption
      | inr hor =>
        right
        apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hor
        intros
        apply push_subset; assumption
    | inl heq =>
      subst heq
      simp [YjsItem.origin, YjsItem.rightOrigin] at *
      cases hreach _ hreachable with
      | inl hor =>
        left
        apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hor
        intros
        apply push_subset; assumption
      | inr hor =>
        right
        apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hor
        intros
        apply push_subset; assumption
  . intros x y hinx hiny hineq hid
    simp [ArrSet] at *
    cases hinx with
    | inr hinx =>
      cases hiny with
      | inr hiny =>
        obtain hor := hinv.same_id_ordered _ _ hinx hiny hineq hid
        cases hor with
        | inl hleq =>
          left
          apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
          apply push_subset
        | inr hleq =>
          right
          cases hleq with
          | inl hleq =>
            left
            apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
            apply push_subset
          | inr hleq =>
            right
            cases hleq with
            | inl hleq =>
              left
              apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
              apply push_subset
            | inr hleq =>
              right
              apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
              apply push_subset
      | inl hleq =>
        subst hleq
        cases hsameid _ hinx hid with
        | inl hleq =>
          left
          apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
          apply push_subset
        | inr hleq =>
          right
          right
          right
          apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
          apply push_subset
    | inl hinx =>
      subst hinx
      cases hiny with
      | inr hiny =>
        cases hsameid _ hiny (by rw [hid]) with
        | inl hleq =>
          right
          left
          apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
          apply push_subset
        | inr hleq =>
          right
          right
          left
          apply yjs_leq'_mono _ _ _ _ hclosed hinv _ hleq
          apply push_subset
      | inl heqy =>
        subst heqy
        cases hineq (refl _)

structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun (x y : YjsItem A) => YjsLt' (ArrSet arr) x y) arr
  unique : List.Pairwise (fun x y => x ≠ y) arr

lemma same_yjs_set_unique_aux (xs_all ys_all xs ys : List (YjsItem A)) :
  YjsArrInvariant xs_all ->
  YjsArrInvariant ys_all ->
  (∀ a, ArrSet xs_all a ↔ ArrSet ys_all a) ->
  (∃ t, t ++ xs = xs_all) ->
  (∃ t, t ++ ys = ys_all) ->
  (∀ x, ArrSet xs x ↔ ArrSet ys x) ->
  xs = ys := by
  intros hinv1 hinv2 hseteq_all hsubset1 hsubset2 hseteq
  obtain ⟨ hclosed1, hinv1, hsort1, huniq1 ⟩ := hinv1
  obtain ⟨ hclosed2, hinv2, hsort2, huniq2 ⟩ := hinv2

  revert ys

  induction xs with
  | nil =>
    intros ys hsubset2 hseteq
    cases ys with
    | nil => eq_refl
    | cons y ys =>
      obtain hitem := hseteq y
      simp [ArrSet] at hitem
  | cons x xs ih =>
    intros ys hsubset2 hseteq
    cases ys with
    | nil =>
      obtain hitem := hseteq x
      simp [ArrSet] at hitem
    | cons y ys =>
      have hmin1 : ∀ a ∈ xs, YjsLt' (ArrSet xs_all) x a := by
        obtain ⟨ t, heq ⟩ := hsubset1
        subst heq
        rw [List.pairwise_append] at hsort1
        obtain ⟨ _, hsort1, _ ⟩ := hsort1
        simp at hsort1
        obtain ⟨ hsort1, _ ⟩ := hsort1
        assumption
      have hmin2 : ∀ a ∈ ys, YjsLt' (ArrSet ys_all) y a := by
        obtain ⟨ t, heq ⟩ := hsubset2
        subst heq
        rw [List.pairwise_append] at hsort2
        obtain ⟨ _, hsort2, _ ⟩ := hsort2
        simp at hsort2
        obtain ⟨ hsort2, _ ⟩ := hsort2
        assumption

      have heq : x = y := by
        have hlt1 : x = y ∨ YjsLt' (ArrSet ys_all) y x := by
          cases yjsItem_decidable_eq A x y with
          | inl heq =>
            left; assumption
          | inr hneq =>
            obtain ⟨ hinx, _ ⟩ := hseteq x
            have hinx : x = y ∨ x ∈ ys:= by
              simp [ArrSet] at hinx
              assumption
            cases hinx with
            | inl heq =>
              left; assumption
            | inr hinx =>
              apply hmin2 at hinx
              obtain ⟨ _, hinx ⟩ := hinx
              right
              constructor
              assumption

        have hlt2 : x = y ∨ YjsLt' (ArrSet xs_all) x y := by
          cases yjsItem_decidable_eq A x y with
          | inl heq =>
            subst heq; left; eq_refl
          | inr hneq =>
            obtain ⟨ _, hinx ⟩ := hseteq y
            have hiny : y = x ∨ y ∈ xs:= by
              simp [ArrSet] at hinx
              assumption
            cases hiny with
            | inl heq =>
              subst heq; left; eq_refl
            | inr hiny =>
              apply hmin1 at hiny
              obtain ⟨ _, hiny ⟩ := hiny
              right
              constructor
              assumption

        cases hlt1 with
        | inl heq =>
          assumption
        | inr hlt1 =>
          cases hlt2 with
          | inl heq =>
            assumption
          | inr hlt2 =>
            have hlt3 : YjsLt' (ArrSet ys_all) x y := by
              apply yjs_lt'_mono (ArrSet xs_all) _ _ _ hclosed1 hinv1 <;> try assumption
              intros a hlt
              rw [<-hseteq_all a]; assumption

            cases yjs_lt_anti_symm hclosed2 hinv2 x y hlt3 hlt1

      subst heq
      congr

      apply ih
      . obtain ⟨ t, heq ⟩ := hsubset1
        subst heq
        exists (t ++ [x])
        simp
      . obtain ⟨ t, heq ⟩ := hsubset2
        subst heq
        exists (t ++ [x])
        simp
      . intros a
        simp [ArrSet] at *
        cases a with
        | first =>
          simp
        | last =>
          simp
        | itemPtr a =>
          specialize hseteq a
          simp at *
          obtain ⟨ t, heq ⟩ := hsubset1
          subst heq
          obtain ⟨ t', heq ⟩ := hsubset2
          subst heq
          rw [List.pairwise_append] at huniq1
          rw [List.pairwise_append] at huniq2
          simp at *
          obtain ⟨ _, ⟨ huniq1, _ ⟩, _ ⟩ := huniq1
          obtain ⟨ _, ⟨ huniq2, _ ⟩ , _ ⟩ := huniq2
          constructor
          . intros hin
            obtain hneq := huniq1 _ hin
            have h : a = x ∨ a ∈ ys := by
              rw [<-hseteq]
              right; assumption
            cases h with
            | inl heq =>
              subst heq
              cases hneq (refl _)
            | inr hin =>
              assumption
          . intros hin
            obtain hneq := huniq2 _ hin
            have h : a = x ∨ a ∈ xs := by
              rw [hseteq]
              right; assumption
            cases h with
            | inl heq =>
              subst heq
              cases hneq (refl _)
            | inr hin =>
              assumption

lemma same_yjs_set_unique (xs ys : List (YjsItem A)) :
  YjsArrInvariant xs ->
  YjsArrInvariant ys ->
  (∀ a, ArrSet xs a ↔ ArrSet ys a) ->
  xs = ys := by
  intros hinv1 hinv2 hseteq
  apply same_yjs_set_unique_aux xs ys xs ys hinv1 hinv2 hseteq
  . exists []
  . exists []
  . apply hseteq

lemma findIdx_lt_YjsLt' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findIdx x arr = Except.ok i ->
  findIdx y arr = Except.ok j ->
  i < j ->
  YjsLt' (ArrSet arr.toList) x y := by
  intros hinv hfindx hfindy hlt
  obtain ⟨ hclosed, hinv, hsort, huniq ⟩ := hinv
  sorry
