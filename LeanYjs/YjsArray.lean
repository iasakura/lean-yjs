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

omit [DecidableEq A] in theorem arr_set_closed_exists_index_for_right_origin :
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

omit [DecidableEq A] in theorem yjs_lt_mono (P Q : ItemSet A) (x y : YjsPtr A) :
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

omit [DecidableEq A] in theorem yjs_lt'_mono :
  ∀ (P Q : ItemSet A) (x y : YjsPtr A),
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  (∀ a, P a -> Q a) ->
  YjsLt' P x y -> YjsLt' Q x y := by
  intros P Q x y hclosedP hinvP hsubset hlt
  obtain ⟨ _, hlt ⟩ := hlt
  constructor
  apply yjs_lt_mono P Q x y hclosedP hinvP hsubset hlt

omit [DecidableEq A] in theorem yjs_leq'_mono :
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

theorem ItemSetInvariant.eq_set {A} (P Q : ItemSet A) :
  IsClosedItemSet P →
  ItemSetInvariant P →
  (∀x, P x ↔ Q x) →
  ItemSetInvariant Q := by
  intros hPclosed hP hiff
  constructor
  . intros o r c id hq
    rw [<-hiff] at *
    apply yjs_lt'_mono P Q o r hPclosed hP (by intros; rw [<-hiff]; assumption)
    apply hP.origin_not_leq <;> assumption
  . intros o r c id x hq hreachable
    rw [<-hiff] at *
    have hor : YjsLeq' P x o ∨ YjsLeq' P r x := by
      apply hP.origin_nearest_reachable <;> assumption
    cases hor with
    | inl hor =>
      left
      apply yjs_leq'_mono P Q x o hPclosed hP (by intros; rw [<-hiff]; assumption) hor
    | inr hor =>
      right
      apply yjs_leq'_mono P Q r x hPclosed hP (by intros; rw [<-hiff]; assumption) hor
  . intros x y hx hy hineq hid
    rw [<-hiff] at *
    have hor : YjsLeq' P (YjsPtr.itemPtr x) y.origin ∨
      YjsLeq' P (YjsPtr.itemPtr y) x.origin ∨
      YjsLeq' P x.rightOrigin (YjsPtr.itemPtr y) ∨ YjsLeq' P y.rightOrigin (YjsPtr.itemPtr x) := by
      apply hP.same_id_ordered <;> assumption
    cases hor with
    | inl hor =>
      left
      apply yjs_leq'_mono P Q (YjsPtr.itemPtr x) y.origin hPclosed hP (by intros; rw [<-hiff]; assumption) hor
    | inr hor =>
      cases hor with
      | inl hor =>
        right
        left
        apply yjs_leq'_mono P Q (YjsPtr.itemPtr y) x.origin hPclosed hP (by intros; rw [<-hiff]; assumption) hor
      | inr hor =>
        cases hor with
        | inl hor =>
          right
          right
          left
          apply yjs_leq'_mono P Q x.rightOrigin (YjsPtr.itemPtr y) hPclosed hP (by intros; rw [<-hiff]; assumption) hor
        | inr hor =>
          right
          right
          right
          apply yjs_leq'_mono P Q y.rightOrigin (YjsPtr.itemPtr x) hPclosed hP (by intros; rw [<-hiff]; assumption) hor

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

omit [DecidableEq A] in theorem same_yjs_set_unique_aux (xs_all ys_all xs ys : List (YjsItem A)) :
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

omit [DecidableEq A] in theorem same_yjs_set_unique (xs ys : List (YjsItem A)) :
  YjsArrInvariant xs ->
  YjsArrInvariant ys ->
  (∀ a, ArrSet xs a ↔ ArrSet ys a) ->
  xs = ys := by
  intros hinv1 hinv2 hseteq
  apply same_yjs_set_unique_aux xs ys xs ys hinv1 hinv2 hseteq
  . exists []
  . exists []
  . apply hseteq

theorem findPtrIdx_item_exists (arr : Array (YjsItem A)) (x : YjsItem A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  ∃j, i.toNat' = some j ∧ arr[j]? = some x := by
  intros hinv hfind
  simp [findPtrIdx] at hfind
  generalize heq : Array.findIdx? (fun i => i = x) arr = idx at hfind
  cases idx <;> cases hfind
  constructor; constructor
  . unfold Int.toNat'
    simp
    eq_refl
  . rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, h1, h2 ⟩ := heq
    rw [Array.getElem?_eq_getElem]
    rw [decide_eq_true_eq] at h1
    simp; assumption

theorem idx_lt_pairwise {α} {P : α -> α -> Prop} (xs : List α) (i j : Nat) :
  List.Pairwise (fun (x y : α) => P x y) xs ->
  i < j ->
  (hlt_x : i < xs.length) ->
  (hlt_y : j < xs.length) ->
  P (xs[i]) (xs[j]) := by
  revert i j
  induction xs with
  | nil =>
    intros i j hpair hlt_ij hlt_x hlt_y
    simp [List.length] at hlt_x
  | cons x xs ih =>
    intros i j hpair hlt_ij hlt_x hlt_y
    simp at *
    cases i <;> cases j <;> try omega
    . simp
      obtain ⟨ h, _ ⟩ := hpair
      apply h; simp
    . simp
      apply ih
      . obtain ⟨ _, hpair ⟩ := hpair
        apply hpair
      . omega

omit [DecidableEq A] in theorem getElem_lt_YjsLt' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i < j) ->
  (hjsize : j < arr.size) ->
  YjsLt' (ArrSet arr.toList) arr[i] arr[j] := by
  intros hinv hij hjsize
  apply idx_lt_pairwise (P := fun x y => YjsLt' (ArrSet arr.toList) (YjsPtr.itemPtr x) y) <;> try assumption
  apply hinv.sorted

omit [DecidableEq A] in theorem getElem_leq_YjsLeq' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i ≤ j) ->
  (hjsize : j < arr.size) ->
  YjsLeq' (ArrSet arr.toList) arr[i] arr[j] := by
  intros hinv hij hjsize
  rw [Nat.le_iff_lt_or_eq] at hij
  cases hij with
  | inl hij =>
    have ⟨ _, hlt ⟩ : YjsLt' (ArrSet arr.toList) arr[i] arr[j] := by
      apply getElem_lt_YjsLt' arr i j hinv hij hjsize
    constructor
    right
    assumption
  | inr heq =>
    subst heq
    exists 0
    apply YjsLeq.leqSame
    . simp [ArrSet]

theorem findPtrIdx_lt_YjsLt' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j ->
  YjsLt' (ArrSet arr.toList) x y := by
  intros hinv hfindx hfindy hlt
  have hinx : ArrSet arr.toList x := by
    cases x with
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
    | itemPtr x =>
      apply findPtrIdx_item_exists arr x hinv at hfindx
      obtain ⟨ j, heq, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      subst hfindx
      simp [ArrSet]
  have hiny : ArrSet arr.toList y := by
    cases y with
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
    | itemPtr y =>
      apply findPtrIdx_item_exists arr y hinv at hfindy
      obtain ⟨ j, heq, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      subst hfindy
      simp [ArrSet]
  cases x with
  | first =>
    cases y with
    | first =>
      cases hfindx
      cases hfindy
      omega
    | last =>
      constructor
      apply YjsLt.ltOriginOrder
      apply hinv.closed.baseFirst
      apply hinv.closed.baseLast
      apply OriginLt.lt_first_last
    | itemPtr y =>
      constructor
      apply YjsLt.ltOriginOrder
      . apply hinv.closed.baseFirst
      . assumption
      . apply OriginLt.lt_first
  | last =>
    cases y with
    | first =>
      cases hfindx
      cases hfindy
      omega
    | last =>
      cases hfindx
      cases hfindy
      omega
    | itemPtr y =>
      cases hfindx
      apply findPtrIdx_item_exists arr y hinv at hfindy
      obtain ⟨ k, heq, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      unfold Int.toNat' at heq
      cases j <;> cases heq
      simp at hlt
      omega
  | itemPtr x =>
    cases y with
    | first =>
      cases hfindy
      apply findPtrIdx_item_exists arr x hinv at hfindx
      obtain ⟨ k, heq, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      cases i <;> cases heq
      simp at hlt
      omega
    | last =>
      constructor
      apply YjsLt.ltOriginOrder
      . assumption
      . apply hinv.closed.baseLast
      . apply OriginLt.lt_last
    | itemPtr y =>
      apply findPtrIdx_item_exists arr x hinv at hfindx
      obtain ⟨ ix, heqx, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      subst hfindx

      apply findPtrIdx_item_exists arr y hinv at hfindy
      obtain ⟨ iy, heqy, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      subst hfindy

      apply idx_lt_pairwise (P := fun x y => YjsLt' (ArrSet arr.toList) (YjsPtr.itemPtr x) y)
      . apply hinv.sorted
      . cases i <;> cases heqx
        cases j <;> cases heqy
        rw [<-Int.ofNat_lt]
        assumption

omit [DecidableEq A] in theorem getElem_YjsLt'_index_lt (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hi_lt : i < arr.size) -> (hj_lt : j < arr.size) ->
  YjsLt' (ArrSet arr.toList) arr[i] arr[j] ->
  i < j := by
  intros hinv hi_lt hj_lt hlt
  have hij_or : i < j ∨ i ≥ j := by
    apply Nat.lt_or_ge
  cases hij_or with
  | inl hij => assumption
  | inr hij =>
    have hleq : YjsLeq' (ArrSet arr.toList) arr[j] arr[i] := by
      apply getElem_leq_YjsLeq' arr j i hinv hij hi_lt
    have _ : False := by
      apply yjs_lt_of_not_leq hinv.item_set_inv _ _ hinv.closed hlt hleq
    contradiction

lemma YjsLt'_findPtrIdx_lt (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList ->
  YjsLt' (ArrSet arr.toList) x y ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j := by
  intros hinv hlt hleft hright
  cases x with
  | last =>
    obtain ⟨ _, hlt ⟩ := hlt
    apply not_last_lt_ptr at hlt
    contradiction
    apply hinv.item_set_inv
  | first =>
    cases y with
    | first =>
      obtain ⟨ _, hlt ⟩ := hlt
      apply not_ptr_lt_first at hlt
      contradiction
      apply hinv.item_set_inv
    | itemPtr r =>
      simp only [findPtrIdx] at hleft hright
      generalize heqright : Array.findIdx? (fun i => decide (i = r)) arr = right at hright
      cases right with
      | none => simp at hright
      | some left =>
        cases hleft
        cases hright
        omega
    | last =>
      simp only [findPtrIdx] at hleft hright
      cases hleft
      cases hright
      omega
  | itemPtr o =>
    cases y with
    | first =>
      obtain ⟨ _, hlt ⟩ := hlt
      apply not_ptr_lt_first at hlt
      contradiction
      apply hinv.item_set_inv
    | last =>
      simp only [findPtrIdx] at hleft hright
      generalize heqleft : Array.findIdx? (fun i => decide (i = o)) arr = left at hleft
      cases left with
      | none => simp at hleft
      | some left =>
        cases hleft
        cases hright
        rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heqleft
        omega
    | itemPtr r =>
      simp only [findPtrIdx] at hleft hright
      generalize heqleft : Array.findIdx? (fun i => decide (i = o)) arr = left at hleft
      generalize heqright : Array.findIdx? (fun i => decide (i = r)) arr = right at hright
      cases left with
      | none => simp at hleft
      | some left =>
        cases right with
        | none => simp at hright
        | some right =>
          rw [Array.findIdx?_eq_some_iff_getElem] at heqleft heqright
          obtain ⟨ _, hgetElemLeft, _ ⟩ := heqleft
          obtain ⟨ _, hgetElemRight, _ ⟩ := heqright
          simp at *
          cases hleft
          cases hright
          simp
          subst hgetElemLeft
          subst hgetElemRight
          apply getElem_YjsLt'_index_lt _ _ _ hinv _ _ hlt

omit [DecidableEq A] in theorem YjsArrayInvariant_lt_neq (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hilt : i < arr.size) ->
  (hjlt : j < arr.size) ->
  i < j ->
  arr[i] ≠ arr[j] := by
  intros hinv hilt hjlt hij
  apply idx_lt_pairwise (P := fun x y => x ≠ y) arr.toList i j hinv.unique hij hilt hjlt

theorem findPtrIdx_getElem (arr : Array (YjsItem A)) (i :  ℕ) :
  YjsArrInvariant arr.toList ->
  (hlt : i < arr.size) ->
  findPtrIdx arr[i] arr = Except.ok ↑i := by
  intros hinv hlt
  simp [findPtrIdx]
  suffices Array.findIdx? (fun x => x = arr[i]) arr = some i by
    rw [this]
    eq_refl
  rw [Array.findIdx?_eq_some_iff_getElem]
  constructor
  constructor
  . simp
  . intros j hij heq
    apply YjsArrayInvariant_lt_neq arr j i hinv (by omega) hlt hij (by simp at heq; assumption)
  . assumption
