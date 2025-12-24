import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity
import LeanYjs.Order.Asymmetry
import LeanYjs.Algorithm.Integrate

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
  obtain ⟨ o, r, id, c, d ⟩ := item
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

theorem ItemSetInvariant.eq_set {A} (P Q : ItemSet A) :
  IsClosedItemSet P →
  ItemSetInvariant P →
  (∀x, P x ↔ Q x) →
  ItemSetInvariant Q := by
  intros hPclosed hP hiff
  constructor
  . intros o r c id d hq
    rw [<-hiff] at *
    apply hP.origin_not_leq <;> assumption
  . intros o r c id d x hq hreachable
    rw [<-hiff] at *
    apply hP.origin_nearest_reachable <;> assumption
  . intros x y h_id_eq h_qx h_qy
    rw [<-hiff] at *
    apply hP.id_unique x y h_id_eq <;> assumption

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
  . intros o r c id d x hin hreachable
    simp [ArrSet] at hin
    cases hin with
    | inr hin =>
      apply hinv.origin_nearest_reachable _ _ _ _ _ _ hin hreachable
    | inl heq =>
      subst heq
      simp [YjsItem.origin, YjsItem.rightOrigin] at *
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

structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun (x y : YjsItem A) => YjsLt' (A := A) x y) arr
  unique : List.Pairwise (fun x y => x ≠ y) arr

theorem same_yjs_set_unique_aux (xs_all ys_all xs ys : List (YjsItem A)) :
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
      have hmin1 : ∀ a ∈ xs, YjsLt' (A := A) x a := by
        obtain ⟨ t, heq ⟩ := hsubset1
        subst heq
        rw [List.pairwise_append] at hsort1
        obtain ⟨ _, hsort1, _ ⟩ := hsort1
        simp at hsort1
        obtain ⟨ hsort1, _ ⟩ := hsort1
        assumption
      have hmin2 : ∀ a ∈ ys, YjsLt' (A := A) y a := by
        obtain ⟨ t, heq ⟩ := hsubset2
        subst heq
        rw [List.pairwise_append] at hsort2
        obtain ⟨ _, hsort2, _ ⟩ := hsort2
        simp at hsort2
        obtain ⟨ hsort2, _ ⟩ := hsort2
        assumption

      have heq : x = y := by
        have hlt1 : x = y ∨ YjsLt' (A := A) y x := by
          cases (inferInstance : Decidable (x = y)) with
          | isTrue heq =>
            left; assumption
          | isFalse hneq =>
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

        have hlt2 : x = y ∨ YjsLt' (A := A) x y := by
          cases (inferInstance : Decidable (x = y)) with
          | isTrue heq =>
            subst heq; left; eq_refl
          | isFalse hneq =>
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
            obtain ⟨ tx, heq1 ⟩ := hsubset1
            obtain ⟨ ty, heq2 ⟩ := hsubset2
            subst heq1 heq2
            cases yjs_lt_asymm hclosed2 hinv2 x y (by rw [<-hseteq_all]; simp [ArrSet]) (by simp [ArrSet]) hlt2 hlt1

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

theorem same_yjs_set_unique (xs ys : List (YjsItem A)) :
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
  findPtrIdx x arr = Except.ok i ->
  ∃j, i.toNat? = some j ∧ arr[j]? = some x := by
  intros hfind
  simp [findPtrIdx] at hfind
  generalize heq : Array.findIdx? (fun i => i = x) arr = idx at hfind
  cases idx <;> cases hfind
  constructor; constructor
  . unfold Int.toNat?
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
  YjsLt' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  apply idx_lt_pairwise (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y) <;> try assumption
  apply hinv.sorted

omit [DecidableEq A] in theorem getElem_leq_YjsLeq' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i ≤ j) ->
  (hjsize : j < arr.size) ->
  YjsLeq' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  rw [Nat.le_iff_lt_or_eq] at hij
  cases hij with
  | inl hij =>
    have ⟨ _, hlt ⟩ : YjsLt' (A := A) arr[i] arr[j] := by
      apply getElem_lt_YjsLt' arr i j hinv hij hjsize
    constructor
    right
    assumption
  | inr heq =>
    subst heq
    exists 0
    apply YjsLeq.leqSame

theorem findPtrIdx_lt_YjsLt' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j ->
  YjsLt' x y := by
  intros hinv hfindx hfindy hlt
  have hinx : ArrSet arr.toList x := by
    cases x with
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
    | itemPtr x =>
      apply findPtrIdx_item_exists arr x at hfindx
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
      apply findPtrIdx_item_exists arr y at hfindy
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
      apply OriginLt.lt_first_last
    | itemPtr y =>
      constructor
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first
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
      apply findPtrIdx_item_exists arr y at hfindy
      obtain ⟨ k, heq, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      unfold Int.toNat? at heq
      cases j <;> cases heq
      simp at hlt
      omega
  | itemPtr x =>
    cases y with
    | first =>
      cases hfindy
      apply findPtrIdx_item_exists arr x at hfindx
      obtain ⟨ k, heq, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      cases i <;> cases heq
      simp at hlt
      omega
    | last =>
      constructor
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_last
    | itemPtr y =>
      apply findPtrIdx_item_exists arr x at hfindx
      obtain ⟨ ix, heqx, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      subst hfindx

      apply findPtrIdx_item_exists arr y at hfindy
      obtain ⟨ iy, heqy, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      subst hfindy

      apply idx_lt_pairwise (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y)
      . apply hinv.sorted
      . cases i <;> cases heqx
        cases j <;> cases heqy
        rw [<-Int.ofNat_lt]
        assumption

theorem findPtrIdx_eq_ok_inj {arr : Array (YjsItem A)} (x y : YjsPtr A) :
  findPtrIdx x arr = Except.ok i →
  findPtrIdx y arr = Except.ok i →
   x = y := by
  intros heq_x heq_y
  cases x with
  | first =>
    cases y with
    | first =>
      simp
    | last =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
  | last =>
    cases y with
    | first =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | last =>
      simp
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
  | itemPtr x =>
    cases y with
    | first =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
    | last =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
    | itemPtr y =>
      simp [findPtrIdx] at heq_x heq_y
      generalize heq_x :  Array.findIdx? (fun i => decide (i = x)) arr = idxX at *
      generalize heq_y :  Array.findIdx? (fun i => decide (i = y)) arr = idxY at *
      cases idxX <;> cases heq_x
      cases idxY <;> cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_y
      obtain ⟨ hlt_x, heq_x ⟩ := heq_x
      obtain ⟨ hlt_y, heq_y ⟩ := heq_y
      rw [Array.findIdx_eq hlt_x] at heq_x
      rw [Array.findIdx_eq hlt_y] at heq_y
      simp at heq_x heq_y
      obtain ⟨ heq_x, _ ⟩ := heq_x
      obtain ⟨ heq_y, _ ⟩ := heq_y
      subst x y
      simp

theorem findPtrIdx_leq_YjsLeq' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i ≤ j ->
  YjsLeq' x y := by
  intros hinv hfindx hfindy hleq
  have hor : i < j ∨ i = j := by omega
  cases hor with
  | inl hor =>
    apply YjsLeq'.leqLt
    apply findPtrIdx_lt_YjsLt' _ _ _ hinv hfindx hfindy hor
  | inr heq =>
    subst heq
    have heq : x = y := by
      apply findPtrIdx_eq_ok_inj x y hfindx hfindy
    subst x
    apply YjsLeq'.leqSame

theorem getElem_YjsLt'_index_lt (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hi_lt : i < arr.size) -> (hj_lt : j < arr.size) ->
  YjsLt' (A := A) arr[i] arr[j] ->
  i < j := by
  intros hinv hi_lt hj_lt hlt
  have hij_or : i < j ∨ i ≥ j := by
    apply Nat.lt_or_ge
  cases hij_or with
  | inl hij => assumption
  | inr hij =>
    have hleq : YjsLeq' (A := A) arr[j] arr[i] := by
      apply getElem_leq_YjsLeq' arr j i hinv hij hi_lt
    by_contra
    apply yjs_lt_of_not_leq hinv.item_set_inv _ _ hinv.closed _ _ hlt hleq
    simp [ArrSet]
    simp [ArrSet]

lemma YjsLt'_findPtrIdx_lt (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList ->
  ArrSet arr.toList x -> ArrSet arr.toList y ->
  YjsLt' (A := A) x y ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j := by
  intros hinv harrx harry hlt hleft hright
  cases x with
  | last =>
    obtain ⟨ _, hlt ⟩ := hlt
    by_contra
    apply not_last_lt_ptr hinv.closed hinv.item_set_inv at hlt <;> assumption
  | first =>
    cases y with
    | first =>
      obtain ⟨ _, hlt ⟩ := hlt
      by_contra
      apply not_ptr_lt_first hinv.closed hinv.item_set_inv at hlt <;> assumption
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
      by_contra
      apply not_ptr_lt_first hinv.closed hinv.item_set_inv at hlt <;> assumption
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

theorem YjsLeq'_findPtrIdx_leq (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList ->
  ArrSet arr.toList x -> ArrSet arr.toList y ->
  YjsLeq' x y ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i ≤ j := by
  intros hinv harrx harry hleq hleft hright
  apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
  cases hleq with
  | inl heq =>
    subst heq
    rw [hleft] at hright
    cases hright
    simp
  | inr hlt =>
    suffices h : i < j by omega
    apply YjsLt'_findPtrIdx_lt _ _ _ _ _ hinv harrx harry hlt hleft hright

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


theorem findPtrIdx_ge_minus_1 {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≥ -1 := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    simp
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      omega

theorem findPtrIdx_le_size {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≤ arr.size := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    simp
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      obtain ⟨ _, _ ⟩ := heq
      simp
      omega

theorem findPtrIdx_origin_leq_newItem_YjsLt' {arr : Array (YjsItem A)} {other newItem : YjsItem A} :
  (∀i, i ∈ arr → i ∈ ls) ->
  (newItem ∈ ls) ->
  (other ∈ ls) ->
  (hclosed : IsClosedItemSet $ ArrSet ls) ->
  (harrsetinv : ItemSetInvariant $ ArrSet ls) ->
  (harrinv : YjsArrInvariant arr.toList) ->
  YjsArrInvariant arr.toList ->
  findPtrIdx newItem.origin arr = Except.ok leftIdx ->
  findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx ->
  findPtrIdx other.origin arr = Except.ok oLeftIdx ->
  findPtrIdx other.rightOrigin arr = Except.ok oReftIdx ->
  YjsLt' newItem.origin other ->
  YjsLt' other newItem.rightOrigin ->
  leftIdx ≤ oLeftIdx ->
  (leftIdx = oLeftIdx -> other.id < newItem.id) ->
  YjsLt' other.origin newItem ->
  YjsLt' (A := A) other newItem := by
  intros hsubset hnewItem_in_ls hother_in_ls hclosed harrsetinv harrinv hinv hfindLeft hfindRight hfindOLeft hfindORight h_newItem_origin_lt_other h_origin_lt_newItem_rightOrigin heq_oleft heq_oleft_eq hlt_oleft_newItem
  have hor : YjsLeq' other.rightOrigin newItem ∨ YjsLt' newItem other.rightOrigin := by
    apply yjs_lt_total (P := ArrSet $ ls) <;> try assumption
    . obtain ⟨ o, r, id, c, d ⟩ := other
      apply hclosed.closedRight o r id c
      simp [ArrSet]
      assumption
  cases hor with
  | inl hle =>
    obtain ⟨ _, hle ⟩ := hle
    obtain ⟨ o, r, id, c, d ⟩ := other
    constructor
    apply YjsLt.ltRightOrigin
    assumption
  | inr hlt =>
    have hor : leftIdx < oLeftIdx ∨ leftIdx = oLeftIdx := by
      omega
    cases hor with
    | inl hlt_left =>
      have heq_origin : YjsLt' newItem.origin other.origin := by
        apply findPtrIdx_lt_YjsLt' <;> assumption
      obtain ⟨ o, r, id, c, d ⟩ := other
      obtain ⟨ no, nr, nid, nc, nd ⟩ := newItem
      simp [YjsItem.origin, YjsItem.rightOrigin] at heq_origin hlt
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginDiff <;> try assumption
    | inr heq_origin =>
      subst oLeftIdx
      have heq_origin : newItem.origin = other.origin := by
        apply findPtrIdx_eq_ok_inj _ _ hfindLeft hfindOLeft
      obtain ⟨ o, r, id, c, d ⟩ := other
      obtain ⟨ no, nr, nid, nc, nd ⟩ := newItem
      simp [YjsItem.origin, YjsItem.rightOrigin, YjsItem.id] at heq_origin heq_oleft_eq hlt
      subst no
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginSame <;> try assumption

theorem findPtrIdx_ArrSet {A : Type} [DecidableEq A] {arr : Array (YjsItem A)} {p : YjsPtr A} {idx : ℤ} :
  findPtrIdx p arr = Except.ok idx →
  ArrSet arr.toList p := by
  intros hfind
  unfold findPtrIdx at hfind
  cases p with
  | first =>
    simp at hfind
    cases hfind
    simp [ArrSet]
  | last =>
    simp at hfind
    cases hfind
    simp [ArrSet]
  | itemPtr p =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = p)) arr = idxOpt at hfind
    cases idxOpt <;> cases hfind
    rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, heq, _ ⟩ := heq
    simp at heq
    subst p
    simp [ArrSet]

theorem findPtrIdx_insert_some {arr other} {newItem : YjsItem A} :
  YjsArrInvariant (arr.insertIdxIfInBounds i newItem).toList
  → findPtrIdx other arr = Except.ok idx
  → findPtrIdx other (arr.insertIdxIfInBounds i newItem) = if i ≤ idx then Except.ok (idx + 1) else Except.ok idx := by
  intros h_inv h_findPtrIdx_other
  cases other with
  | first =>
    simp [findPtrIdx] at *
    cases h_findPtrIdx_other
    split; omega
    eq_refl
  | last =>
    simp [findPtrIdx] at *
    cases h_findPtrIdx_other
    simp [Array.insertIdxIfInBounds]
    split
    . simp; eq_refl
    . eq_refl
  | itemPtr p =>
    apply findPtrIdx_item_exists at h_findPtrIdx_other
    obtain ⟨ j, h_j, h_getElem_eq ⟩ := h_findPtrIdx_other
    have h_j_lt : j < arr.size := by
      rw [Array.getElem?_eq_some_iff] at h_getElem_eq
      obtain ⟨ h, h_eq ⟩ := h_getElem_eq
      assumption
    have h_idx_eq_j : idx = j := by
      cases idx with
      | negSucc n =>
        simp [Int.toNat?] at *
      | ofNat n =>
        simp [Int.toNat?] at *
        omega

    subst idx
    simp

    have h_lt : (if i ≤ j then j + 1 else j) < (arr.insertIdxIfInBounds i newItem).size := by
      simp [Array.insertIdxIfInBounds]
      split_ifs
      . simp
        omega
      . omega
      . simp
        omega
      . omega

    have h_getElem : (arr.insertIdxIfInBounds i newItem)[if i ≤ j then j + 1 else j] = p := by
      rw [Array.getElem_eq_iff]
      simp [Array.insertIdxIfInBounds] at *
      split_ifs
      . rw [Array.getElem?_insertIdx]
        split_ifs <;> try omega
        simp; assumption
      . rw [Array.getElem?_insertIdx]
        split_ifs <;> try omega
      . omega
      . omega

    rw [<-h_getElem]
    rw [findPtrIdx_getElem _ _ h_inv]
    split_ifs <;> eq_refl
