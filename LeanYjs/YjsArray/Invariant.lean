import LeanYjs.ListLemmas
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.ItemOrder
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity
import LeanYjs.Asymmetry
import LeanYjs.Integrate
import LeanYjs.YjsArray.ArrSet

structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun (x y : YjsItem A) => YjsLt' (A := A) x y) arr
  unique : List.Pairwise (fun x y => x ≠ y) arr

section YjsArrInvariant

variable [DecidableEq A]

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
          by_cases heq : x = y
          . left; assumption
          . obtain ⟨ hinx, _ ⟩ := hseteq x
            have hinx : x = y ∨ x ∈ ys := by
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
          by_cases heq : x = y
          . subst heq; left; eq_refl
          . obtain ⟨ _, hinx ⟩ := hseteq y
            have hiny : y = x ∨ y ∈ xs := by
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

end YjsArrInvariant

theorem insertIdxIfInBounds_mem {arr : Array (YjsItem A)} :
  i ≤ arr.size →
  (ArrSet (newItem :: arr.toList) x ↔ ArrSet (arr.insertIdxIfInBounds i newItem).toList x) := by
  intros hlt
  simp [ArrSet]
  cases x <;> try simp
  rw [List.insertIdxIfInBounds_toArray]
  simp
  rw [List.mem_insertIdx]
  simp
  assumption

theorem YjsArrInvariant_insertIdxIfInBounds [DecidableEq A] (arr : Array (YjsItem A)) (newItem : YjsItem A) (i : ℕ) :
  IsClosedItemSet (ArrSet $ newItem :: arr.toList)
  -> ItemSetInvariant (ArrSet $ newItem :: arr.toList)
  -> YjsArrInvariant arr.toList
  -> (hisize : i ≤ arr.size)
  -> ((hizero : 0 < i) -> YjsLt' (A := A) arr[i - 1] newItem)
  -> ((hisize : i < arr.size) -> YjsLt' (A := A) newItem arr[i])
  -> (∀ a, a ∈ arr -> a ≠ newItem)
  -> YjsArrInvariant (arr.insertIdxIfInBounds i newItem).toList := by
  intros hclosed hinv harrinv hisize hlt1 hlt2 hneq
  obtain ⟨ _, _, hsorted, hunique ⟩ := harrinv
  have heqset : ∀ x, ArrSet (newItem :: arr.toList) x ↔ ArrSet (List.insertIdx arr.toList i newItem) x := by
    intros x
    simp only [ArrSet]
    cases x with
    | first => simp
    | last => simp
    | itemPtr x =>
      simp
      rw [List.mem_insertIdx hisize]
      simp

  have heqset' : ∀ x, ArrSet (newItem :: arr.toList) x ↔ ArrSet (arr.insertIdxIfInBounds i newItem).toList x := by
    intros
    rw [List.insertIdxIfInBounds_toArray]
    simp
    rw [heqset]

  have hsubset a : (ArrSet arr.toList) a -> (ArrSet (List.insertIdx arr.toList i newItem)) a := by
    intros hmem
    cases a with
    | first => simp [ArrSet]
    | last => simp [ArrSet]
    | itemPtr a =>
      simp [ArrSet]
      rw [List.mem_insertIdx hisize]
      right
      assumption

  have hsubset' : ∀ x, ArrSet arr.toList x -> ArrSet (newItem :: arr.toList) x := by
    intros a hmem
    simp [ArrSet] at *
    cases a <;> simp
    right
    assumption

  apply YjsArrInvariant.mk
  . apply IsClosedItemSet.eq_set (P := ArrSet $ newItem :: arr.toList) _ hclosed heqset'
  . apply ItemSetInvariant.eq_set (P := ArrSet $ newItem :: arr.toList) _ hclosed hinv heqset'
  . rw [List.insertIdxIfInBounds_toArray]
    simp
    apply List.Pairwise_insertIdx
    . apply List.Pairwise_weaken (R := fun (a b : YjsItem A) => YjsLt' (A := A) a b) <;> try assumption
      intros
      assumption
    . intros j hji
      apply yjs_leq'_p_trans1 (inv := hinv) (y := arr[i - 1]) <;> try assumption
      . simp [ArrSet]
      . simp [ArrSet]
      . simp [ArrSet]
      . rw [List.pairwise_iff_getElem] at hsorted
        cases Nat.lt_or_ge j (i - 1) with
        | inl hj_lt =>
          have hlt : YjsLt' (A := A) (YjsPtr.itemPtr arr[j]) (YjsPtr.itemPtr arr[i - 1]) := by
            apply hsorted; assumption
          obtain ⟨ k, hlt ⟩ := hlt
          simp at *
          -- We can't use `exists k + 1` because it causes error in Lean4.18-rc1.
          -- This `apply` generates a seemingly unnecesarry goal here.
          apply Exists.intro (k + 1)
          apply YjsLeq.leqLt
          assumption
          -- Here, we need to prove the following:
          --- List.Pairwise (fun x y => x ≠ y) arr.toList →
          -- (∀ (x : YjsPtr A), ArrSet (newItem :: arr.toList) x ↔ ArrSet (List.insertIdx i newItem arr.toList) x) →
          --   (∀ (x : YjsPtr A), ArrSet (newItem :: arr.toList) x ↔ ArrSet (arr.insertIdxIfInBounds i newItem).toList x) →
          --     (∀ (a : YjsPtr A), ArrSet arr.toList a → ArrSet (List.insertIdx i newItem arr.toList) a) →
          --       (∀ (x : YjsPtr A), ArrSet arr.toList x → ArrSet (newItem :: arr.toList) x) → i ≤ arr.toList.length
          intros
          simp; omega
        | inr hj_ge =>
          have heq : j = i - 1 := by omega
          subst heq
          simp
          exists 0
          apply YjsLeq.leqSame
      . apply hlt1; omega
    . intros j hij hjlen
      simp at hjlen
      apply yjs_leq'_p_trans2 (inv := hinv) (y := YjsPtr.itemPtr arr[i]) <;> try assumption
      . simp [ArrSet]
      . simp [ArrSet]
      . simp [ArrSet]
      . apply hlt2
      . rw [List.pairwise_iff_getElem] at hsorted
        cases Nat.lt_or_ge i j with
        | inl hj_lt =>
          have hlt : YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr arr[j]) := by
            apply hsorted; try assumption
          obtain ⟨ h, hlt' ⟩ := hlt
          exists h + 1; right; assumption
        | inr hj_ge =>
          have heq : j = i := by omega
          subst heq
          simp
          exists 0; apply YjsLeq.leqSame
  . rw [List.insertIdxIfInBounds_toArray]
    apply List.Pairwise_insertIdx <;> try assumption
    . intros
      apply hneq
      simp
    . intros j hij hlt heq
      apply hneq arr[j]
      simp
      subst heq
      simp

theorem item_set_invariant_push (item : YjsItem A) :
  ItemSetInvariant (ArrSet arr) →
  ArrSetClosed arr →
  YjsLt' item.origin item.rightOrigin →
  (∀ x, OriginReachable item x → YjsLeq' x item.origin ∨ YjsLeq' item.rightOrigin x) →
  (∀ x : YjsItem A, ArrSet arr x → x.id = item.id → YjsLeq' x item.origin ∨ YjsLeq' item.rightOrigin x) →
  ItemSetInvariant (ArrSet (item :: arr)) := by
  intros hinv hclosed horigin hreach hsameid
  constructor
  · intros o r c id hitem
    simp [ArrSet] at hitem
    cases hitem with
    | inr hin =>
      apply hinv.origin_not_leq at hin
      assumption
    | inl heq =>
      subst heq
      assumption
  · intros o r c id x hin hreachable
    simp [ArrSet] at hin
    cases hin with
    | inr hin =>
      apply hinv.origin_nearest_reachable _ _ _ _ _ hin hreachable
    | inl heq =>
      subst heq
      simp [YjsItem.origin, YjsItem.rightOrigin] at *
      apply hreach _ hreachable
  · intros x y hinx hiny hineq hid
    simp [ArrSet] at *
    cases hinx with
    | inr hinx =>
      cases hiny with
      | inr hiny =>
        apply hinv.same_id_ordered _ _ hinx hiny hineq hid
      | inl hleq =>
        subst hleq
        cases hsameid _ hinx hid with
        | inl hleq =>
          left; assumption
        | inr hleq =>
          right; right; right; assumption
    | inl hinx =>
      subst hinx
      cases hiny with
      | inr hiny =>
        cases hsameid _ hiny (by rw [hid]) with
        | inl hleq =>
          right; left; assumption
        | inr hleq =>
          right; right; left; assumption
      | inl heqy =>
        subst heqy
        cases hineq (rfl)
