import Mathlib.Tactic.ApplyAt

import LeanYjs.Item
import LeanYjs.ItemSet

variable {A : Type}

def ArrSet (arr : List (YjsItem A)) : YjsPtr A -> Prop :=
  fun a => match a with
  | YjsPtr.itemPtr item => item ∈ arr
  | YjsPtr.first => True
  | YjsPtr.last => True

def ArrSetClosed (arr : List (YjsItem A)) : Prop :=
  IsClosedItemSet (ArrSet arr)

theorem subset_ArrSet {arr1 arr2 : Array (YjsItem A)} {a : YjsPtr A}:
  (∀ a, a ∈ arr1 -> a ∈ arr2)
  -> ArrSet arr1.toList a
  -> ArrSet arr2.toList a := by
  intros h_subset h_arr1
  simp [ArrSet] at *
  cases a with
  | first => simp
  | last => simp
  | itemPtr a =>
    simp at *
    apply h_subset a h_arr1

theorem arr_set_closed_push (arr : List (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr ->
  ArrSet arr item.origin ->
  ArrSet arr item.rightOrigin ->
  ArrSetClosed (item :: arr) := by
  intros hclosed horigin hright
  constructor <;> try simp [ArrSet]
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

theorem arr_set_item_exists_index (arr arr' : List (YjsItem A)) (item : YjsItem A) :
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

theorem arr_set_closed_exists_index_for_origin :
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

theorem arr_set_closed_exists_index_for_right_origin :
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
