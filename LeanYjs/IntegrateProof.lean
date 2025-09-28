import Mathlib.Tactic.WLOG
import Mathlib.Tactic.ExtractGoal

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
import LeanYjs.YjsArray
import LeanYjs.Integrate.Loop
import LeanYjs.Integrate.LoopInvariant
import LeanYjs.NoCrossOrigin

variable {A : Type}
variable [DecidableEq A]

set_option maxHeartbeats 400000

theorem ok_bind {α β ε : Type} (x : α) (f : α -> Except β ε) :
  (do
    let x <- Except.ok x
    f x) = f x := by
  eq_refl

theorem for_in_list_loop_invariant {α β ε : Type} (ls : List α) (init : β) (body : α -> β -> Except ε (ForInStep β)) (I : Option α -> ForInStep β -> Prop) :
  I ls.head? (ForInStep.yield init) ->
  (∀ x (y : β) res i (hlt : i < ls.length),
    x = ls[i] ->
    I x (ForInStep.yield y) ->
    body x y = Except.ok res ->
    I ls[i + 1]? res) ->
  ∀ res, forIn ls init body = Except.ok res ->
  ∃ x res', res'.value = res ∧ I x res' ∧ (res' = ForInStep.done res ∨ x = none) := by
  intros hinit hbody res hforin
  induction ls generalizing init with
  | nil =>
    cases hforin
    exists none, ForInStep.yield res
    constructor; constructor; constructor <;> try assumption
    simp
  | cons x xs ih =>
    simp at hforin
    generalize heq : body x init = res at hforin
    cases res with
    | error e =>
      cases hforin
    | ok res =>
      rw [ok_bind res] at hforin
      cases res with
      | yield y =>
        apply ih y <;> try assumption
        . apply hbody (i := 0) at heq <;> try first | simp | assumption
          simp at *
          rw [List.head?_eq_getElem?]
          assumption
        . intros x' y' res' xin' hy hbody'
          apply hbody <;> try assumption
          simp
          assumption
      | done y =>
        simp at hforin
        cases hforin
        apply hbody (i := 0) at heq <;> try first | simp | assumption
        simp at heq
        exists xs[0]?, ForInStep.done res
        constructor; constructor; constructor <;> try assumption
        simp

structure InsertOk (arr : Array (YjsItem A)) (newItem : YjsItem A) where
  not_mem : (∀ x ∈ arr, x ≠ newItem)
  origin_in : ArrSet arr.toList newItem.origin
  rightOrigin_in : ArrSet arr.toList newItem.rightOrigin
  origin_lt_rightOrigin : YjsLt' (A := A) newItem.origin newItem.rightOrigin
  reachable_YjsLeq' : (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
      YjsLeq' (A := A) x newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin x)
  id_eq_YjsLeq' : (∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
      x.id = newItem.id →
      YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))

theorem YjsArrInvariant_integrate (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  -> InsertOk arr newItem
  -> integrate newItem arr = Except.ok newArr
  -> ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList := by
  intros harrinv h_InsertOk hintegrate
  obtain ⟨ hneq, horigin, hrorigin, horigin_consistent, hreachable_consistent, hsameid_consistent ⟩ :=
    h_InsertOk
  unfold integrate at hintegrate

  have hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)) := by
    apply arr_set_closed_push _ _ _ horigin hrorigin
    apply harrinv.closed

  have harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList)) := by
    apply item_set_invariant_push
    apply harrinv.item_set_inv
    apply harrinv.closed
    apply horigin_consistent
    apply hreachable_consistent
    apply hsameid_consistent

  generalize heqleft : findPtrIdx newItem.origin arr = leftIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ leftIdx ⟩ := leftIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  generalize heqright : findPtrIdx newItem.rightOrigin arr = rightIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ rightIdx ⟩ := rightIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  have hleftIdxrightIdx : leftIdx < rightIdx := by
    apply YjsLt'_findPtrIdx_lt leftIdx rightIdx newItem.origin newItem.rightOrigin arr harrinv _ (by assumption) (by assumption) heqleft heqright
    assumption

  have hrightIdx : rightIdx ≥ 0 := by
    apply findPtrIdx_ge_minus_1 at heqright
    apply findPtrIdx_ge_minus_1 at heqleft
    omega

  simp at hintegrate

  generalize hloop :
   forIn (m := Except IntegrateError) (ρ := List ℕ) (α := ℕ) (β := MProd ℤ Bool) (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1) ⟨leftIdx + 1, false⟩ (fun offset r => do
      let other ← getElemExcept arr (leftIdx + ↑offset).toNat
      let oLeftIdx ← findPtrIdx other.origin arr
      let oRightIdx ← findPtrIdx other.rightOrigin arr
      if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
        else
          if oLeftIdx = leftIdx then
            if other.id < newItem.id then pure (ForInStep.yield ⟨(leftIdx + ↑offset) ⊔ 0 + 1, false⟩)
            else
              if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
              else pure (ForInStep.yield ⟨r.fst, true⟩)
          else
            if r.snd = false then pure (ForInStep.yield ⟨(leftIdx + ↑offset) ⊔ 0 + 1, r.snd⟩)
            else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = l at hintegrate

  obtain ⟨ _ ⟩ | ⟨ resState ⟩ := l; cases hintegrate
  apply for_in_list_loop_invariant (I := fun x state => loopInv arr newItem leftIdx rightIdx.toNat x state) at hloop
  . -- Here, we prove that the array is still pairwise ordered after the integration.
    -- So, what we need is arr[res.first] < newItem < arr[res.first + 1] (and also, 0 <= res.first <= arr.size)
    simp at hintegrate
    rw [<-hintegrate]
    obtain ⟨ offset, res', hres', hloopInv, hdone ⟩ := hloop
    have h_resState : resState.fst.toNat ≤ arr.size := by
      obtain ⟨ hidx, hdest_current, _, hlt, htbd1, htbd2, hdone ⟩ := hloopInv
      simp at *
      apply findPtrIdx_le_size at heqright
      subst resState
      have h_dest_leq_size : res'.value.fst.toNat ≤ offsetToIndex leftIdx rightIdx offset (isBreak res') := by
        cases res' <;> simp at *
        all_goals rw [Int.max_eq_left hrightIdx] at *
        all_goals omega
      have h_current_leq_size : offsetToIndex leftIdx rightIdx offset (isBreak res') ≤ arr.size := by
        cases offset with
        | none =>
          simp [offsetToIndex]; omega
        | some offset =>
          simp [offsetToIndex]; omega
      omega
    exists resState.fst.toNat
    constructor
    . assumption
    constructor
    . subst newArr; eq_refl
    . apply YjsArrInvariant_insertIdxIfInBounds arr newItem resState.fst.toNat hclosed harrsetinv harrinv h_resState
      . intros hi0
        simp [loopInv] at hloopInv
        obtain ⟨ hidx, hdest_current, _, hlt, htbd1, htbd2, hdone ⟩ := hloopInv
        subst hres'
        obtain hlt  := hlt (res'.value.fst.toNat - 1) (by omega) (by omega)
        assumption
      . have current_lt : offsetToIndex leftIdx rightIdx offset (isBreak res') ≤ arr.size := by
          obtain ⟨ hidx, dest, hdest, hlt, htbd1, htbd2, hdone ⟩ := hloopInv
          apply findPtrIdx_le_size at heqright
          cases offset <;> simp [offsetToIndex] <;> omega
        intros hisize
        apply loopInv_YjsLt' (current := offsetToIndex leftIdx rightIdx offset (isBreak res')) <;> try assumption
        . simp
          rw [max_eq_left hrightIdx]
          assumption
        . simp
          rw [max_eq_left hrightIdx]
        . intros hlt
          simp [loopInv] at hloopInv
          obtain ⟨ hidx, hdest_current, hdestLt, hlt', htbd1, htbd2, hdone' ⟩ := hloopInv
          apply hdone'
          . cases hdone with
            | inl hdone =>
              subst hdone
              simp [isDone]
            | inr hdone =>
              subst hdone
              simp [isDone]
          . rw [max_eq_left hrightIdx]
            simp [extGetElemExcept]
            rw [Array.getElem?_eq_getElem (by omega)]
            simp
            split; omega
            split; omega
            eq_refl
        . subst hres'
          simp
        . subst hres'
          obtain ⟨ hidx, hdest_current, hdestLt, hlt', htbd1, htbd2, hdone' ⟩ := hloopInv
          simp at *
          rw [Int.max_eq_left hrightIdx] at hdest_current
          obtain ⟨ _, _ ⟩ | ⟨ _, _ ⟩ := res' <;> simp at * <;> omega
      . intros
        apply hneq
        assumption
  . -- initial
    simp only [loopInv]
    rw [List.head?_range']
    generalize heq : (if (rightIdx - leftIdx).toNat - 1 = 0 then none else some 1) = offset0
    constructor
    . cases offset0 with
      | none => simp
      | some x =>
        simp
        split at heq <;> cases heq
        constructor
        . simp
        . omega
    constructor
    . simp [offsetToIndex]
      cases offset0 with
      | none =>
        simp [isBreak]
        omega
      | some offset0 =>
        split at heq <;> cases heq
        simp [isBreak]
    constructor
    . simp [offsetToIndex]
      cases offset0 with
      | none =>
        split at heq <;> cases heq
        simp [isBreak]
        have rightIdx_leftIdx : rightIdx = leftIdx + 1 := by
          omega
        subst rightIdx
        intros hdone
        rw [Int.max_eq_left (by omega)]
      | some offset0 =>
        split at heq <;> cases heq
        simp [isBreak]
        have hlt : -1 ≤ leftIdx := by
          apply findPtrIdx_ge_minus_1 at heqleft
          assumption
        omega
    constructor
    . simp
      intros i h_i_lt h_i_lt_size
      obtain ⟨ o, r, id, c ⟩ := newItem
      apply YjsLt'.ltOrigin
      simp [YjsItem.origin] at *

      apply findPtrIdx_leq_YjsLeq' (i := i) _ _ _ harrinv _ heqleft _
      . apply findPtrIdx_getElem _ _ harrinv
      . omega
    constructor
    . simp [offsetToIndex]
      intros i h_i_lt h_i_lt_size
      cases offset0 with
      | none =>
        simp at h_i_lt_size
        split at heq <;> cases heq
        omega
      | some offset0 =>
        simp at h_i_lt_size
        split at heq <;> cases heq
        omega
    constructor
    . simp
    . simp [isDone]
      intros hdone item h_item_eq
      cases offset0 with
      | none =>
        split at heq <;> cases heq
        rw [Int.max_eq_left (by assumption)] at h_item_eq
        simp [offsetToIndex, extGetElemExcept, isBreak] at h_item_eq
        simp [Int.max_eq_left (by omega)] at h_item_eq
        generalize h_getElem_eq : arr[rightIdx.toNat]? = rItem at h_item_eq
        split at h_item_eq; omega
        split at h_item_eq
        cases h_item_eq
        . apply YjsLt'.ltOriginOrder
          . apply OriginLt.lt_last
        . split at h_item_eq
          . simp at *
          . cases rItem <;> cases h_item_eq
            rw [Array.getElem?_eq_some_iff] at h_getElem_eq
            obtain ⟨ _, h_getElem_eq ⟩ := h_getElem_eq
            subst h_getElem_eq
            have heq : arr[rightIdx.toNat] = newItem.rightOrigin := by
              apply findPtrIdx_lt_size_getElem heqright (by omega)
            rw [heq]
            obtain ⟨ o, r, id, c ⟩ := newItem
            apply YjsLt'.ltRightOrigin
            apply YjsLeq'.leqSame
      | some offset0 =>
        simp at hdone
  . intros x state hloop i hlt heq hinv hbody
    rw [List.getElem_range'] at *; simp at heq
    have hlt2: i < ((rightIdx - leftIdx).toNat - 1) := by
      rw [List.length_range'] at hlt; assumption

    subst heq
    generalize hother : getElemExcept arr (leftIdx + ↑(1 + i)).toNat = other at hbody
    obtain ⟨ _ ⟩ | ⟨ other ⟩ := other; cases hbody
    rw [ok_bind] at hbody

    generalize hoLeftIdx : findPtrIdx other.origin arr = oLeftIdx at hbody
    obtain ⟨ _ ⟩ | ⟨ oLeftIdx ⟩ := oLeftIdx; (split at hbody <;> cases hbody)
    rw [ok_bind] at hbody

    generalize hoRightIdx : findPtrIdx other.rightOrigin arr = oRightIdx at hbody
    obtain ⟨ _ ⟩ | ⟨ oRightIdx ⟩ := oRightIdx; (split at hbody <;> cases hbody)
    rw [ok_bind] at hbody

    let next : (ForInStep (MProd ℤ Bool)) :=
      if oLeftIdx < leftIdx then ForInStep.done ⟨state.fst, state.snd⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨(leftIdx + ↑(1 + i)) ⊔ 0 + 1, false⟩
          else
            if oRightIdx = rightIdx then ForInStep.done ⟨state.fst, state.snd⟩
            else ForInStep.yield ⟨state.fst, true⟩
        else
          if state.snd = false then ForInStep.yield ⟨(leftIdx + ↑(1 + i)) ⊔ 0 + 1, state.snd⟩
          else ForInStep.yield ⟨state.fst, state.snd⟩
    have hnext : hloop = next := by
      suffices Except.ok (ε := IntegrateError) hloop = Except.ok next by
        simp at this
        assumption
      rw [<-hbody]
      unfold next
      simp
      obtain ⟨ dest, scanning ⟩ := state
      simp
      cases scanning with
      | true =>
        simp
        (repeat' (split <;> try simp)) <;> try simp [pure, Except.pure]
      | false =>
        simp
        (repeat' (split <;> try simp)) <;> try simp [pure, Except.pure]

    apply loopInv_preserve1
      newItem arr horigin hrorigin horigin_consistent hreachable_consistent hsameid_consistent hneq
      harrinv hclosed harrsetinv leftIdx heqleft rightIdx heqright hleftIdxrightIdx hrightIdx
      state hloop i hlt hlt2 hinv other hother oLeftIdx hoLeftIdx oRightIdx hoRightIdx hnext

theorem insertOk_mono (arr1 arr2 : Array (YjsItem A)) (x : YjsItem A) :
  YjsArrInvariant arr1.toList
  -> YjsArrInvariant arr2.toList
  -> (∀ a, a ∈ arr1 → a ∈ arr2)
  -> (∀ a, a ∈ arr2 → a ∉ arr1 -> a.id ≠ x.id)
  -> InsertOk arr1 x
  -> InsertOk arr2 x := by
  intros harrinv1 harrinv2 h_arr1_subset_arr2 h_id_neq h_InsertOk
  obtain ⟨ hneq, horigin, hrorigin, horigin_consistent, hreachable_consistent, hsameid_consistent ⟩ := h_InsertOk
  constructor <;> try assumption
  . intros y hy_in_arr1 hy_eq_x
    generalize hy_in_arr1_eq : decide (y ∈ arr1) = hy_in_arr1
    cases hy_in_arr1 with
    | true =>
      rw [decide_eq_true_eq] at hy_in_arr1_eq
      apply hneq y hy_in_arr1_eq hy_eq_x
    | false =>
      rw [decide_eq_false_iff_not] at hy_in_arr1_eq
      replace h_id_neq := h_id_neq y hy_in_arr1 hy_in_arr1_eq
      subst x
      contradiction
  . apply subset_ArrSet h_arr1_subset_arr2
    assumption
  . apply subset_ArrSet h_arr1_subset_arr2
    assumption
  . intros y hy_in_arr2 hid_eq
    have hy_in_arr1 : ArrSet arr1.toList y := by
      simp [ArrSet]
      generalize y_in_arr1_eq : decide (y ∈ arr1) = y_in_arr1
      cases y_in_arr1 with
      | true =>
        rw [decide_eq_true_eq] at y_in_arr1_eq
        assumption
      | false =>
        rw [decide_eq_false_iff_not] at y_in_arr1_eq
        simp [ArrSet] at hy_in_arr2
        obtain h_neq := h_id_neq y hy_in_arr2 y_in_arr1_eq
        contradiction
    replace hsameid_consistent := hsameid_consistent y hy_in_arr1 hid_eq
    cases hsameid_consistent with
    | inl hleq =>
      left
      apply hleq
    | inr hleq =>
      right
      apply hleq

theorem insertIdxIfInBounds_insertOk (arr : Array (YjsItem A)) (a x : YjsItem A) :
  YjsArrInvariant arr.toList
  → YjsArrInvariant (arr.insertIdxIfInBounds idx a).toList
  → InsertOk arr x
  → a.id ≠ x.id
  → InsertOk (arr.insertIdxIfInBounds idx a) x := by
  intros harrinv harrinv2 ha_neq_x h_InsertOk
  wlog hidx : idx ≤ arr.size
  case inr =>
    rw [List.insertIdxIfInBounds_toArray]
    rw [List.insertIdx_of_length_lt (l := arr.toList) (by simp only [Array.length_toList]; omega)]
    simp
    assumption
  apply insertOk_mono arr (arr.insertIdxIfInBounds idx a) x harrinv harrinv2
  . intros b hb_in_arr
    rw [List.insertIdxIfInBounds_toArray]
    simp
    rw [List.mem_insertIdx hidx]
    right
    simp
    assumption
  . intros b hb_in_arr2 hb_nin_arr
    rw [List.insertIdxIfInBounds_toArray] at hb_in_arr2
    simp at *
    rw [List.mem_insertIdx hidx] at hb_in_arr2
    simp at *
    cases hb_in_arr2 with
    | inl hidx_eq =>
      subst b
      assumption
    | inr hb_in_arr2 =>
      contradiction
  . assumption

theorem integrate_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id ≠ b.id
  -> InsertOk arr1 a
  -> InsertOk arr1 b
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  intros harrinv hcid_neq_bid h_InsertOk_a h_InsertOk_b hintegrate_a hintegrate_b hintegrate_b' hintegrate_a'

  have ⟨ idx2, h_idx2, arr2_insertIdx, arr2_inv ⟩ : ∃ idx ≤ arr1.size, arr2 = arr1.insertIdxIfInBounds idx a ∧ YjsArrInvariant arr2.toList := by
    apply YjsArrInvariant_integrate a arr1 arr2
    assumption
    assumption
    assumption

  have h_InsertOk_arr2_b : InsertOk arr2 b := by
    subst arr2
    apply insertIdxIfInBounds_insertOk <;> assumption

  have ⟨ idx2', h_idx2', arr2'_insertIdx, arr2'_inv ⟩ : ∃ idx ≤ arr1.size, arr2' = arr1.insertIdxIfInBounds idx b ∧ YjsArrInvariant arr2'.toList := by
    apply YjsArrInvariant_integrate b arr1 arr2'
    assumption
    assumption
    assumption

  have h_InsertOk_arr2'_a : InsertOk arr2' a := by
    subst arr2'
    apply insertIdxIfInBounds_insertOk <;> try assumption
    intros heq
    rw [heq] at hcid_neq_bid
    contradiction

  have ⟨ idx3, h_idx3, arr3_insertIdx,  arr3_inv ⟩ : ∃ idx ≤ arr2.size, arr3 = arr2.insertIdxIfInBounds idx b ∧ YjsArrInvariant arr3.toList := by
    apply YjsArrInvariant_integrate b arr2 arr3
    assumption
    assumption
    assumption

  have ⟨ idx3', h_idx3', arr3'_insertIdx, arr3'_inv ⟩ : ∃ idx ≤ arr2'.size, arr3' = arr2'.insertIdxIfInBounds idx a ∧ YjsArrInvariant arr3'.toList := by
    apply YjsArrInvariant_integrate a arr2' arr3'
    assumption
    assumption
    assumption

  subst arr2 arr2' arr3 arr3'

  rw [<-Array.toList_inj]

  rw [List.insertIdxIfInBounds_toArray] at *; simp at *
  rw [List.insertIdxIfInBounds_toArray] at *; simp at *
  rw [List.insertIdxIfInBounds_toArray] at *; simp at *
  rw [List.insertIdxIfInBounds_toArray] at *; simp at *

  apply same_yjs_set_unique _ _ arr3_inv arr3'_inv

  intros a
  cases a with
  | first =>
    simp [ArrSet]
  | last =>
    simp [ArrSet]
  | itemPtr a =>
    simp [ArrSet]
    rw [List.mem_insertIdx h_idx3, List.mem_insertIdx h_idx3', List.mem_insertIdx h_idx2, List.mem_insertIdx h_idx2']
    simp
    tauto
