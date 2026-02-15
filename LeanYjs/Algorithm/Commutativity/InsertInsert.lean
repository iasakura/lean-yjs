import Mathlib.Tactic.WLOG
import Mathlib.Tactic.ExtractGoal

import LeanYjs.Algorithm.Invariant.Lemmas
import LeanYjs.ListLemmas
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity
import LeanYjs.Order.Asymmetry
import LeanYjs.Order.NoCrossOrigin
import LeanYjs.Algorithm.Basic
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Lemmas
import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Invariant.Lemmas
import LeanYjs.Algorithm.Invariant.Basic
import LeanYjs.Algorithm.Invariant.YjsArray

variable {A : Type}
variable [DecidableEq A]

set_option maxHeartbeats 400000

omit [DecidableEq A] in theorem subset_ArrSet {arr1 arr2 : Array (YjsItem A)} {a : YjsPtr A}:
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

theorem uniqueId_mono (arr1 arr2 : Array (YjsItem A)) (x : YjsItem A) :
  YjsArrInvariant arr1.toList
  -> YjsArrInvariant arr2.toList
  -> (∀ a, a ∈ arr1 → a ∈ arr2)
  -> (∀ a, a ∈ arr2 → a ∉ arr1 -> a.id.clientId ≠ x.id.clientId)
  -> maximalId x arr1
  -> maximalId x arr2 := by
  intros harrinv1 harrinv2 h_arr1_subset_arr2 h_id_neq h_UniqueId
  intros y hy_in_arr2 hid_eq
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
  replace h_UniqueId := h_UniqueId y hy_in_arr1 hid_eq
  assumption

theorem insertIdxIfInBounds_UniqueId (arr : Array (YjsItem A)) (a x : YjsItem A) :
  YjsArrInvariant arr.toList
  → YjsArrInvariant (arr.insertIdxIfInBounds idx a).toList
  → maximalId x arr
  → a.id.clientId ≠ x.id.clientId
  → maximalId x (arr.insertIdxIfInBounds idx a) := by
  intros harrinv harrinv2 ha_neq_x h_UniqueId
  wlog hidx : idx ≤ arr.size
  case inr =>
    rw [List.insertIdxIfInBounds_toArray]
    rw [List.insertIdx_of_length_lt (l := arr.toList) (by simp only [Array.length_toList]; omega)]
    simp
    assumption
  apply uniqueId_mono arr (arr.insertIdxIfInBounds idx a) x harrinv harrinv2
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

theorem IntegrateInput.toItem_insertIfInBounds {arr : Array (YjsItem A)} (input : IntegrateInput A) (a : YjsItem A) :
  input.toItem arr = Except.ok item →
  uniqueId (arr.insertIdxIfInBounds idx a).toList →
  input.toItem (arr.insertIdxIfInBounds idx a) = Except.ok item := by
  intros h_input_def h_uniqueId
  have h_uniqueId_arr : uniqueId arr.toList := by
    simp [uniqueId] at *
    simp [Array.insertIdxIfInBounds] at *
    rw [List.pairwise_iff_getElem] at *
    intros i j hi hj hij
    by_cases hi_idx : idx ≤ arr.size
    . simp [hi_idx, List.length_insertIdx] at *
      specialize h_uniqueId (if i < idx then i else i + 1) (if j < idx then j else j + 1)
      grind
    . simp at *
      specialize h_uniqueId i j
      grind
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_uniqueId_arr] at h_input_def
  obtain ⟨ o, r, id, c, h_item_eq, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_input_def
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_uniqueId]
  use o, r, id, c
  refine ⟨ h_item_eq, ?_, ?_, h_id, h_content ⟩
  . simp [isLeftIdPtr] at *
    cases heq : input.originId with
    | none => simp [heq] at *; assumption
    | some originId =>
      simp [heq] at *
      obtain ⟨ item, heq1, heq2 ⟩ := h_origin
      use item
      refine ⟨ heq1, ?_ ⟩
      rw [Array.find?_eq_some_iff_getElem] at *
      simp at *
      obtain ⟨ hid, i, hilt, hgetElem, heq_idx ⟩ := heq2
      refine ⟨ hid, if i < idx then i else i + 1, ?_, ?_, ?_ ⟩
      . simp [Array.insertIdxIfInBounds]
        grind [Array.size_insertIdx]
      . simp [Array.insertIdxIfInBounds]
        grind
      . simp [Array.insertIdxIfInBounds]
        grind [uniqueId_insertIdxIfInBounds_id_neq]
  . simp [isRightIdPtr] at *
    cases heq : input.rightOriginId with
    | none => simp [heq] at *; assumption
    | some rightOriginId =>
      simp [heq] at *
      obtain ⟨ item, heq1, heq2 ⟩ := h_rightOrigin
      use item
      refine ⟨ heq1, ?_ ⟩
      rw [Array.find?_eq_some_iff_getElem] at *
      simp at *
      obtain ⟨ hid, i, hilt, hgetElem, heq_idx ⟩ := heq2
      refine ⟨ hid, if i < idx then i else i + 1, ?_, ?_, ?_ ⟩
      . simp [Array.insertIdxIfInBounds]
        grind [Array.size_insertIdx]
      . simp [Array.insertIdxIfInBounds]
        grind
      . simp [Array.insertIdxIfInBounds]
        grind [uniqueId_insertIdxIfInBounds_id_neq]

theorem integrate_ok_commutative (a b : IntegrateInput A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  → a.toItem arr1 = Except.ok aItem
  → b.toItem arr1 = Except.ok bItem
  → a.id.clientId ≠ b.id.clientId
  → aItem.isValid
  → bItem.isValid
  → integrateSafe a arr1 = Except.ok arr2
  → integrateSafe b arr2 = Except.ok arr3
  → integrateSafe b arr1 = Except.ok arr2'
  → integrateSafe a arr2' = Except.ok arr3'
  → arr3 = arr3' := by
  intros harrinv h_aItem_def h_bItem_def hcid_neq_bid h_a_valid h_b_valid hintegrate_a hintegrate_b hintegrate_b' hintegrate_a'

  simp [integrateSafe] at *
  split_ifs at *
  rw [<-isClockSafe_maximalId harrinv.unique h_aItem_def] at *
  rw [<-isClockSafe_maximalId harrinv.unique h_bItem_def] at *

  have h_aItem_tmp := h_aItem_def
  have h_bItem_tmp := h_bItem_def

  rw [IntegrateInput.toItem_ok_iff _ _ _ harrinv.unique] at h_aItem_tmp h_bItem_tmp

  obtain ⟨ ao, ar, aid, acontent, haItem_eq, haorigin, harorigin, haid, hac ⟩ := h_aItem_tmp
  obtain ⟨ bo, br, bid, bcontent, hbItem_eq, hborigin, hbrorigin, hbid, hbc ⟩ := h_bItem_tmp

  have ⟨ idx2, h_idx2, arr2_insertIdx, arr2_inv ⟩ : ∃ idx ≤ arr1.size, arr2 = arr1.insertIdxIfInBounds idx aItem ∧ YjsArrInvariant arr2.toList := by
    grind only [YjsArrInvariant_integrate]

  have h_UniqueId_arr2_b : maximalId bItem arr2 := by
    grind only [insertIdxIfInBounds_UniqueId]

  have ⟨ idx2', h_idx2', arr2'_insertIdx, arr2'_inv ⟩ : ∃ idx ≤ arr1.size, arr2' = arr1.insertIdxIfInBounds idx bItem ∧ YjsArrInvariant arr2'.toList := by
    grind only [YjsArrInvariant_integrate]

  have h_UniqueId_arr2'_a : maximalId aItem arr2' := by
    grind only [insertIdxIfInBounds_UniqueId]

  have ⟨ idx3, h_idx3, arr3_insertIdx,  arr3_inv ⟩ : ∃ idx ≤ arr2.size, arr3 = arr2.insertIdxIfInBounds idx bItem ∧ YjsArrInvariant arr3.toList := by
    apply YjsArrInvariant_integrate b arr2 arr3 <;> try assumption
    grind [IntegrateInput.toItem_insertIfInBounds, YjsArrInvariant]

  have ⟨ idx3', h_idx3', arr3'_insertIdx, arr3'_inv ⟩ : ∃ idx ≤ arr2'.size, arr3' = arr2'.insertIdxIfInBounds idx aItem ∧ YjsArrInvariant arr3'.toList := by
    apply YjsArrInvariant_integrate a arr2' arr3' <;> try assumption
    grind [IntegrateInput.toItem_insertIfInBounds, YjsArrInvariant]

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
    grind only

theorem forIn_ok {α β : Type} {lst : List α} {init : β} {f : α → β → Except IntegrateError (ForInStep β)} :
  (∀ x ∈ lst, ∀ state, ∃ state', f x state = Except.ok state')
  → ∃ finalState, forIn lst init f = Except.ok finalState := by
  intros h_f
  induction lst generalizing init with
  | nil =>
    exists init
  | cons x xs ih =>
    simp
    have ⟨ state', hfx ⟩ := h_f x (by simp) init
    rw [hfx]
    simp [bind, Except.bind]
    cases state' with
    | done finalState =>
      exists finalState
    | yield nextState =>
      simp
      replace ⟨ finalState, ih ⟩ := ih (init := nextState) (fun y hy state => h_f y (by simp [hy]) state)
      use finalState

theorem ArrSet_findPtrIdx_eq_some {p : YjsPtr A} {arr : Array (YjsItem A)} :
  ArrSet arr.toList p
  → ∃idx, findPtrIdx p arr = Except.ok idx:= by
  intros h_arrset
  cases p with
  | first =>
    exists -1
  | last =>
    exists arr.size
  | itemPtr p =>
    simp [findPtrIdx]
    rw [Array.findIdx?_eq_some_of_exists]
    simp; constructor; eq_refl
    simp [ArrSet] at h_arrset
    use p; simp; assumption

theorem findIntegratedIndex_safe {leftIdx rightIdx : ℤ} {arr : Array (YjsItem A)} {input : IntegrateInput A} {newItem: YjsItem A} :
  YjsArrInvariant arr.toList
  → input.toItem arr = Except.ok newItem
  → -1 ≤ leftIdx → leftIdx ≤ arr.size
  → -1 ≤ rightIdx → rightIdx ≤ arr.size
  → ∃ idx', findIntegratedIndex leftIdx rightIdx input arr = Except.ok idx' := by
  intros harrinv h_newItem_def hleft_ge hleft_le hright_ge hright_le
  unfold findIntegratedIndex
  simp

  rw [IntegrateInput.toItem_ok_iff _ _ _ harrinv.unique] at h_newItem_def

  have ⟨ ⟨ dest, scanning ⟩, loop_ok ⟩ :
    ∃ state, forIn (m := Except IntegrateError) (ρ := List ℕ) (α := ℕ) (β := MProd ℤ Bool)
      (List.range' 1 ((rightIdx - leftIdx).toNat - 1)) ⟨leftIdx + 1, false⟩ (fun offset r => do
        let other ← getElemExcept arr (leftIdx + ↑offset).toNat
        let oLeftIdx ← findPtrIdx other.origin arr
        let oRightIdx ← findPtrIdx other.rightOrigin arr
        if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
          else
            if oLeftIdx = leftIdx then
              if other.id.clientId < input.id.clientId then
                pure (ForInStep.yield ⟨max (leftIdx + ↑offset) 0 + 1, false⟩)
              else
                if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
                else pure (ForInStep.yield ⟨r.fst, true⟩)
            else
              if r.snd = false then pure (ForInStep.yield ⟨max (leftIdx + ↑offset) 0 + 1, r.snd⟩)
              else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = Except.ok state := by
    apply forIn_ok
    intros offset h_offset_mem state
    obtain ⟨ destIdx, scanning ⟩ := state

    simp at h_offset_mem

    have ⟨ other, h_other_eq ⟩ : ∃ other, arr[(leftIdx + ↑offset).toNat]? = some other := by
      rw [Array.getElem?_eq_getElem (by omega)]
      simp

    have h_other_ok : getElemExcept arr (leftIdx + ↑offset).toNat = Except.ok other := by
      simp [getElemExcept]
      rw [h_other_eq]
      simp; eq_refl

    rw [h_other_ok, ok_bind]

    have ArrSet_other_origin : ArrSet arr.toList other.origin := by
      obtain ⟨ o, r, id, c ⟩ := other
      apply harrinv.closed.closedLeft o r id c
      simp [ArrSet]
      rw [getElem?_eq_some_iff] at h_other_eq
      obtain ⟨ _, h_other_eq ⟩ := h_other_eq
      rw [<-h_other_eq]
      simp

    have ArrSet_other_rightOrigin : ArrSet arr.toList other.rightOrigin := by
      obtain ⟨ o, r, id, c ⟩ := other
      apply harrinv.closed.closedRight o r id c
      simp [ArrSet]
      rw [getElem?_eq_some_iff] at h_other_eq
      obtain ⟨ _, h_other_eq ⟩ := h_other_eq
      rw [<-h_other_eq]
      simp

    have ⟨ oLeftIdx, h_oLeftIdx_ok ⟩ : ∃ oLeftIdx, findPtrIdx other.origin arr = Except.ok oLeftIdx := by
      simp [getElemExcept] at h_other_ok
      apply ArrSet_findPtrIdx_eq_some ArrSet_other_origin

    rw [h_oLeftIdx_ok, ok_bind]

    have ⟨ oRightIdx, h_oRightIdx_ok ⟩ : ∃ oRightIdx, findPtrIdx other.rightOrigin arr = Except.ok oRightIdx := by
      simp [getElemExcept] at h_other_ok
      apply ArrSet_findPtrIdx_eq_some ArrSet_other_rightOrigin

    rw [h_oRightIdx_ok, ok_bind]

    (repeat' (split)) <;> (constructor; eq_refl)

  use dest.toNat; rw [loop_ok]
  eq_refl

theorem findPtrIdx_none_insert {p : YjsItem A} {arr : Array (YjsItem A)} {a : YjsItem A} :
  findPtrIdx a arr = Except.error e
  → a ≠ p
  → findPtrIdx a (arr.insertIdxIfInBounds idx p) = Except.error e := by
  intros h_neq_other heq
  simp [findPtrIdx] at *
  cases h_findPtrIdx_arr : Array.findIdx? (fun i => decide (i = a)) arr with
  | some idx' =>
    rw [h_findPtrIdx_arr] at h_neq_other; contradiction
  | none =>
    rw [h_findPtrIdx_arr] at h_neq_other; cases h_neq_other
    rw [Array.findIdx?_insertIdxIfInBounds_none (by grind) h_findPtrIdx_arr]

theorem findLeftIdx_none_insert {originId : Option YjsId} {arr : Array (YjsItem A)} {a : YjsItem A} :
  findLeftIdx originId arr = Except.error e
  → originId ≠ a.id
  → findLeftIdx originId (arr.insertIdxIfInBounds idx a) = Except.error e := by
  intros h_neq_other heq
  cases originId with
  | none =>
    simp [findLeftIdx] at *
    rw [h_neq_other]
  | some id =>
    simp [findLeftIdx] at *
    cases h_findLeftIdx_arr : arr.findIdx? (fun item => item.id = id) with
    | some idx' =>
      rw [h_findLeftIdx_arr] at h_neq_other; contradiction
    | none =>
      rw [h_findLeftIdx_arr] at h_neq_other; cases h_neq_other
      rw [Array.findIdx?_insertIdxIfInBounds_none (by grind) h_findLeftIdx_arr]

theorem findRightIdx_none_insert {originId : Option YjsId} {arr : Array (YjsItem A)} {a : YjsItem A} :
  findRightIdx originId arr = Except.error e
  → originId ≠ a.id
  → findRightIdx originId (arr.insertIdxIfInBounds idx a) = Except.error e := by
  intros h_neq_other heq
  cases originId with
  | none =>
    simp [findRightIdx] at *
    cases h_neq_other
  | some id =>
    simp [findRightIdx] at *
    cases h_findRightIdx_arr : arr.findIdx? (fun item => item.id = id) with
    | some idx' =>
      rw [h_findRightIdx_arr] at h_neq_other; contradiction
    | none =>
      rw [h_findRightIdx_arr] at h_neq_other; cases h_neq_other
      rw [Array.findIdx?_insertIdxIfInBounds_none (by grind) h_findRightIdx_arr]

theorem findLeftIdx_some_getPtrExcept_some {originId : Option YjsId} {arr : Array (YjsItem A)}:
  findLeftIdx originId arr = Except.ok idx
  → ∃ p, getPtrExcept arr idx = Except.ok p ∧
      (match originId with
       | some id => ∃(item : YjsItem A), p = item ∧ item.id = id
       | none => p = YjsPtr.first) := by
  intros h_findLeftIdx
  simp [findLeftIdx, getPtrExcept] at *
  cases originId with
  | none =>
    use YjsPtr.first; simp at *
    cases h_findLeftIdx
    grind
  | some id =>
    simp at *
    cases heq : Array.findIdx? (fun item => item.id = id) arr with
    | none =>
      simp [heq] at h_findLeftIdx
    | some idx =>
      simp [heq] at h_findLeftIdx
      cases h_findLeftIdx
      grind [Array.findIdx?_eq_some_iff_getElem]


theorem findRightIdx_some_getPtrExcept_some {originId : Option YjsId} {arr : Array (YjsItem A)}:
  findRightIdx originId arr = Except.ok idx
  → ∃ p, getPtrExcept arr idx = Except.ok p ∧
      (match originId with
       | some id => ∃(item : YjsItem A), p = item ∧ item.id = id
       | none => p = YjsPtr.last) := by
  intros h_findRightIdx
  simp [findRightIdx, getPtrExcept] at *
  cases originId with
  | none =>
    use YjsPtr.last; simp at *
    cases h_findRightIdx
    grind
  | some id =>
    simp at *
    cases heq : Array.findIdx? (fun item => item.id = id) arr with
    | none =>
      simp [heq] at h_findRightIdx
    | some idx =>
      simp [heq] at h_findRightIdx
      cases h_findRightIdx
      grind [Array.findIdx?_eq_some_iff_getElem]

theorem integrate_insert_eq_none {arr : Array (YjsItem A)} {input : IntegrateInput A} {newItem other: YjsItem A} :
  YjsArrInvariant arr.toList
  → input.toItem arr = Except.ok newItem
  → ¬OriginReachable newItem (YjsPtr.itemPtr other)
  → integrate input arr = Except.error e
  → ∃ e', integrate input (arr.insertIdxIfInBounds idx other) = Except.error e' := by
  intros harrinv h_newItem_def h_not_reachable hintegrate
  unfold integrate at *

  cases heqleft : findLeftIdx input.originId arr with
  | error e =>
    rw [heqleft] at hintegrate
    cases hintegrate
    rw [findLeftIdx_none_insert heqleft _]
    . use e; rfl
    . intro h_eq
      have h_toItem := (IntegrateInput.toItem_ok_iff input arr newItem harrinv.unique).1 h_newItem_def
      obtain ⟨origin, rightOrigin, id, content, h_item_eq, h_origin, h_rightOrigin, h_id, h_content⟩ := h_toItem
      rw [h_eq] at h_origin
      simp [isLeftIdPtr] at h_origin
      obtain ⟨originItem, horigin_eq, h_find⟩ := h_origin
      have h_not_none : arr.findIdx? (fun item => item.id = other.id) ≠ none := by
        intro h_none
        rw [Array.findIdx?_eq_none_iff] at h_none
        have h_mem : originItem ∈ arr := Array.mem_of_find?_eq_some h_find
        rw [Array.find?_eq_some_iff_getElem] at h_find
        exact (by simpa [h_find.1] using h_none originItem h_mem)
      cases h_idx : arr.findIdx? (fun item => item.id = other.id) with
      | none =>
        exact (h_not_none h_idx).elim
      | some idx' =>
        simp [findLeftIdx, h_eq, h_idx] at heqleft
        cases heqleft
  | ok leftIdx =>
    rw [heqleft, ok_bind] at hintegrate
    cases heqleft' : findLeftIdx input.originId (arr.insertIdxIfInBounds idx other) with
    | error e =>
      exists e
    | ok leftIdx' =>
      rw [ok_bind]
      cases heqright : findRightIdx input.rightOriginId arr with
      | error e =>
        rw [heqright] at hintegrate
        cases hintegrate
        rw [findRightIdx_none_insert heqright _]
        . exists e
        . intro h_eq
          have h_toItem := (IntegrateInput.toItem_ok_iff input arr newItem harrinv.unique).1 h_newItem_def
          obtain ⟨origin, rightOrigin, id, content, h_item_eq, h_origin, h_rightOrigin, h_id, h_content⟩ := h_toItem
          rw [h_eq] at h_rightOrigin
          simp [isRightIdPtr] at h_rightOrigin
          obtain ⟨rightItem, hright_eq, h_find⟩ := h_rightOrigin
          have h_not_none : arr.findIdx? (fun item => item.id = other.id) ≠ none := by
            intro h_none
            rw [Array.findIdx?_eq_none_iff] at h_none
            have h_mem : rightItem ∈ arr := Array.mem_of_find?_eq_some h_find
            rw [Array.find?_eq_some_iff_getElem] at h_find
            exact (by simpa [h_find.1] using h_none rightItem h_mem)
          cases h_idx : arr.findIdx? (fun item => item.id = other.id) with
          | none =>
            exact (h_not_none h_idx).elim
          | some idx' =>
            simp [findRightIdx, h_eq, h_idx] at heqright
            cases heqright
      | ok rightIdx =>
        cases heqright' : findRightIdx input.rightOriginId (arr.insertIdxIfInBounds idx other) with
        | error e =>
          exists e
        | ok rightIdx' =>
          simp [heqright, ok_bind] at hintegrate
          simp [ok_bind]
          have ⟨ destIdx, h_destIdx ⟩ : ∃ destdx, findIntegratedIndex leftIdx rightIdx input arr = Except.ok destdx := by
            apply findIntegratedIndex_safe harrinv h_newItem_def
            . cases h_originId : input.originId with
              | none =>
                simp [findLeftIdx, h_originId] at heqleft
                cases heqleft
                omega
              | some oid =>
                simp [findLeftIdx, h_originId] at heqleft
                cases h_find : arr.findIdx? (fun item => item.id = oid) with
                | none =>
                  simp [h_find] at heqleft
                | some idx' =>
                  simp [h_find] at heqleft
                  cases heqleft
                  omega
            . cases h_originId : input.originId with
              | none =>
                simp [findLeftIdx, h_originId] at heqleft
                cases heqleft
                omega
              | some oid =>
                simp [findLeftIdx, h_originId] at heqleft
                cases h_find : arr.findIdx? (fun item => item.id = oid) with
                | none =>
                  simp [h_find] at heqleft
                | some idx' =>
                  simp [h_find] at heqleft
                  cases heqleft
                  rw [Array.findIdx?_eq_some_iff_getElem] at h_find
                  obtain ⟨ hlt, _, _ ⟩ := h_find
                  exact_mod_cast Nat.le_of_lt hlt
            . cases h_rightOriginId : input.rightOriginId with
              | none =>
                simp [findRightIdx, h_rightOriginId] at heqright
                cases heqright
                omega
              | some rid =>
                simp [findRightIdx, h_rightOriginId] at heqright
                cases h_find : arr.findIdx? (fun item => item.id = rid) with
                | none =>
                  simp [h_find] at heqright
                | some idx' =>
                  simp [h_find] at heqright
                  cases heqright
                  omega
            . cases h_rightOriginId : input.rightOriginId with
              | none =>
                simp [findRightIdx, h_rightOriginId] at heqright
                cases heqright
                omega
              | some rid =>
                simp [findRightIdx, h_rightOriginId] at heqright
                cases h_find : arr.findIdx? (fun item => item.id = rid) with
                | none =>
                  simp [h_find] at heqright
                | some idx' =>
                  simp [h_find] at heqright
                  cases heqright
                  rw [Array.findIdx?_eq_some_iff_getElem] at h_find
                  obtain ⟨ hlt, _, _ ⟩ := h_find
                  exact_mod_cast Nat.le_of_lt hlt
          rw [h_destIdx, ok_bind] at hintegrate
          simp [mkItemByIndex] at hintegrate
          have ⟨ item, hitem, hitemid ⟩ := findLeftIdx_some_getPtrExcept_some heqleft
          rw [hitem] at hintegrate
          have ⟨ item', hitem', hitemid' ⟩ := findRightIdx_some_getPtrExcept_some heqright
          rw [hitem'] at hintegrate
          simp [bind, Except.bind] at hintegrate

theorem Except.bind_eq_ok {α β ε : Type} (e : Except ε α) (f : α → Except ε β) (b : β) :
  e >>= f = Except.ok b →
  ∃ a, e = Except.ok a ∧ f a = Except.ok b := by
  intro heq
  simp [bind, Except.bind] at heq
  cases e with
  | error err =>
    cases heq
  | ok val =>
    simp at heq
    use val

theorem Except.bind_eq_error {α β ε : Type} (e : Except ε α) (f : α → Except ε β) (err : ε) :
  e >>= f = Except.error err →
  (e = Except.error err) ∨ (∃ a, e = Except.ok a ∧ f a = Except.error err) := by
  intro heq
  simp [bind, Except.bind] at heq
  cases e with
  | error e_err =>
    simp at heq
    left; rw [heq]
  | ok val =>
    simp at heq
    right
    use val

theorem Except.map_eq_ok {α β ε : Type} (f : α → β) {e : Except ε α} (b : β) :
  f <$> e = Except.ok b →
  ∃ a, e = Except.ok a ∧ f a = b := by
  intro heq
  cases e with
  | error err =>
    simp at heq
  | ok val =>
    simp at heq
    use val

-- TODO: Move to YjsArray
theorem maximalId_insert {arr : Array (YjsItem A)} {a x : YjsItem A} :
  YjsArrInvariant arr.toList
  → maximalId x (arr.insertIdxIfInBounds idx a)
  → maximalId x arr := by
  intros harrinv h_UniqueId_insert
  intros y hy_in_arr hid_eq
  rw [List.insertIdxIfInBounds_toArray] at *
  simp [maximalId, ArrSet] at *
  apply h_UniqueId_insert y _ hid_eq
  by_cases idx <= arr.size
  . grind [List.mem_insertIdx]
  . rw [List.insertIdx_of_length_lt]
    grind
    grind

theorem integrate_integrate_eq_none {arr : Array (YjsItem A)} {a b : IntegrateInput A} {aItem bItem : YjsItem A}:
  YjsArrInvariant arr.toList
  → a.toItem arr = Except.ok aItem
  → b.toItem arr = Except.ok bItem
  → a.id.clientId ≠ b.id.clientId
  → aItem.isValid
  → bItem.isValid
  → ¬OriginReachable aItem (YjsPtr.itemPtr bItem)
  → integrateSafe a arr = Except.error e
  → integrateSafe b arr = Except.ok arr2
  → ∃ e', integrateSafe a arr2 = Except.error e' := by
  intros harrinv haItem hbItem hcid_neq_bid h_a_valid h_b_valid h_not_reachable h_integrate_a h_integrate_b
  simp [integrateSafe] at *
  split_ifs at *
  constructor; constructor; apply IntegrateError.error
  intros hsafe
  rw [<-isClockSafe_maximalId harrinv.unique haItem] at *
  rw [<-isClockSafe_maximalId harrinv.unique hbItem] at *
  have h_maxb : maximalId bItem arr := by assumption
  have haItem_arr2 : a.toItem arr2 = Except.ok aItem := by
    obtain ⟨ idxb, hidxb, h_arr2_eq, harrinv_arr2 ⟩ :=
      YjsArrInvariant_integrate b arr arr2 harrinv hbItem h_b_valid h_maxb h_integrate_b
    have h_unique_insert : uniqueId (arr.insertIdxIfInBounds idxb bItem).toList := by
      simpa [h_arr2_eq] using harrinv_arr2.unique
    have h_toItem_insert :
        a.toItem (arr.insertIdxIfInBounds idxb bItem) = Except.ok aItem :=
      IntegrateInput.toItem_insertIfInBounds (idx := idxb) (input := a) (a := bItem) haItem h_unique_insert
    simpa [h_arr2_eq] using h_toItem_insert

  have ⟨ idx, h_arr2 ⟩  : ∃ i, arr2 = arr.insertIdxIfInBounds i bItem := by
    simp [integrate] at h_integrate_b
    apply Except.bind_eq_ok at h_integrate_b
    replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_a ⟩ := h_integrate_b
    apply Except.bind_eq_ok at h_integrate_a
    replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_a ⟩ := h_integrate_a
    apply Except.bind_eq_ok at h_integrate_a
    obtain ⟨ destIdx, h_destIdx_eq, h_integrate_a ⟩ := h_integrate_a
    apply Except.map_eq_ok at h_integrate_a
    obtain ⟨ bItem', hbItem', heq ⟩ := h_integrate_a
    have hbItem' : bItem' = bItem := by
      have hbItem_tmp := hbItem
      rw [IntegrateInput.toItem_ok_iff _ _ _ harrinv.unique] at hbItem_tmp
      obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin, h_rightOrigin, h_id, h_content ⟩ := hbItem_tmp
      have h_leftIdx_eq' := h_leftIdx_eq
      have h_rightIdx_eq' := h_rightIdx_eq
      apply findLeftIdx_getElemExcept at h_leftIdx_eq'
      obtain ⟨ originPtr, h_originPtr, h_leftIdPtr ⟩ := h_leftIdx_eq'
      apply findRightIdx_getElemExcept at h_rightIdx_eq'
      obtain ⟨ rightOriginPtr, h_rightOriginPtr, h_rightIdPtr ⟩ := h_rightIdx_eq'
      have h_mkItem_bItem : mkItemByIndex leftIdx rightIdx b arr = Except.ok bItem := by
        simp [mkItemByIndex, h_originPtr, h_rightOriginPtr, bind, Except.bind, pure, Except.pure]
        have hleft_unique := isLeftIdPtr_unique _ _ _ _ harrinv.unique h_leftIdPtr h_origin
        have hright_unique := isRightIdPtr_unique _ _ _ _ harrinv.unique h_rightIdPtr h_rightOrigin
        grind
      rw [h_mkItem_bItem] at hbItem'
      injection hbItem' with hb_eq
      exact hb_eq.symm
    grind

  suffices maximalId aItem arr by
    have ⟨ e, h ⟩ := integrate_insert_eq_none (idx := idx) harrinv haItem h_not_reachable (h_integrate_a this)
    rw [h_arr2, h]

  simp [integrate] at h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  obtain ⟨ destIdx, h_destIdx_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.map_eq_ok at h_integrate_b
  obtain ⟨ bItem', hbItem', heq' ⟩ := h_integrate_b
  subst arr2
  apply maximalId_insert harrinv (idx := idx) (a := bItem)
  intros x hmem heq
  rw [<-isClockSafe_maximalId] at hsafe
  . apply hsafe x hmem heq
  . have h_integrate_b_idx : integrate b arr = Except.ok (arr.insertIdxIfInBounds idx bItem) := by
      have h_integrate_b_dest : integrate b arr = Except.ok (arr.insertIdxIfInBounds destIdx bItem') := by
        unfold integrate
        rw [h_leftIdx_eq, ok_bind, h_rightIdx_eq, ok_bind, h_destIdx_eq, ok_bind, hbItem']
        simp
      simpa [heq'] using h_integrate_b_dest
    have h_maxb' : maximalId bItem arr := by assumption
    obtain ⟨ i, hi, h_newArr_eq, h_newArr_inv ⟩ :=
      YjsArrInvariant_integrate b arr (arr.insertIdxIfInBounds idx bItem) harrinv hbItem h_b_valid h_maxb' h_integrate_b_idx
    exact h_newArr_inv.unique
  . exact haItem_arr2

theorem findLeftIdx_insert {originId : Option YjsId} {arr : Array (YjsItem A)} {a : YjsItem A} :
  findLeftIdx originId arr = Except.ok leftIdx
  → a.id ≠ originId
  → findLeftIdx originId (arr.insertIdxIfInBounds idx a) = if leftIdx < idx then Except.ok leftIdx else Except.ok (leftIdx + 1) := by
  intros h_findLeftIdx hneq
  simp [findLeftIdx] at *
  cases originId with
  | none =>
    simp at *
    cases h_findLeftIdx
    split
    . rfl
    . omega
  | some id =>
    simp at *
    cases heq : arr.findIdx? (fun item => item.id = id) with
    | none =>
      simp [heq] at h_findLeftIdx
    | some idx' =>
      simp [heq] at h_findLeftIdx
      cases h_findLeftIdx
      rw [Array.findIdx?_insertIdxIfInBounds_some _ heq]
      . split_ifs
        . rfl
        . omega
        . omega
        . rfl
      . grind


theorem findRightIdx_insert {originId : Option YjsId} {arr : Array (YjsItem A)} {a : YjsItem A} :
  findRightIdx originId arr = Except.ok rigthIdx
  → a.id ≠ originId
  → findRightIdx originId (arr.insertIdxIfInBounds idx a) =
   if rigthIdx < idx then Except.ok rigthIdx
   else Except.ok (rigthIdx + 1) := by
  intros h_findLeftIdx hneq
  simp [findRightIdx] at *
  cases originId with
  | none =>
    simp at *
    cases h_findLeftIdx
    split
    . simp [Array.insertIdxIfInBounds]
      split
      . omega
      . rfl
    . simp [Array.insertIdxIfInBounds]
      split
      . rw [Array.size_insertIdx]; rfl
      . omega
  | some id =>
    simp at *
    cases heq : arr.findIdx? (fun item => item.id = id) with
    | none =>
      simp [heq] at h_findLeftIdx
    | some idx' =>
      simp [heq] at h_findLeftIdx
      cases h_findLeftIdx
      rw [Array.findIdx?_insertIdxIfInBounds_some _ heq]
      . split_ifs
        . rfl
        . omega
        . omega
        . rfl
      . grind

theorem integrate_integrate_eq_some {arr : Array (YjsItem A)} {a b : IntegrateInput A} {aItem bItem : YjsItem A} {arr2 arr2' : Array (YjsItem A)}:
  YjsArrInvariant arr.toList
  → a.toItem arr = Except.ok aItem
  → b.toItem arr = Except.ok bItem
  → a.id.clientId ≠ b.id.clientId
  → aItem.isValid
  → bItem.isValid
  → integrateSafe a arr = Except.ok arr2
  → integrateSafe b arr = Except.ok arr2'
  → ∃ arr3, integrateSafe b arr2 = Except.ok arr3 := by
  intros harrinv h_aItem h_bItem h_aid_neq_bid h_a_valid h_b_valid h_integrate_a h_integrate_b

  have harrinv_arr2 : YjsArrInvariant arr2.toList := by
    have ⟨ _, _, _, h ⟩ := YjsArrInvariant_integrateSafe a aItem arr arr2 harrinv h_aItem h_a_valid h_integrate_a
    assumption

  simp [integrateSafe] at *
  split_ifs at h_integrate_a h_integrate_b

  simp [integrate] at h_integrate_a
  apply Except.bind_eq_ok at h_integrate_a
  replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_a ⟩ := h_integrate_a
  apply Except.bind_eq_ok at h_integrate_a
  replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_a ⟩ := h_integrate_a
  apply Except.bind_eq_ok at h_integrate_a
  replace ⟨ destIdx, h_destIdx_eq, h_integrate_a ⟩ := h_integrate_a
  apply Except.map_eq_ok at h_integrate_a
  obtain ⟨ item, h_item_eq, h_eq ⟩ := h_integrate_a

  simp [integrate] at h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ leftIdx', h_leftIdx'_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ rightIdx', h_rightIdx'_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ destIdx', h_destIdx'_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.map_eq_ok at h_integrate_b
  obtain ⟨ item', h_item'_eq, h_eq' ⟩ := h_integrate_b

  subst arr2
  simp [integrate]

  have heq_item_aItem : item = aItem := by
    have h_aItem_tmp := (IntegrateInput.toItem_ok_iff a arr aItem harrinv.unique).1 h_aItem
    obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_aItem_tmp
    have h_leftIdx_eq' := h_leftIdx_eq
    have h_rightIdx_eq' := h_rightIdx_eq
    apply findLeftIdx_getElemExcept at h_leftIdx_eq'
    obtain ⟨ originPtr, h_originPtr, h_leftIdPtr ⟩ := h_leftIdx_eq'
    apply findRightIdx_getElemExcept at h_rightIdx_eq'
    obtain ⟨ rightOriginPtr, h_rightOriginPtr, h_rightIdPtr ⟩ := h_rightIdx_eq'
    have h_mkItem_aItem : mkItemByIndex leftIdx rightIdx a arr = Except.ok aItem := by
      simp [mkItemByIndex, h_originPtr, h_rightOriginPtr, bind, Except.bind, pure, Except.pure]
      have hleft_unique := isLeftIdPtr_unique _ _ _ _ harrinv.unique h_leftIdPtr h_origin
      have hright_unique := isRightIdPtr_unique _ _ _ _ harrinv.unique h_rightIdPtr h_rightOrigin
      grind
    rw [h_mkItem_aItem] at h_item_eq
    injection h_item_eq with h_eq_item
    exact h_eq_item.symm
  subst item

  have ⟨ leftIdx'', h_leftIdx''_eq ⟩ : ∃ leftIdx'', findLeftIdx b.originId (arr.insertIdxIfInBounds destIdx aItem) = Except.ok leftIdx'' := by
    rw [findLeftIdx_insert h_leftIdx'_eq]
    split_ifs <;> simp
    intro h_eq
    have h_a_clock : isClockSafe a.id arr = true := by
      assumption
    have h_a_max : maximalId aItem arr := by
      rw [<-isClockSafe_maximalId harrinv.unique h_aItem] at h_a_clock
      exact h_a_clock
    have h_bItem_tmp := (IntegrateInput.toItem_ok_iff b arr bItem harrinv.unique).1 h_bItem
    obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_bItem_tmp
    rw [<-h_eq] at h_origin
    simp [isLeftIdPtr] at h_origin
    obtain ⟨ originItem, horigin_eq, h_find_origin ⟩ := h_origin
    have h_origin_mem : ArrSet arr.toList (YjsPtr.itemPtr originItem) := by
      simp [ArrSet, Array.mem_of_find?_eq_some h_find_origin]
    have h_find_origin' := h_find_origin
    rw [Array.find?_eq_some_iff_getElem] at h_find_origin'
    have h_id_eq : originItem.id = aItem.id := by
      simpa using h_find_origin'.1
    have h_clock_lt : originItem.id.clock < aItem.id.clock := by
      apply h_a_max originItem h_origin_mem
      simpa [h_id_eq]
    have h_clock_self : originItem.id.clock < originItem.id.clock := by
      simpa [h_id_eq] using h_clock_lt
    exact (Nat.lt_irrefl _ h_clock_self).elim
  have h_leftIdx''_range : -1 ≤ leftIdx'' ∧ leftIdx'' ≤ (arr.insertIdxIfInBounds destIdx aItem).size := by
    cases h_originId : b.originId with
    | none =>
      simp [findLeftIdx, h_originId] at h_leftIdx''_eq
      cases h_leftIdx''_eq
      constructor <;> omega
    | some oid =>
      simp [findLeftIdx, h_originId] at h_leftIdx''_eq
      cases h_find : (arr.insertIdxIfInBounds destIdx aItem).findIdx? (fun item => item.id = oid) with
      | none =>
        simp [h_find] at h_leftIdx''_eq
      | some i =>
        simp [h_find] at h_leftIdx''_eq
        cases h_leftIdx''_eq
        have hi_lt : i < (arr.insertIdxIfInBounds destIdx aItem).size := by
          rw [Array.findIdx?_eq_some_iff_getElem] at h_find
          exact h_find.1
        constructor <;> omega
  have ⟨ rightIdx'', h_rightIdx''_eq ⟩ : ∃ rightIdx'', findRightIdx b.rightOriginId (arr.insertIdxIfInBounds destIdx aItem) = Except.ok rightIdx'' := by
    rw [findRightIdx_insert h_rightIdx'_eq]
    split_ifs <;> simp
    intro h_eq
    have h_a_clock : isClockSafe a.id arr = true := by
      assumption
    have h_a_max : maximalId aItem arr := by
      rw [<-isClockSafe_maximalId harrinv.unique h_aItem] at h_a_clock
      exact h_a_clock
    have h_bItem_tmp := (IntegrateInput.toItem_ok_iff b arr bItem harrinv.unique).1 h_bItem
    obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_bItem_tmp
    rw [<-h_eq] at h_rightOrigin
    simp [isRightIdPtr] at h_rightOrigin
    obtain ⟨ rightItem, hright_eq, h_find_right ⟩ := h_rightOrigin
    have h_right_mem : ArrSet arr.toList (YjsPtr.itemPtr rightItem) := by
      simp [ArrSet, Array.mem_of_find?_eq_some h_find_right]
    have h_find_right' := h_find_right
    rw [Array.find?_eq_some_iff_getElem] at h_find_right'
    have h_id_eq : rightItem.id = aItem.id := by
      simpa using h_find_right'.1
    have h_clock_lt : rightItem.id.clock < aItem.id.clock := by
      apply h_a_max rightItem h_right_mem
      simpa [h_id_eq]
    have h_clock_self : rightItem.id.clock < rightItem.id.clock := by
      simpa [h_id_eq] using h_clock_lt
    exact (Nat.lt_irrefl _ h_clock_self).elim
  have h_rightIdx''_range : -1 ≤ rightIdx'' ∧ rightIdx'' ≤ (arr.insertIdxIfInBounds destIdx aItem).size := by
    cases h_rightOriginId : b.rightOriginId with
    | none =>
      simp [findRightIdx, h_rightOriginId] at h_rightIdx''_eq
      cases h_rightIdx''_eq
      constructor <;> omega
    | some rid =>
      simp [findRightIdx, h_rightOriginId] at h_rightIdx''_eq
      cases h_find : (arr.insertIdxIfInBounds destIdx aItem).findIdx? (fun item => item.id = rid) with
      | none =>
        simp [h_find] at h_rightIdx''_eq
      | some i =>
        simp [h_find] at h_rightIdx''_eq
        cases h_rightIdx''_eq
        have hi_lt : i < (arr.insertIdxIfInBounds destIdx aItem).size := by
          rw [Array.findIdx?_eq_some_iff_getElem] at h_find
          exact h_find.1
        constructor <;> omega

  have hbItem_arr2 : b.toItem (arr.insertIdxIfInBounds destIdx aItem) = Except.ok bItem := by
    exact IntegrateInput.toItem_insertIfInBounds (idx := destIdx) (input := b) (a := aItem) h_bItem harrinv_arr2.unique

  split_ifs
  . rw [h_leftIdx''_eq, h_rightIdx''_eq]
    rw [ok_bind, ok_bind]
    have h : b.toItem (arr.insertIdxIfInBounds destIdx aItem) = Except.ok bItem := by
      exact hbItem_arr2
    have ⟨ _, h ⟩ := findIntegratedIndex_safe (leftIdx := leftIdx'') (rightIdx := rightIdx'') (newItem := bItem) harrinv_arr2 h (by omega) (by omega) (by omega) (by omega)
    rw [h]
    rw [ok_bind]
    have h : mkItemByIndex leftIdx'' rightIdx'' b (arr.insertIdxIfInBounds destIdx aItem) = Except.ok bItem := by
      have h_toItem := hbItem_arr2
      rw [IntegrateInput.toItem_ok_iff _ _ _ harrinv_arr2.unique] at h_toItem
      obtain ⟨ origin, rightOrigin, id, content, h_item_def, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_toItem
      have h_leftIdx''_eq' := h_leftIdx''_eq
      have h_rightIdx''_eq' := h_rightIdx''_eq
      apply findLeftIdx_getElemExcept at h_leftIdx''_eq'
      obtain ⟨ originPtr, h_originPtr, h_leftIdPtr ⟩ := h_leftIdx''_eq'
      apply findRightIdx_getElemExcept at h_rightIdx''_eq'
      obtain ⟨ rightOriginPtr, h_rightOriginPtr, h_rightIdPtr ⟩ := h_rightIdx''_eq'
      simp [mkItemByIndex, h_originPtr, h_rightOriginPtr, bind, Except.bind, pure, Except.pure]
      have hleft_unique := isLeftIdPtr_unique _ _ _ _ harrinv_arr2.unique h_leftIdPtr h_origin
      have hright_unique := isRightIdPtr_unique _ _ _ _ harrinv_arr2.unique h_rightIdPtr h_rightOrigin
      grind
    rw [h]
    constructor; rfl
  . have h_contra : maximalId bItem (arr.insertIdxIfInBounds destIdx aItem) := by
      rw [<-isClockSafe_maximalId harrinv.unique h_bItem] at *
      apply insertIdxIfInBounds_UniqueId <;> try assumption
      have h_aItem_tmp := (IntegrateInput.toItem_ok_iff a arr aItem harrinv.unique).1 h_aItem
      have h_bItem_tmp := (IntegrateInput.toItem_ok_iff b arr bItem harrinv.unique).1 h_bItem
      obtain ⟨ ao, ar, aid, ac, ha_def, ha_origin, ha_right, ha_id, ha_content ⟩ := h_aItem_tmp
      obtain ⟨ bo, br, bid, bc, hb_def, hb_origin, hb_right, hb_id, hb_content ⟩ := h_bItem_tmp
      intro h_client_eq
      apply h_aid_neq_bid
      simpa [ha_def, hb_def, ha_id, hb_id] using h_client_eq
    have h_clock_true : isClockSafe b.id (arr.insertIdxIfInBounds destIdx aItem) = true := by
      exact (isClockSafe_maximalId harrinv_arr2.unique hbItem_arr2).1 h_contra
    have h_not_clock_true : ¬isClockSafe b.id (arr.insertIdxIfInBounds destIdx aItem) = true := by
      assumption
    exact (False.elim (h_not_clock_true h_clock_true))

theorem integrate_commutative (a b : IntegrateInput A) (aItem bItem : YjsItem A) (arr1 : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  → a.toItem arr1 = Except.ok aItem
  → b.toItem arr1 = Except.ok bItem
  → a.id.clientId ≠ b.id.clientId
  → ¬OriginReachable aItem (YjsPtr.itemPtr bItem)
  → ¬OriginReachable bItem (YjsPtr.itemPtr aItem)
  → aItem.isValid
  → bItem.isValid
  → (do
    let arr2 <- integrateSafe a arr1;
    integrateSafe b arr2) =
  (do
    let arr2' <- integrateSafe b arr1;
    integrateSafe a arr2') := by
  intros harrinv h_aItem h_bItem hcid_neq_bid h_not_a_origin_b h_not_b_origin_a h_a_valid h_b_valid
  cases h_eq_a : integrateSafe a arr1 with
  | error e_a =>
    cases h_eq_b : integrateSafe b arr1 with
    | error e_b =>
      simp [bind, Except.bind]
    | ok arr2' =>
      simp [bind, Except.bind]
      have ⟨ e_a', h_integrate_a' ⟩ : ∃ e_a', integrateSafe a arr2' = Except.error e_a' := by
        apply integrate_integrate_eq_none harrinv h_aItem h_bItem hcid_neq_bid h_a_valid h_b_valid h_not_a_origin_b h_eq_a h_eq_b
      rw [h_integrate_a']
  | ok arr2 =>
    cases h_eq_b : integrateSafe b arr1 with
    | error e_b =>
      simp [bind, Except.bind]
      have ⟨ e_b', h_integrate_b' ⟩ : ∃ e_b', integrateSafe b arr2 = Except.error e_b' := by
        apply integrate_integrate_eq_none harrinv h_bItem h_aItem (by grind)  h_b_valid h_a_valid h_not_b_origin_a h_eq_b  h_eq_a
      rw [h_integrate_b']
    | ok arr2' =>
      simp [bind, Except.bind]
      have ⟨ arr3', h_integrate_comm ⟩ : ∃ arr3', integrateSafe a arr2' = Except.ok arr3' := by
        apply integrate_integrate_eq_some harrinv h_bItem h_aItem (by grind) h_b_valid h_a_valid h_eq_b h_eq_a
      have ⟨ arr3, h_integrate_comm' ⟩ : ∃ arr3, integrateSafe b arr2 = Except.ok arr3 := by
        apply integrate_integrate_eq_some harrinv h_aItem h_bItem hcid_neq_bid h_a_valid h_b_valid h_eq_a h_eq_b
      rw [h_integrate_comm, h_integrate_comm']
      rw [integrate_ok_commutative a b arr1 arr2 arr3 arr2' arr3' harrinv h_aItem h_bItem hcid_neq_bid h_a_valid h_b_valid h_eq_a h_integrate_comm' h_eq_b h_integrate_comm]

theorem insert_commutative (a b : IntegrateInput A) (aItem bItem : YjsItem A) (arr res: YjsState A) :
  YjsStateInvariant arr
  → a.toItem arr.items = Except.ok aItem
  → b.toItem arr.items = Except.ok bItem
  → a.id.clientId ≠ b.id.clientId
  → ¬OriginReachable aItem (YjsPtr.itemPtr bItem)
  → ¬OriginReachable bItem (YjsPtr.itemPtr aItem)
  → aItem.isValid
  → bItem.isValid
  → (do
    let arr2 <- arr.insert a;
    arr2.insert b) = Except.ok res
  → (do
    let arr2' <- arr.insert b;
    arr2'.insert a) = Except.ok res := by
  intros harrinv h_aItem_def h_bItem_def hcid_neq_bid h_not_a_origin_b h_not_b_origin_a h_a_valid h_b_valid h_eq
  generalize heq1 : arr.insert a = arr2 at h_eq
  generalize heq2 : arr.insert b = arr2'
  subst arr2
  subst arr2'

  have h_bind_ok : (arr.insert a >>= fun arr2 => arr2.insert b) = Except.ok res := by
    simpa [bind, Except.bind] using h_eq
  obtain ⟨ arrA, h_insert_a_ok, h_insert_b_after_a_ok ⟩ :=
    except_bind_eq_ok_exists (x := arr.insert a) (f := fun arr2 => arr2.insert b) (y := res) h_bind_ok

  have h_insert_a_do :
      (do
        let newArr <- integrateSafe a arr.items
        pure { arr with items := newArr }) = Except.ok arrA := by
    simpa [YjsState.insert, bind, Except.bind] using h_insert_a_ok
  apply Except.bind_eq_ok at h_insert_a_do
  obtain ⟨ arrAItems, h_integrate_a_ok, h_arrA_eq ⟩ := h_insert_a_do
  have h_arrA_state : arrA = { arr with items := arrAItems } := by
    have htmp : ({ arr with items := arrAItems } : YjsState A) = arrA := by
      simpa [pure, Except.pure] using h_arrA_eq
    exact htmp.symm
  have h_arrA_items : arrA.items = arrAItems := by
    simpa [h_arrA_state]

  have h_insert_b_after_a_do :
      (do
        let newArr <- integrateSafe b arrA.items
        pure { arrA with items := newArr }) = Except.ok res := by
    simpa [YjsState.insert, bind, Except.bind] using h_insert_b_after_a_ok
  apply Except.bind_eq_ok at h_insert_b_after_a_do
  obtain ⟨ resItems, h_integrate_b_after_a_ok, h_res_eq ⟩ := h_insert_b_after_a_do
  have h_res_state : res = { arrA with items := resItems } := by
    have htmp : ({ arrA with items := resItems } : YjsState A) = res := by
      simpa [pure, Except.pure] using h_res_eq
    exact htmp.symm
  have h_integrate_b_after_a_ok_items : integrateSafe b arrAItems = Except.ok resItems := by
    simpa [h_arrA_items] using h_integrate_b_after_a_ok

  have h_insert_b_ok : ∃ arrB, arr.insert b = Except.ok arrB := by
    cases h_b : arr.insert b with
    | error e =>
      have h_integrate_b_err : integrateSafe b arr.items = Except.error e := by
        cases h_intb : integrateSafe b arr.items with
        | error e' =>
          have h_b' := h_b
          simp [YjsState.insert, bind, Except.bind, h_intb] at h_b'
          cases h_b'
          simpa using h_intb
        | ok newArr =>
          simp [YjsState.insert, bind, Except.bind, h_intb] at h_b
          cases h_b
      have h_integrate_a_ok_items : integrateSafe a arr.items = Except.ok arrAItems := by
        exact h_integrate_a_ok
      have ⟨ e', h_integrate_b_after_a_err ⟩ :=
        integrate_integrate_eq_none (arr := arr.items) (a := b) (b := a) (aItem := bItem) (bItem := aItem)
          harrinv h_bItem_def h_aItem_def (by simpa using hcid_neq_bid.symm) h_b_valid h_a_valid h_not_b_origin_a h_integrate_b_err h_integrate_a_ok_items
      have h_contra : (Except.ok resItems : Except IntegrateError (Array (YjsItem A))) = Except.error e' := by
        calc
          Except.ok resItems = integrateSafe b arrAItems := by symm; exact h_integrate_b_after_a_ok_items
          _ = Except.error e' := h_integrate_b_after_a_err
      cases h_contra
    | ok arrB =>
      exact ⟨ arrB, rfl ⟩

  obtain ⟨ arrB, h_insert_b_ok ⟩ := h_insert_b_ok
  have h_insert_b_do :
      (do
        let newArr <- integrateSafe b arr.items
        pure { arr with items := newArr }) = Except.ok arrB := by
    simpa [YjsState.insert, bind, Except.bind] using h_insert_b_ok
  apply Except.bind_eq_ok at h_insert_b_do
  obtain ⟨ arrBItems, h_integrate_b_ok, h_arrB_eq ⟩ := h_insert_b_do
  have h_arrB_state : arrB = { arr with items := arrBItems } := by
    have htmp : ({ arr with items := arrBItems } : YjsState A) = arrB := by
      simpa [pure, Except.pure] using h_arrB_eq
    exact htmp.symm
  have h_arrB_items : arrB.items = arrBItems := by
    simpa [h_arrB_state]

  have ⟨ arrBAItems, h_integrate_a_after_b_ok ⟩ :=
    integrate_integrate_eq_some (arr := arr.items) (a := b) (b := a) (aItem := bItem) (bItem := aItem)
      harrinv h_bItem_def h_aItem_def (by simpa using hcid_neq_bid.symm) h_b_valid h_a_valid h_integrate_b_ok h_integrate_a_ok
  have h_integrate_a_after_b_ok_state : integrateSafe a arrB.items = Except.ok arrBAItems := by
    simpa [h_arrB_items] using h_integrate_a_after_b_ok

  have h_items_eq :
      resItems = arrBAItems := by
    have h_comm :=
      integrate_ok_commutative a b arr.items arrAItems resItems arrBItems arrBAItems
        harrinv h_aItem_def h_bItem_def hcid_neq_bid h_a_valid h_b_valid
        h_integrate_a_ok h_integrate_b_after_a_ok_items h_integrate_b_ok h_integrate_a_after_b_ok
    exact h_comm

  have h_state_eq : { arrB with items := arrBAItems } = res := by
    rw [h_arrB_state, h_res_state, h_arrA_state]
    simp [h_items_eq]

  have h_insert_a_after_b_ok : arrB.insert a = Except.ok res := by
    unfold YjsState.insert
    rw [h_integrate_a_after_b_ok_state, ok_bind]
    simpa [pure, Except.pure, h_state_eq]

  rw [h_insert_b_ok]
  rw [ok_bind]
  exact h_insert_a_after_b_ok
