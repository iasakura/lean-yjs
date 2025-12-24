import Mathlib.Tactic.WLOG
import Mathlib.Tactic.ExtractGoal

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
import LeanYjs.Algorithm.Integrate
import LeanYjs.Algorithm.YjsArray
import LeanYjs.Algorithm.IntegrateSpec

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
  -> UniqueId x arr1
  -> UniqueId x arr2 := by
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
  → UniqueId x arr
  → a.id.clientId ≠ x.id.clientId
  → UniqueId x (arr.insertIdxIfInBounds idx a) := by
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

theorem integrate_ok_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id.clientId ≠ b.id.clientId
  → a.isValid
  → b.isValid
  -> integrateSafe a arr1 = Except.ok arr2
  -> integrateSafe b arr2 = Except.ok arr3
  -> integrateSafe b arr1 = Except.ok arr2'
  -> integrateSafe a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  intros harrinv hcid_neq_bid h_a_valid h_b_valid hintegrate_a hintegrate_b hintegrate_b' hintegrate_a'

  simp [integrateSafe] at *
  split_ifs at *
  rw [<-isClockSafe_uniqueId] at *

  have ⟨ idx2, h_idx2, arr2_insertIdx, arr2_inv ⟩ : ∃ idx ≤ arr1.size, arr2 = arr1.insertIdxIfInBounds idx a ∧ YjsArrInvariant arr2.toList := by
    apply YjsArrInvariant_integrate a arr1 arr2
    assumption
    assumption
    assumption
    assumption

  have h_UniqueId_arr2_b : UniqueId b arr2 := by
    subst arr2
    apply insertIdxIfInBounds_UniqueId <;> assumption

  have ⟨ idx2', h_idx2', arr2'_insertIdx, arr2'_inv ⟩ : ∃ idx ≤ arr1.size, arr2' = arr1.insertIdxIfInBounds idx b ∧ YjsArrInvariant arr2'.toList := by
    apply YjsArrInvariant_integrate b arr1 arr2'
    assumption
    assumption
    assumption
    assumption

  have h_UniqueId_arr2'_a : UniqueId a arr2' := by
    subst arr2'
    apply insertIdxIfInBounds_UniqueId <;> try assumption
    intros heq
    rw [heq] at hcid_neq_bid
    contradiction

  have ⟨ idx3, h_idx3, arr3_insertIdx,  arr3_inv ⟩ : ∃ idx ≤ arr2.size, arr3 = arr2.insertIdxIfInBounds idx b ∧ YjsArrInvariant arr3.toList := by
    apply YjsArrInvariant_integrate b arr2 arr3
    assumption
    assumption
    assumption
    assumption

  have ⟨ idx3', h_idx3', arr3'_insertIdx, arr3'_inv ⟩ : ∃ idx ≤ arr2'.size, arr3' = arr2'.insertIdxIfInBounds idx a ∧ YjsArrInvariant arr3'.toList := by
    apply YjsArrInvariant_integrate a arr2' arr3'
    assumption
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

theorem findIntegratedIndex_safe {leftIdx rightIdx : ℤ} {arr : Array (YjsItem A)} {newItem: YjsItem A} :
  YjsArrInvariant arr.toList
  → -1 ≤ leftIdx → leftIdx ≤ arr.size
  → -1 ≤ rightIdx → rightIdx ≤ arr.size
  → ∃ idx', findIntegratedIndex leftIdx rightIdx newItem arr = Except.ok idx' := by
  intros harrinv hleft_ge hleft_le hright_ge hright_le
  unfold findIntegratedIndex
  simp

  have ⟨ ⟨ dest, scanning ⟩, loop_ok ⟩ :
    ∃ idx, forIn (m := Except IntegrateError) (ρ := List ℕ) (α := ℕ) (β := MProd ℤ Bool)
      (List.range' 1 ((rightIdx - leftIdx).toNat - 1)) ⟨leftIdx + 1, false⟩ (fun offset r => do
        let other ← getElemExcept arr (leftIdx + ↑offset).toNat
        let oLeftIdx ← findPtrIdx other.origin arr
        let oRightIdx ← findPtrIdx other.rightOrigin arr
        if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
          else
            if oLeftIdx = leftIdx then
              if other.id.clientId < newItem.id.clientId then
                pure (ForInStep.yield ⟨max (leftIdx + ↑offset) 0 + 1, false⟩)
              else
                if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
                else pure (ForInStep.yield ⟨r.fst, true⟩)
            else
              if r.snd = false then pure (ForInStep.yield ⟨max (leftIdx + ↑offset) 0 + 1, r.snd⟩)
              else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = Except.ok idx := by
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
      obtain ⟨ o, r, id, c, d ⟩ := other
      apply harrinv.closed.closedLeft o r id c
      simp [ArrSet]
      rw [getElem?_eq_some_iff] at h_other_eq
      obtain ⟨ _, h_other_eq ⟩ := h_other_eq
      rw [<-h_other_eq]
      simp

    have ArrSet_other_rightOrigin : ArrSet arr.toList other.rightOrigin := by
      obtain ⟨ o, r, id, c, d ⟩ := other
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

theorem integrate_insert_eq_none {arr : Array (YjsItem A)} {newItem other: YjsItem A} :
  YjsArrInvariant arr.toList
  → ¬OriginReachable newItem (YjsPtr.itemPtr other)
  → integrate newItem arr = Except.error e
  → ∃ e', integrate newItem (arr.insertIdxIfInBounds idx other) = Except.error e' := by
  intros harrinv h_not_reachable hintegrate
  unfold integrate at *

  have h_neq_other_error : ∀ (t : YjsItem A), t ≠ other
    → findPtrIdx t arr = Except.error e
    → findPtrIdx t (arr.insertIdxIfInBounds idx other) = Except.error e := by
    intros t heq h_neq_other
    clear hintegrate
    simp [findPtrIdx] at *
    cases h_findPtrIdx_arr : Array.findIdx? (fun i => decide (i = t)) arr with
    | some idx' =>
      rw [h_findPtrIdx_arr] at h_neq_other; contradiction
    | none =>
      rw [h_findPtrIdx_arr] at h_neq_other; cases h_neq_other
      cases heq' : Array.findIdx? (fun i => decide (i = t)) (arr.insertIdxIfInBounds idx other) with
      | none =>
        simp
      | some idx' =>
        have h_not_mem : t ∉ arr := by
          intros hmem
          rw [Array.findIdx?_eq_none_iff] at h_findPtrIdx_arr
          simp at h_findPtrIdx_arr
          apply h_findPtrIdx_arr _ hmem
          simp
        have h_mem : t ∈ arr.insertIdxIfInBounds idx other := by
          rw [Array.findIdx?_eq_some_iff_getElem] at heq'
          obtain ⟨ hlt, h1, _ ⟩ := heq'
          simp at h1
          subst t
          simp
        simp [Array.insertIdxIfInBounds] at h_mem
        split at h_mem
        . rw [Array.mem_insertIdx] at h_mem
          cases h_mem with
          | inl heq =>
            contradiction
          | inr hmem =>
            contradiction
        . contradiction

  cases heqleft : findPtrIdx newItem.origin arr with
  | error e =>
    rw [heqleft] at hintegrate
    cases hintegrate
    have heqleft' : findPtrIdx newItem.origin (arr.insertIdxIfInBounds idx other) = Except.error e := by
      cases h_origin_eq : newItem.origin with
      | first =>
        rw [h_origin_eq] at heqleft
        simp [findPtrIdx] at heqleft
        contradiction
      | last =>
        rw [h_origin_eq] at heqleft
        simp [findPtrIdx] at heqleft
        contradiction
      | itemPtr p =>
        rw [h_origin_eq] at heqleft
        apply h_neq_other_error _ _ heqleft
        intros heq
        rw [<-heq, <-h_origin_eq] at h_not_reachable
        apply h_not_reachable
        obtain ⟨ o, r, id, c, d ⟩ := newItem
        apply OriginReachable.reachable_single
        apply OriginReachableStep.reachable
    rw [heqleft']
    exists e
  | ok leftIdx =>
    rw [heqleft, ok_bind] at hintegrate
    cases heqleft' : findPtrIdx newItem.origin (arr.insertIdxIfInBounds idx other) with
    | error e =>
      simp [bind, Except.bind]
      apply Nonempty.intro IntegrateError.notFound
    | ok leftIdx' =>
      rw [ok_bind]
      cases heqright : findPtrIdx newItem.rightOrigin arr with
      | error e =>
        rw [heqright] at hintegrate
        cases hintegrate
        have heqright' : findPtrIdx newItem.rightOrigin (arr.insertIdxIfInBounds idx other) = Except.error e := by
          cases h_rightOrigin_eq : newItem.rightOrigin with
          | first =>
            rw [h_rightOrigin_eq] at heqright
            simp [findPtrIdx] at heqright
            contradiction
          | last =>
            rw [h_rightOrigin_eq] at heqright
            simp [findPtrIdx] at heqright
            contradiction
          | itemPtr p =>
            rw [h_rightOrigin_eq] at heqright
            apply h_neq_other_error _ _ heqright
            intros heq
            rw [<-heq, <-h_rightOrigin_eq] at h_not_reachable
            apply h_not_reachable
            obtain ⟨ o, r, id, c, d ⟩ := newItem
            apply OriginReachable.reachable_single
            apply OriginReachableStep.reachable_right
        rw [heqright']
        exists e
      | ok rightIdx =>
        rw [heqright, ok_bind] at hintegrate
        have ⟨ destIdx, h_destIdx ⟩ : ∃ destdx, findIntegratedIndex leftIdx rightIdx newItem arr = Except.ok destdx := by
          apply findIntegratedIndex_safe harrinv
          apply findPtrIdx_ge_minus_1 at heqleft
          assumption
          apply findPtrIdx_le_size at heqleft
          assumption
          apply findPtrIdx_ge_minus_1 at heqright
          assumption
          apply findPtrIdx_le_size at heqright
          assumption
        rw [h_destIdx, ok_bind] at hintegrate
        cases hintegrate

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

theorem integrate_integrate_eq_none {arr : Array (YjsItem A)} {a b : YjsItem A} :
  YjsArrInvariant arr.toList
  → a.id.clientId ≠ b.id.clientId
  → a.isValid
  → b.isValid
  → ¬OriginReachable a (YjsPtr.itemPtr b)
  → integrateSafe a arr = Except.error e
  → integrateSafe b arr = Except.ok arr2
  → ∃ e', integrateSafe a arr2 = Except.error e' := by
  intros harrinv hcid_neq_bid h_a_valid h_b_valid h_not_reachable h_integrate_a h_integrate_b
  simp [integrateSafe] at *
  split_ifs at *
  constructor; constructor; apply IntegrateError.notFound
  intros hsafe
  rw [<-isClockSafe_uniqueId] at *
  have ⟨ idx, h_arr2 ⟩  : ∃ i, arr2 = arr.insertIdxIfInBounds i b := by
    simp [integrate] at h_integrate_b
    apply Except.bind_eq_ok at h_integrate_b
    replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_a ⟩ := h_integrate_b
    apply Except.bind_eq_ok at h_integrate_a
    replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_a ⟩ := h_integrate_a
    apply Except.map_eq_ok at h_integrate_a
    obtain ⟨ destIdx, h_destIdx_eq, h_eq ⟩ := h_integrate_a
    use destIdx; simp [h_eq]
  suffices UniqueId a arr by
    have ⟨ e, h ⟩ := integrate_insert_eq_none (idx := idx) harrinv h_not_reachable (h_integrate_a this)
    rw [h_arr2, h]

  simp [integrate] at h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.map_eq_ok at h_integrate_b
  obtain ⟨ destIdx, h_destIdx_eq, h_eq ⟩ := h_integrate_b

  intros x hmem heq
  apply hsafe x _ heq
  subst arr2
  simp [ArrSet, Array.insertIdxIfInBounds] at *
  split_ifs
  . rw [Array.mem_insertIdx]
    right; assumption
  . assumption

theorem integrate_integrate_eq_some {arr : Array (YjsItem A)} {a b : YjsItem A} :
  YjsArrInvariant arr.toList
  → a.id.clientId ≠ b.id.clientId
  → a.isValid
  → b.isValid
  → integrateSafe a arr = Except.ok arr2
  → integrateSafe b arr = Except.ok arr2'
  → ∃ arr3, integrateSafe b arr2 = Except.ok arr3 := by
  intros harrinv h_aid_neq_bid h_a_valid h_b_valid h_integrate_a h_integrate_b

  have harrinv_arr2 : YjsArrInvariant arr2.toList := by
    have ⟨ _, _, _, h ⟩ := YjsArrInvariant_integrateSafe a arr arr2 harrinv h_a_valid h_integrate_a
    assumption

  simp [integrateSafe] at *
  split_ifs at h_integrate_a h_integrate_b

  simp [integrate] at h_integrate_a
  apply Except.bind_eq_ok at h_integrate_a
  replace ⟨ leftIdx, h_leftIdx_eq, h_integrate_a ⟩ := h_integrate_a
  apply Except.bind_eq_ok at h_integrate_a
  replace ⟨ rightIdx, h_rightIdx_eq, h_integrate_a ⟩ := h_integrate_a
  apply Except.map_eq_ok at h_integrate_a
  obtain ⟨ destIdx, h_destIdx_eq, h_eq ⟩ := h_integrate_a

  simp [integrate] at h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ leftIdx', h_leftIdx'_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.bind_eq_ok at h_integrate_b
  replace ⟨ rightIdx', h_rightIdx'_eq, h_integrate_b ⟩ := h_integrate_b
  apply Except.map_eq_ok at h_integrate_b
  obtain ⟨ destIdx', h_destIdx'_eq, h_eq' ⟩ := h_integrate_b

  subst arr2
  simp [integrate]

  have ⟨ leftIdx'', h_leftIdx''_eq ⟩ : ∃ leftIdx'', findPtrIdx b.origin (arr.insertIdxIfInBounds destIdx a) = Except.ok leftIdx'' := by
    rw [findPtrIdx_insert_some harrinv_arr2 h_leftIdx'_eq]
    split_ifs <;> simp
  have h_leftIdx''_range : -1 ≤ leftIdx'' ∧ leftIdx'' ≤ (arr.insertIdxIfInBounds destIdx a).size := by
    constructor
    . apply findPtrIdx_ge_minus_1 at h_leftIdx''_eq; omega
    . apply findPtrIdx_le_size at h_leftIdx''_eq; omega
  have ⟨ rightIdx'', h_rightIdx''_eq ⟩ : ∃ rightIdx'', findPtrIdx b.rightOrigin (arr.insertIdxIfInBounds destIdx a) = Except.ok rightIdx'' := by
    rw [findPtrIdx_insert_some harrinv_arr2 h_rightIdx'_eq]
    split_ifs <;> simp
  have h_rightIdx''_range : -1 ≤ rightIdx'' ∧ rightIdx'' ≤ (arr.insertIdxIfInBounds destIdx a).size := by
    constructor
    . apply findPtrIdx_ge_minus_1 at h_rightIdx''_eq; omega
    . apply findPtrIdx_le_size at h_rightIdx''_eq; omega

  split_ifs
  . rw [h_leftIdx''_eq, h_rightIdx''_eq]
    rw [ok_bind, ok_bind]
    have ⟨ _, h ⟩ := findIntegratedIndex_safe (leftIdx := leftIdx'') (rightIdx := rightIdx'') (newItem := b) harrinv_arr2 (by omega) (by omega) (by omega) (by omega)
    rw [h]; simp
  . rw [<-isClockSafe_uniqueId] at *
    have h_contra : UniqueId b (arr.insertIdxIfInBounds destIdx a) := by
      apply insertIdxIfInBounds_UniqueId <;> try assumption
    contradiction

theorem integrate_commutative (a b : YjsItem A) (arr1 : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id.clientId ≠ b.id.clientId
  → ¬OriginReachable a (YjsPtr.itemPtr b)
  → ¬OriginReachable b (YjsPtr.itemPtr a)
  → a.isValid
  → b.isValid
  -> (do
    let arr2 <- integrateSafe a arr1;
    integrateSafe b arr2) =
  (do
    let arr2' <- integrateSafe b arr1;
    integrateSafe a arr2') := by
  intros harrinv hcid_neq_bid h_not_a_origin_b h_not_b_origin_a h_a_valid h_b_valid
  cases h_eq_a : integrateSafe a arr1 with
  | error e_a =>
    cases h_eq_b : integrateSafe b arr1 with
    | error e_b =>
      simp [bind, Except.bind]
    | ok arr2' =>
      simp [bind, Except.bind]
      have ⟨ e_a', h_integrate_a' ⟩ : ∃ e_a', integrateSafe a arr2' = Except.error e_a' := by
        apply integrate_integrate_eq_none harrinv hcid_neq_bid h_a_valid h_b_valid h_not_a_origin_b h_eq_a h_eq_b
      rw [h_integrate_a']
  | ok arr2 =>
    cases h_eq_b : integrateSafe b arr1 with
    | error e_b =>
      simp [bind, Except.bind]
      have ⟨ e_b', h_integrate_b' ⟩ : ∃ e_b', integrateSafe b arr2 = Except.error e_b' := by
        apply integrate_integrate_eq_none harrinv _ h_b_valid h_a_valid h_not_b_origin_a h_eq_b h_eq_a
        intros heq; rw [heq] at hcid_neq_bid; contradiction
      rw [h_integrate_b']
    | ok arr2' =>
      simp [bind, Except.bind]
      have ⟨ arr3', h_integrate_comm ⟩ : ∃ arr3', integrateSafe a arr2' = Except.ok arr3' := by
        apply integrate_integrate_eq_some harrinv _ h_b_valid h_a_valid h_eq_b h_eq_a
        intros heq; rw [heq] at hcid_neq_bid; contradiction
      have ⟨ arr3, h_integrate_comm' ⟩ : ∃ arr3, integrateSafe b arr2 = Except.ok arr3 := by
        apply integrate_integrate_eq_some harrinv hcid_neq_bid h_a_valid h_b_valid h_eq_a h_eq_b
      rw [h_integrate_comm, h_integrate_comm']
      rw [integrate_ok_commutative a b arr1 arr2 arr3 arr2' arr3' harrinv hcid_neq_bid h_a_valid h_b_valid h_eq_a h_integrate_comm' h_eq_b h_integrate_comm]
