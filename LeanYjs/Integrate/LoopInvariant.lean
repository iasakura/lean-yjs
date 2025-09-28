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
import LeanYjs.NoCrossOrigin
import LeanYjs.Integrate
import LeanYjs.YjsArray
import LeanYjs.Integrate.Loop

variable {A : Type}
variable [DecidableEq A]

set_option maxHeartbeats 400000

omit [DecidableEq A] in theorem not_rightOrigin_first (P : YjsPtr A -> Prop) (item : YjsItem A) :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  P item ->
  item.rightOrigin ≠ YjsPtr.first := by
  intros hclosed hinv hin heq
  have hlt : YjsLt' (A := A) item item.rightOrigin := by
    exists 1
    obtain ⟨ o, r, id, c ⟩ := item
    apply YjsLt.ltRightOrigin
    left
  obtain ⟨ _, hlt ⟩ := hlt
  rw [heq] at hlt
  apply not_ptr_lt_first hclosed hinv _ _ hin at hlt; assumption

-- 補題: itemとの大小関係が保留の区間 [dest, i) newItem < arr[i]なら∀j ∈ [dest, i) でnewItem < arr[j]が成り立つ。
-- つまりループの終了条件が満たされたら[dest, i)のすべてでnewItem < arr[j]
theorem loopInv_YjsLt' {current} offset (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : ℤ) (state : ForInStep (MProd ℤ Bool)) :
  IsClosedItemSet (ArrSet (newItem :: arr.toList)) ->
  ItemSetInvariant (ArrSet (newItem :: arr.toList)) ->
  YjsArrInvariant arr.toList ->
  loopInv arr newItem leftIdx rightIdx offset state ->

  findPtrIdx newItem.origin arr = Except.ok leftIdx ->
  findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx ->

  current = offsetToIndex leftIdx rightIdx offset (isBreak state) ->
  (hcurrentlt : current ≤ arr.size) ->
  ((hlt : current < arr.size) -> YjsLt' (A := A) newItem arr[current]) ->
  ∀ j : ℕ, (h_j_dest : state.value.fst ≤ j) ->
    (h_j_i : j ≤ current) -> (h_j_size : j < arr.size) ->
    YjsLt' (A := A) newItem arr[j] := by

  intros hclosed hinv harrinv hloopinv hleftIdx hrightIdx hcurrent hcurrent_lt hi_lt j h_j_dest h_j_i h_j_size
  generalize hsize : arr[j].size = size
  revert j
  generalize h_dest_def : state.value.fst = dest
  generalize h_scanning : state.value.snd = scanning
  apply Nat.strongRec' (p := fun size => ∀ (j : ℕ), dest ≤ j → (h_j_i : j ≤ current) -> (h_j_size : j < arr.size) -> arr[j].size = size → YjsLt' (A := A) newItem (YjsPtr.itemPtr arr[j]))
  intros n ih j h_j_dest h_j_i h_j_size heq_n
  wlog h_j_i : j < current
  case inr =>
    have h_j_eq : j = current := by
      omega
    subst j
    apply hi_lt

  subst heq_n
  unfold loopInv at hloopinv
  have heq : state.value = ⟨dest, scanning⟩ := by
    subst h_dest_def
    subst h_scanning
    cases state <;> eq_refl
  rw [heq] at hloopinv
  obtain ⟨ hsize, hdest_current, h_not_scanning, h_lt_item, h_tbd, h_cand, h_done ⟩ := hloopinv
  -- simp [offsetToIndex] at h_tbd hcurrent
  subst hcurrent
  obtain ⟨ h_j_lt_size, h_dest_lt_size, h_tbd ⟩ := h_tbd j (by omega) h_j_i
  cases h_tbd with
  | inl h_origin =>
    obtain ⟨ h_origin_eq, h_id_lt ⟩ := h_origin

    have ⟨ _, hlt_ro ⟩ : YjsLt' (A := A) newItem arr[j].rightOrigin := by
      generalize h_ro_eq : arr[j].rightOrigin = ro at heq
      cases ro with
      | first =>
        apply not_rightOrigin_first _ arr[j] hclosed hinv at h_ro_eq
        contradiction
        simp [ArrSet]
      | last =>
        constructor
        apply YjsLt.ltOriginOrder
        apply OriginLt.lt_last
      | itemPtr ro =>
        have ⟨ roIdx, h_ro_in ⟩ : ∃ k : Fin arr.size, arr[k] = ro := by
          cases arr_set_closed_exists_index_for_right_origin arr.toList arr[j] (harrinv.closed) (by simp [ArrSet]) with
          | inl h1 =>
            rw [h_ro_eq] at h1
            cases h1
          | inr h =>
            cases h with
            | inl h1 =>
              rw [h_ro_eq] at h1
              cases h1
            | inr h1 =>
              rw [h_ro_eq] at h1
              obtain ⟨ k, h1 ⟩ := h1
              cases h1
              exists k

        have hsize : ro.size < arr[j].size := by
          revert h_ro_eq
          obtain ⟨ o, r, id, c ⟩ := arr[j]
          simp [YjsItem.rightOrigin]
          intros h_ro_eq
          subst h_ro_eq
          simp [YjsItem.size, YjsPtr.size]
          omega

        have h_dest_k : dest.toNat ≤ roIdx := by
          obtain ⟨ roIdx, _ ⟩ := roIdx
          simp at *
          have hlt : j < roIdx := by
            have hlt : YjsLt' (A := A) arr[j] arr[roIdx] := by
              rw [h_ro_in]
              generalize heq : arr[j] = arrj at *
              obtain ⟨ o, r, id, c ⟩ := arrj
              simp [YjsItem.rightOrigin] at h_ro_eq
              subst h_ro_eq
              exists 1
              have harrin : ArrSet arr.toList (YjsItem.item o (YjsPtr.itemPtr ro) id c) := by
                rw [<-heq]
                simp [ArrSet]
              apply YjsLt.ltRightOrigin
              apply YjsLeq.leqSame

            have hltj : j < arr.size := by
              omega
            have hltk : roIdx < arr.size := by
              omega
            apply getElem_YjsLt'_index_lt arr j roIdx harrinv hltj hltk hlt
          omega

        cases Nat.lt_or_ge roIdx (offsetToIndex leftIdx rightIdx offset (isBreak state)) with
        | inl h_k_current =>
          obtain x := ih (ro.size) hsize roIdx (by omega) (by omega) (by omega) (by rw [<-h_ro_in]; simp)
          simp at h_ro_in x
          rw [h_ro_in] at x
          assumption
        | inr h_k_current =>
          -- newItem < arr[current] <= arr[k]
          have hlt : YjsLeq' (A := A) arr[offsetToIndex leftIdx rightIdx offset (isBreak state)] ro := by
            subst h_ro_in
            apply getElem_leq_YjsLeq' arr (offsetToIndex leftIdx rightIdx offset (isBreak state)) roIdx harrinv (by omega) (by omega)
          apply yjs_leq'_p_trans2 hinv _ _ _ _ _ _ hclosed (hi_lt (by omega)) hlt
          . simp [ArrSet]
          . simp [ArrSet]
          . subst ro; simp [ArrSet]

    have ⟨ _, hlt_ro' ⟩ : YjsLt' (A := A) arr[j] newItem.rightOrigin := by
      have hlt : j < rightIdx := by
        cases offset <;> simp [offsetToIndex] at h_j_i <;> omega
      have heq : findPtrIdx arr[j] arr = Except.ok j := by
        apply findPtrIdx_getElem; assumption
      apply findPtrIdx_lt_YjsLt' _ _ _ harrinv heq hrightIdx hlt

    obtain ⟨ o, r, id, c ⟩ := newItem
    generalize arr[j] = item at *
    obtain ⟨ oo, or, oid, oc ⟩ := item
    simp [YjsItem.origin, YjsItem.rightOrigin] at h_origin_eq hlt_ro hlt_ro'
    rw [h_origin_eq]
    rw [h_origin_eq] at hlt_ro'
    constructor
    apply YjsLt.ltConflict
    apply ConflictLt.ltOriginSame <;> try assumption
  | inr hleq =>
    have hlt_ro : YjsLt' (A := A) newItem arr[j].origin := by
      generalize h_o_eq : arr[j].origin = o at heq
      cases o with
      | first =>
        rw [h_o_eq] at hleq
        apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
        cases hleq with
        | inl heq =>
          cases heq
        | inr hlt =>
          by_contra
          apply not_ptr_lt'_first hclosed hinv at hlt; assumption
          simp [ArrSet]

      | last =>
        constructor
        apply YjsLt.ltOriginOrder
        apply OriginLt.lt_last
      | itemPtr o =>
        have ⟨ ⟨ oIdx, _ ⟩ , h_o_in ⟩ : ∃ k : Fin arr.size, arr[k] = o := by
          cases arr_set_closed_exists_index_for_origin arr.toList arr[j] (harrinv.closed) (by simp [ArrSet]) with
          | inl h1 =>
            rw [h_o_eq] at h1
            cases h1
          | inr h =>
            cases h with
            | inl h1 =>
              rw [h_o_eq] at h1
              cases h1
            | inr h1 =>
              rw [h_o_eq] at h1
              obtain ⟨ k, h1 ⟩ := h1
              cases h1
              exists k

        have hsize : o.size < arr[j].size := by
          revert h_o_eq
          obtain ⟨ o, r, id, c ⟩ := arr[j]
          simp [YjsItem.origin]
          intros h_o_eq
          subst h_o_eq
          simp [YjsItem.size, YjsPtr.size]
          omega

        have h_dest_k : dest ≤ oIdx := by
          simp at *
          rw [h_o_eq] at hleq
          subst h_o_in

          have hor : dest < 0 ∨ 0 ≤ dest := by
            apply Int.lt_or_le
          cases hor with
          | inl _ => omega
          | inr _ =>
            apply YjsLeq'_findPtrIdx_leq _ _ _ _ _ harrinv _ _ hleq
            . rw [findPtrIdx_getElem _ _ harrinv]
              simp
              omega
            . rw [findPtrIdx_getElem _ _ harrinv]
            . simp [ArrSet]
            . simp [ArrSet]

        simp at h_o_in
        subst h_o_in
        apply ih arr[oIdx].size hsize _ h_dest_k
        . simp
        . have hlt : oIdx < j := by
            apply getElem_YjsLt'_index_lt arr oIdx j harrinv (by omega) (by omega)
            rw [<-h_o_eq]
            generalize heq : arr[j] = arrj at *
            obtain ⟨ o, r, id, c ⟩ := arrj
            simp [YjsItem.origin]
            apply YjsLt'.ltOrigin
            apply YjsLeq'.leqSame
          omega

    generalize heq : arr[j] = arrj at *
    obtain ⟨ o, r, id, c ⟩ := arrj
    apply YjsLt'.ltOrigin (A := A)
    simp [YjsItem.origin] at hlt_ro
    apply YjsLeq'.leqLt; assumption


theorem offsetToIndex_range'_getElem {leftIdx rightIdx : ℤ} {offset : ℕ} :
  -1 ≤ leftIdx →
  0 ≤ rightIdx →
  offset ≤ rightIdx - leftIdx - 1 →
  offsetToIndex leftIdx rightIdx (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[offset]? (isBreak state) = (leftIdx + offset + 1).toNat - (if isBreak state then 1 else 0) := by
  intros h_leftIdx h_rightIdx hle
  generalize heq : (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[offset]? = i at *
  cases i with
  | none =>
    simp [offsetToIndex]
    rw [List.getElem?_eq_none_iff] at heq
    rw [List.length_range'] at heq
    omega
  | some o =>
    simp [offsetToIndex]
    rw [List.getElem?_eq_some_iff] at heq
    obtain ⟨ h_length, heq ⟩ := heq
    rw [List.getElem_range'] at heq
    rw [List.length_range'] at h_length
    omega

theorem dest_lt_YjsLt'_preserve {A : Type} [inst : DecidableEq A] (newItem : YjsItem A) (arr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin) (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (horigin_consistent : YjsLt' (A := A) newItem.origin newItem.rightOrigin)
  (hreachable_consistent :
    ∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
        YjsLeq' (A := A) x newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin x)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))
  (hneq : ∀ x ∈ arr, ¬x = newItem) (harrinv : YjsArrInvariant arr.toList)
  (hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)))
  (harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList))) (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx) (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx) (hleftIdxrightIdx : leftIdx < rightIdx)
  (next : ForInStep (MProd ℤ Bool)) (i : ℕ) (hlt2 : i < (rightIdx - leftIdx).toNat - 1) (other : YjsItem A)
  (hother : getElemExcept arr (leftIdx + (1 + ↑i)).toNat = Except.ok other) (oLeftIdx : ℤ)
  (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx) (oRightIdx : ℤ)
  (hoRightIdx : findPtrIdx other.rightOrigin arr = Except.ok oRightIdx) (dest : ℤ) (scanning : Bool)
  (h_cand : scanning = true → ∃ (h_dest_lt : dest.toNat < arr.size), arr[dest.toNat].origin = newItem.origin)
  (h_leftIdx : -1 ≤ leftIdx) (nDest : ℤ) (nScanning : Bool)
  (hnexteq : next.value = ⟨nDest, nScanning⟩) (hrightIdx : 0 ≤ rightIdx) (hlt : i < (rightIdx - leftIdx).toNat - 1)
  (hinv : loopInv arr newItem leftIdx (max rightIdx 0) (some (1 + i)) (ForInStep.yield ⟨dest, scanning⟩))
  (hbody :
    next =
      if oLeftIdx < leftIdx then ForInStep.done ⟨dest, scanning⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, false⟩
          else if oRightIdx = rightIdx then ForInStep.done ⟨dest, scanning⟩ else ForInStep.yield ⟨dest, true⟩
        else
          if scanning = false then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, scanning⟩
          else ForInStep.yield ⟨dest, scanning⟩)
  (hidx : 0 < 1 + i ∧ 1 + ↑i < max rightIdx 0 - leftIdx)
  (hdest_current :
    dest ≤ ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_not_scanning :
    scanning = false →
      isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = false →
        dest = ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_lt_item :
    ∀ (i : ℕ),
      ↑i < dest →
        ∀ (h_i_lt : i < arr.size),
          YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLeq' (A := A) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (A := A) (YjsPtr.itemPtr newItem) item)
  (hnext_dest :
    nDest =
      if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then if other.id < newItem.id then leftIdx + (1 + ↑i) + 1 else dest
        else if scanning = false then leftIdx + (1 + ↑i) + 1 else dest)
  (hnext_scanning :
    nScanning =
      if oLeftIdx < leftIdx then scanning
      else
        if oLeftIdx = leftIdx then !decide (other.id < newItem.id) && (!decide (oRightIdx = rightIdx) || scanning)
        else scanning)
  (nDest_eq : nDest = dest ∨ nDest = leftIdx + ↑(1 + i) + 1) (hlt_current : (leftIdx + (1 + ↑i)).toNat < arr.size)
  (heq : arr[(leftIdx + (1 + ↑i)).toNat] = other) (h_in_other : ArrSet (newItem :: arr.toList) (YjsPtr.itemPtr other))
  (h_in_other_origin : ArrSet (newItem :: arr.toList) other.origin)
  (h_other_origin_lt : YjsLt' (A := A) other.origin (YjsPtr.itemPtr other))
  (nDest_lt_size : nDest.toNat ≤ arr.size) : ∀ (i : ℕ),
  ↑i < nDest →
    ∀ (h_i_lt : i < arr.size),
      YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem) := by
  intros j h_j_lt h_j_lt_size
  subst nDest
  have h_j_dest :  j < dest.toNat → YjsLt' (A := A) arr[j] newItem := by
    intros
    obtain hlt := h_lt_item j (by omega) (by omega)
    assumption
  have h_newItem_origin_lt_other : YjsLt' (A := A) newItem.origin other := by
    apply findPtrIdx_lt_YjsLt' (i := leftIdx) (j := (leftIdx + (1 + ↑i)).toNat)  <;> try assumption
    . subst other; rw [findPtrIdx_getElem]; assumption
    . omega
  have h_other_lt_newItem_rightOrigin : YjsLt' (A := A) other newItem.rightOrigin := by
    apply findPtrIdx_lt_YjsLt' (i := (leftIdx + (1 + ↑i)).toNat) (j := rightIdx) <;> try assumption
    . subst other; rw [findPtrIdx_getElem]; assumption
    . omega
  split at h_j_lt <;> try (apply h_j_dest (by omega))
  split at h_j_lt
  . split at h_j_lt
    on_goal 2 => apply h_j_dest (by omega)
    apply yjs_leq'_p_trans1 (inv := harrsetinv) (y := other) <;> try assumption
    . simp [ArrSet]
    . subst other; simp [ArrSet]
    . subst other
      apply getElem_leq_YjsLeq' arr j (leftIdx + (1 + ↑i)).toNat harrinv
      omega
    apply findPtrIdx_origin_leq_newItem_YjsLt' _ _ _ hclosed harrsetinv harrinv <;> try assumption
    . omega
    . intros; assumption
    . subst leftIdx
      have heq : newItem.origin = other.origin := by
        apply findPtrIdx_eq_ok_inj _ _ heqleft hoLeftIdx
      rw [<-heq]
      obtain ⟨ o, r, id, c ⟩ := newItem
      apply YjsLt'.ltOrigin
      simp [YjsItem.origin]
      exists 0; apply YjsLeq.leqSame
    . intros; simp; right; assumption
    . simp
  . -- leftIdx < oLeftIdx cases
    split at h_j_lt
    . apply yjs_leq'_p_trans1 (inv := harrsetinv) (y := other) <;> try assumption
      . simp [ArrSet]
      . simp [ArrSet]
      . subst other
        apply getElem_leq_YjsLeq' arr j (leftIdx + (1 + ↑i)).toNat harrinv
        omega
      . apply findPtrIdx_origin_leq_newItem_YjsLt' _ _ _ hclosed harrsetinv harrinv _ (by assumption) (by assumption) <;> try assumption
        . omega
        . omega
        . generalize h_other_origin_eq : other.origin = otherOrigin at *
          cases otherOrigin with
          | first =>
            apply YjsLt'.ltOriginOrder (A := A)
            apply OriginLt.lt_first
          | last =>
            subst other
            obtain ⟨ _, h_other_origin_lt ⟩ := h_other_origin_lt
            by_contra
            apply not_last_lt_ptr hclosed harrsetinv at h_other_origin_lt; try assumption
            simp [ArrSet]
          | itemPtr otherOrigin =>
            have ⟨  k, _, h_otherOrigin_arr_k⟩ : ∃(k : ℕ) (h : k < arr.size), arr[k] = otherOrigin := by
              have h_otherOrigin_in_arr : ArrSet arr.toList (YjsPtr.itemPtr otherOrigin) := by
                obtain ⟨ o, r, id, c ⟩ := other
                -- rw [heq] at h_other_origin_eq
                simp [YjsItem.origin] at h_other_origin_eq
                subst o
                apply harrinv.closed.closedLeft (YjsPtr.itemPtr otherOrigin) r id c
                rw [<-heq]
                simp [ArrSet]
              simp [ArrSet] at h_otherOrigin_in_arr
              rw [Array.mem_iff_getElem] at h_otherOrigin_in_arr
              assumption
            have h_dest_eq : dest.toNat = leftIdx + (1 + i) := by
              have h_isDone_false : isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = false := by
                simp [isDone]
              obtain heq := h_not_scanning (by assumption) (h_isDone_false)
              simp [offsetToIndex, isBreak] at heq
              subst dest
              omega
            rw [<-h_otherOrigin_arr_k]
            apply h_lt_item
            have otherOrigin_lt : YjsLt' (A := A) otherOrigin arr[(leftIdx + (1 + ↑i)).toNat] := by
              rw [<-h_other_origin_eq]
              generalize h_other_eq : arr[(leftIdx + (1 + ↑i)).toNat] = other at *
              obtain ⟨ o, r, id, c ⟩ := other
              apply YjsLt'.ltOrigin
              subst other; apply YjsLeq'.leqSame
            have h_lt : k < (leftIdx + (1 + ↑i)).toNat := by
              apply getElem_YjsLt'_index_lt arr k (leftIdx + (1 + i)).toNat harrinv
              rw [<-h_otherOrigin_arr_k] at otherOrigin_lt
              assumption
            omega
        . intros; simp; right; assumption
        . simp
    apply h_j_dest (by omega)


theorem idx_between_id_neq {i : ℕ} {newItem other : YjsItem A} {arr : Array (YjsItem A)}
  (horigin : ArrSet arr.toList newItem.origin)
  (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (harrinv : YjsArrInvariant arr.toList)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))
  (hleftIdx : findPtrIdx newItem.origin arr = Except.ok leftIdx)
  (hrightIdx : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx)
  (h_leftIdx_lt_i : leftIdx < i)
  (h_i_lt_rightIdx : i < rightIdx)
  (heq : arr[i]? = some other) :
  other.id ≠ newItem.id := by
  intros hcontra
  rw [getElem?_eq_some_iff] at heq
  obtain ⟨ _, heq ⟩ := heq
  have hor : YjsLeq' (A := A) other newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin other := by
    apply hsameid_consistent other
    subst other; simp [ArrSet]
    subst other; assumption
  cases hor with
  | inl hleq =>
    have hlt : YjsLt' (A := A) newItem.origin other := by
      apply findPtrIdx_lt_YjsLt' (arr := arr) (x := newItem.origin) (y := other) (j := i) harrinv hleftIdx
      . subst other
        rw [findPtrIdx_getElem]; assumption
      . omega
    apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed at hleq
    . contradiction
    . assumption
    . subst other; simp [ArrSet]
    . assumption
  | inr hleq =>
    have hlt : YjsLt' (A := A) other newItem.rightOrigin:= by
      apply findPtrIdx_lt_YjsLt' (arr := arr) (x := other) (y := newItem.rightOrigin) (i := i) harrinv _ hrightIdx
      . omega
      . subst other
        rw [findPtrIdx_getElem]; assumption
    apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed (by subst other; simp [ArrSet]) hrorigin hlt at hleq
    contradiction

theorem nDest_geq_i_lt_current_arr_i_origin_eq_newItem_origin_or_arr_nDest_lt_arr_i_origin {A : Type}
  [inst : DecidableEq A] (newItem : YjsItem A) (arr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin)
  (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))
  (harrinv : YjsArrInvariant arr.toList)
  (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx) (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx) (hleftIdxrightIdx : leftIdx < rightIdx)
  (next : ForInStep (MProd ℤ Bool)) (i : ℕ) (hlt2 : i < (rightIdx - leftIdx).toNat - 1) (other : YjsItem A)
  (hother : getElemExcept arr (leftIdx + (1 + ↑i)).toNat = Except.ok other) (oLeftIdx : ℤ)
  (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx) (oRightIdx : ℤ)
  (hoRightIdx : findPtrIdx other.rightOrigin arr = Except.ok oRightIdx) (dest : ℤ) (scanning : Bool)
  (h_cand : scanning = true → ∃ (h_dest_lt : dest.toNat < arr.size), arr[dest.toNat].origin = newItem.origin)
  (h_leftIdx : -1 ≤ leftIdx) (h_rightIdx : rightIdx ≤ ↑arr.size) (nDest : ℤ) (nScanning : Bool)
  (hnexteq : next.value = ⟨nDest, nScanning⟩) (hrightIdx : 0 ≤ rightIdx) (hlt : i < (rightIdx - leftIdx).toNat - 1)
  (hinv : loopInv arr newItem leftIdx (max rightIdx 0) (some (1 + i)) (ForInStep.yield ⟨dest, scanning⟩))
  (hbody :
    next =
      if oLeftIdx < leftIdx then ForInStep.done ⟨dest, scanning⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, false⟩
          else if oRightIdx = rightIdx then ForInStep.done ⟨dest, scanning⟩ else ForInStep.yield ⟨dest, true⟩
        else
          if scanning = false then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, scanning⟩
          else ForInStep.yield ⟨dest, scanning⟩)
  (hidx : 0 < 1 + i ∧ 1 + ↑i < max rightIdx 0 - leftIdx)
  (hdest_current :
    dest ≤ ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_not_scanning :
    scanning = false →
      isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = false →
        dest = ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_lt_item :
    ∀ (i : ℕ),
      ↑i < dest →
        ∀ (h_i_lt : i < arr.size),
          YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLeq' (A := A) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (A := A) (YjsPtr.itemPtr newItem) item)
  (hnext_dest :
    nDest =
      if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then if other.id < newItem.id then leftIdx + (1 + ↑i) + 1 else dest
        else if scanning = false then leftIdx + (1 + ↑i) + 1 else dest)
  (hnext_scanning :
    nScanning =
      if oLeftIdx < leftIdx then scanning
      else
        if oLeftIdx = leftIdx then !decide (other.id < newItem.id) && (!decide (oRightIdx = rightIdx) || scanning)
        else scanning)
  (nDest_eq : nDest = dest ∨ nDest = leftIdx + ↑(1 + i) + 1) (hlt_current : (leftIdx + (1 + ↑i)).toNat < arr.size)
  (heq : arr[(leftIdx + (1 + ↑i)).toNat] = other) (h_in_other : ArrSet (newItem :: arr.toList) (YjsPtr.itemPtr other))
  (h_in_other_origin : ArrSet (newItem :: arr.toList) other.origin)
  (h_other_origin_lt : YjsLt' (A := A) other.origin (YjsPtr.itemPtr other))
  (nDest_lt_size : nDest.toNat ≤ arr.size) (j : ℕ) (h_dest_i : nDest ≤ ↑j)
  (h_i_c :
    j <
      offsetToIndex leftIdx (max rightIdx 0) (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? (isBreak next)) :
  ∃ (i_lt_size : j < arr.size) (h_dest_lt : nDest.toNat < arr.size),
    arr[j].origin = newItem.origin ∧ newItem.id < arr[j].id ∨
      YjsLeq' (A := A) (YjsPtr.itemPtr arr[nDest.toNat]) arr[j].origin := by
  rw [Int.max_eq_left (a := rightIdx) (by omega)] at *
  have h_j_lt_arr_size : j < arr.size := by
    rw [offsetToIndex_range'_getElem (by assumption) (by assumption) (by omega)] at h_i_c
    split at h_i_c <;> omega
  have nDest_lt_arr_size : nDest.toNat < arr.size := by omega
  exists h_j_lt_arr_size, nDest_lt_arr_size
  rw [offsetToIndex_range'_getElem (by assumption) (by assumption) (by omega)] at h_i_c
  split at hbody
  . -- break case (oLeftIdx < leftIdx)
    have ⟨ heq1, heq2 ⟩ : nDest = dest ∧ nScanning = scanning := by
      subst next; cases hnexteq; simp
    subst next heq1 heq2
    simp [isBreak] at h_i_c
    simp [offsetToIndex, isBreak] at h_tbd
    obtain ⟨ _, _, h_tbd ⟩ := h_tbd j (by assumption) (by omega)
    apply h_tbd
  . split at hbody
    . -- oLeftIdx = leftIdx case
      split at hbody
      . -- other.id < newItem.id case
        have ⟨ heq1, heq2 ⟩ : nDest = leftIdx + (1 + ↑i) + 1 ∧ nScanning = false := by
          subst next; cases hnexteq; simp
        subst next heq1 heq2
        simp [isBreak] at h_i_c
        omega
      . -- other.id >= newItem.id case
        split at hbody
        . -- oRightIdx = rightIdx case
          have ⟨ heq1, heq2 ⟩ : nDest = dest ∧ nScanning = scanning := by
            subst next; cases hnexteq; simp
          subst next heq1 heq2
          simp [isBreak] at h_i_c
          simp [offsetToIndex, isBreak] at h_tbd
          obtain ⟨ _, _, h_tbd ⟩ := h_tbd j (by omega) (by omega)
          apply h_tbd
        . -- oRightIdx ≠ rightIdx case
          have ⟨ heq1, heq2 ⟩ : nDest = dest ∧ nScanning = true := by
            subst next; cases hnexteq; simp
          subst next heq1 heq2
          simp [isBreak] at h_i_c
          simp [offsetToIndex, isBreak] at h_tbd
          have hor : ↑j < leftIdx + (1 + ↑i) ∨ ↑j = leftIdx + (1 + ↑i):= by
            omega
          cases hor with
          | inl hlt =>
            obtain ⟨ _, _, h_tbd ⟩ := h_tbd j (by omega) (by omega)
            apply h_tbd
          | inr heq' =>
            left
            have h_j_eq : j = (leftIdx + (1 + ↑i)).toNat := by
              omega
            subst j
            rw [heq]
            constructor
            . have heq : oLeftIdx = leftIdx := by
                omega
              subst heq
              apply findPtrIdx_eq_ok_inj _ _ hoLeftIdx heqleft
            . have hneq : other.id ≠ newItem.id := by
                apply idx_between_id_neq (other := other) (i := (leftIdx + (1 + ↑i)).toNat) horigin hrorigin harrinv hsameid_consistent heqleft heqright
                . omega
                . omega
                . subst other; simp
              unfold ClientId at *
              omega
    . -- oLeftIdx > leftIdx case
      split at hbody
      . -- scanning = false case
        have ⟨ heq1, heq2 ⟩ : nDest = leftIdx + (1 + ↑i) + 1 ∧ nScanning = scanning := by
          subst next; cases hnexteq; simp
        subst next heq1 heq2
        simp [isBreak] at h_i_c
        omega
      . -- scanning = true case
        have ⟨ heq1, heq2 ⟩ : nDest = dest ∧ nScanning = true := by
            subst next; cases hnexteq; simp
            cases scanning
            . contradiction
            . simp
        subst next heq1 heq2
        simp [isBreak] at h_i_c
        simp [offsetToIndex, isBreak] at h_tbd
        have hor : ↑j < leftIdx + (1 + ↑i) ∨ ↑j = leftIdx + (1 + ↑i):= by
          omega
        cases hor with
        | inl hlt =>
          obtain ⟨ _, _, h_tbd ⟩ := h_tbd j (by omega) (by omega)
          apply h_tbd
        | inr heq' =>
          right
          have heq_other_arr_j : arr[j] = other := by
            subst other
            have heq : j = (leftIdx + (1 + ↑i)).toNat := by
              omega
            subst j; simp
          have h_YjsLeq'_arr_nDest_other : YjsLeq' (A := A) (YjsPtr.itemPtr arr[nDest.toNat]) other := by
            subst other
            apply getElem_leq_YjsLeq' _ _ _ harrinv
            omega

          have h_arr_nDest_origin_eq_newItem_origin : arr[nDest.toNat].origin = newItem.origin := by
            have h : scanning = true := by
              cases scanning
              . contradiction
              . simp
            obtain ⟨ _, _ ⟩ := h_cand h
            assumption

          have h_YjsLt'_arr_nDest_other : YjsLt' (A := A) (YjsPtr.itemPtr arr[nDest.toNat]) other := by
            cases yjs_leq'_imp_eq_or_yjs_lt' h_YjsLeq'_arr_nDest_other with
            | inr hlt =>
              assumption
            | inl heq =>
              have h_oLeftIdx_eq_leftIdx : oLeftIdx = leftIdx := by
                injection heq with heq
                have h_other_origin_eq_newItem_origin : other.origin = newItem.origin := by
                  rw [<-heq]
                  rw [h_arr_nDest_origin_eq_newItem_origin]

                have heq : Except.ok (ε := IntegrateError) oLeftIdx = Except.ok leftIdx := by
                  rw [h_other_origin_eq_newItem_origin] at hoLeftIdx
                  rw [<-hoLeftIdx, <-heqleft]

                injection heq

              contradiction

          have hor : YjsLeq' (A := A) other.origin arr[nDest.toNat].origin ∨
            YjsLeq' (A := A) (YjsPtr.itemPtr arr[nDest.toNat]) other.origin := by
            apply no_cross_origin harrinv.closed harrinv.item_set_inv _ _ h_YjsLt'_arr_nDest_other
            . simp [ArrSet]
            . subst other; simp [ArrSet]

          cases hor with
          | inr hleq =>
            rw [heq_other_arr_j]
            assumption
          | inl hleq =>
            have hleq : oLeftIdx ≤ leftIdx := by
              apply YjsLeq'_findPtrIdx_leq _ _ _ _ _ harrinv _ _ hleq hoLeftIdx; try assumption
              rw [h_arr_nDest_origin_eq_newItem_origin]
              assumption
              . obtain ⟨ o, r, id, c ⟩ := other; simp [YjsItem.origin]
                apply harrinv.closed.closedLeft o r id c
                rw [<-heq_other_arr_j]
                simp [ArrSet]
              . generalize h_eq : arr[nDest.toNat] = arr_nDest at *
                obtain ⟨ o, r, id, c ⟩ := arr_nDest; simp [YjsItem.origin]
                apply harrinv.closed.closedLeft o r id c
                rw [<-h_eq]
                simp [ArrSet]

            omega

theorem scanning_dest_origin_eq_newItem_origin_preserve {A : Type} [inst : DecidableEq A] (newItem : YjsItem A)
  (arr : Array (YjsItem A))
  (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx) (rightIdx : ℤ) (next : ForInStep (MProd ℤ Bool))
  (i : ℕ) (other : YjsItem A) (oLeftIdx : ℤ) (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx)
  (oRightIdx : ℤ) (dest : ℤ) (scanning : Bool)
  (h_cand : scanning = true → ∃ (h_dest_lt : dest.toNat < arr.size), arr[dest.toNat].origin = newItem.origin)
  (h_leftIdx : -1 ≤ leftIdx) (nDest : ℤ) (nScanning : Bool) (hnexteq : next.value = ⟨nDest, nScanning⟩)
  (hinv : loopInv arr newItem leftIdx (max rightIdx 0) (some (1 + i)) (ForInStep.yield ⟨dest, scanning⟩))
  (hbody :
    next =
      if oLeftIdx < leftIdx then ForInStep.done ⟨dest, scanning⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, false⟩
          else if oRightIdx = rightIdx then ForInStep.done ⟨dest, scanning⟩ else ForInStep.yield ⟨dest, true⟩
        else
          if scanning = false then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, scanning⟩
          else ForInStep.yield ⟨dest, scanning⟩)
  (hdest_current :
    dest ≤ ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_not_scanning :
    scanning = false →
      isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = false →
        dest = ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_lt_item :
    ∀ (i : ℕ),
      ↑i < dest →
        ∀ (h_i_lt : i < arr.size),
          YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLeq' (A := A) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (A := A) (YjsPtr.itemPtr newItem) item)
  (hnext_dest :
    nDest =
      if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then if other.id < newItem.id then leftIdx + (1 + ↑i) + 1 else dest
        else if scanning = false then leftIdx + (1 + ↑i) + 1 else dest)
  (hnext_scanning :
    nScanning =
      if oLeftIdx < leftIdx then scanning
      else
        if oLeftIdx = leftIdx then !decide (other.id < newItem.id) && (!decide (oRightIdx = rightIdx) || scanning)
        else scanning)
  (nDest_eq : nDest = dest ∨ nDest = leftIdx + ↑(1 + i) + 1) (hlt_current : (leftIdx + (1 + ↑i)).toNat < arr.size)
  (heq : arr[(leftIdx + (1 + ↑i)).toNat] = other)
  (nDest_lt_size : nDest.toNat ≤ arr.size) :
  nScanning = true → ∃ (h_dest_lt : nDest.toNat < arr.size), arr[nDest.toNat].origin = newItem.origin := by
  intros h_scanning
  split at hbody; rw [hbody] at hnexteq; cases hnexteq
  . apply h_cand h_scanning
  split at hbody
  . split at hbody; rw [hbody] at hnexteq; cases hnexteq
    . contradiction
    . split at hbody <;> (rw [hbody] at hnexteq; cases hnexteq)
      . apply h_cand h_scanning
      . cases scanning with
        | true =>
          apply h_cand h_scanning
        | false =>
          have h_dest_eq : dest = ↑(offsetToIndex leftIdx (rightIdx ⊔ 0) (some (1 + i)) false) := by
            apply h_not_scanning (by simp)
            simp [isDone]
          simp [offsetToIndex] at h_dest_eq
          rw [Int.max_eq_left (by omega)] at h_dest_eq
          have h_dest_lt_size : dest.toNat < arr.size := by
            omega
          exists h_dest_lt_size
          subst dest oLeftIdx
          rw [heq]
          apply findPtrIdx_eq_ok_inj _ _ hoLeftIdx heqleft
  split at hbody <;> (rw [hbody] at hnexteq; cases hnexteq)
  . subst scanning
    contradiction
  . apply h_cand h_scanning

theorem isDone_true_newItem_lt_item {A : Type} [inst : DecidableEq A] (newItem : YjsItem A) (arr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin) (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (horigin_consistent : YjsLt' (A := A) newItem.origin newItem.rightOrigin)
  (hreachable_consistent :
    ∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
        YjsLeq' (A := A) x newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin x)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))
  (hneq : ∀ x ∈ arr, ¬x = newItem) (harrinv : YjsArrInvariant arr.toList)
  (hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)))
  (harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList))) (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx) (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx) (hleftIdxrightIdx : leftIdx < rightIdx)
  (next : ForInStep (MProd ℤ Bool)) (i : ℕ) (hlt2 : i < (rightIdx - leftIdx).toNat - 1) (other : YjsItem A)
  (hother : getElemExcept arr (leftIdx + (1 + ↑i)).toNat = Except.ok other) (oLeftIdx : ℤ)
  (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx) (oRightIdx : ℤ)
  (hoRightIdx : findPtrIdx other.rightOrigin arr = Except.ok oRightIdx) (dest : ℤ) (scanning : Bool)
  (h_cand : scanning = true → ∃ (h_dest_lt : dest.toNat < arr.size), arr[dest.toNat].origin = newItem.origin)
  (h_leftIdx : -1 ≤ leftIdx) (h_rightIdx : rightIdx ≤ ↑arr.size) (nDest : ℤ) (nScanning : Bool)
  (hnexteq : next.value = ⟨nDest, nScanning⟩) (hrightIdx : 0 ≤ rightIdx) (hlt : i < (rightIdx - leftIdx).toNat - 1)
  (hinv : loopInv arr newItem leftIdx (max rightIdx 0) (some (1 + i)) (ForInStep.yield ⟨dest, scanning⟩))
  (hbody :
    next =
      if oLeftIdx < leftIdx then ForInStep.done ⟨dest, scanning⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, false⟩
          else if oRightIdx = rightIdx then ForInStep.done ⟨dest, scanning⟩ else ForInStep.yield ⟨dest, true⟩
        else
          if scanning = false then ForInStep.yield ⟨leftIdx + (1 + ↑i) + 1, scanning⟩
          else ForInStep.yield ⟨dest, scanning⟩)
  (hidx : 0 < 1 + i ∧ 1 + ↑i < max rightIdx 0 - leftIdx)
  (hdest_current :
    dest ≤ ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_not_scanning :
    scanning = false →
      isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = false →
        dest = ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))))
  (h_lt_item :
    ∀ (i : ℕ),
      ↑i < dest →
        ∀ (h_i_lt : i < arr.size),
          YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLeq' (A := A) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (A := A) (YjsPtr.itemPtr newItem) item)
  (hnext_dest :
    nDest =
      if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then if other.id < newItem.id then leftIdx + (1 + ↑i) + 1 else dest
        else if scanning = false then leftIdx + (1 + ↑i) + 1 else dest)
  (hnext_scanning :
    nScanning =
      if oLeftIdx < leftIdx then scanning
      else
        if oLeftIdx = leftIdx then !decide (other.id < newItem.id) && (!decide (oRightIdx = rightIdx) || scanning)
        else scanning)
  (nDest_eq : nDest = dest ∨ nDest = leftIdx + ↑(1 + i) + 1) (hlt_current : (leftIdx + (1 + ↑i)).toNat < arr.size)
  (heq : arr[(leftIdx + (1 + ↑i)).toNat] = other) (h_in_other : ArrSet (newItem :: arr.toList) (YjsPtr.itemPtr other))
  (h_in_other_origin : ArrSet (newItem :: arr.toList) other.origin)
  (h_other_origin_lt : YjsLt' (A := A) other.origin (YjsPtr.itemPtr other))
  (hdone : isDone next (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? = true) (item : YjsPtr A)
  (hitem :
    extGetElemExcept arr
        (offsetToIndex leftIdx (max rightIdx 0) (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]?
          (isBreak next)) =
      Except.ok item) :
  YjsLt' (A := A) (YjsPtr.itemPtr newItem) item := by
  rw [Int.max_eq_left (by omega)] at *
  rw [offsetToIndex_range'_getElem (by assumption) (by assumption) (by omega)] at *
  simp [isDone] at hdone
  have harr_other : ArrSet arr.toList (YjsPtr.itemPtr other) := by
    subst other; simp [ArrSet]
  have harr_other_origin : ArrSet arr.toList other.origin := by
    obtain ⟨ o, r, id, c ⟩ := other
    simp [YjsItem.origin]
    apply harrinv.closed.closedLeft o r id c
    rw [<-heq]
    simp [ArrSet]
  -- cases Nat.lt_or_ge (i + 1) ((rightIdx - leftIdx).toNat - 1) with
  cases next with
  | done next  =>
    -- rw [List.getElem?_range' (by omega)] at hdone
    -- simp at hdone
    -- cases next with
    -- | yield next =>
    --   cases hdone
    -- | done next =>
    simp [isBreak] at hitem
    have hor : oLeftIdx < leftIdx ∨ (oLeftIdx = leftIdx ∧ oRightIdx = rightIdx ∧ !(newItem.id > other.id)) := by
      split at hbody
      . left; assumption
      . split at hbody
        . split at hbody
          . cases hbody
          . split at hbody
            . right; constructor; assumption
              constructor; assumption
              simp
              assumption
            . cases hbody
        . split at hbody
          . cases hbody
          . cases hbody
    have hitem_eq_other : item = other := by
      have heq_idx : (↑((leftIdx + (↑i + 1) + 1).toNat - 1)  = leftIdx + ((1 : ℤ) + ↑i)) := by
        omega
      rw [heq_idx] at hitem
      unfold extGetElemExcept at hitem
      split at hitem; omega
      split at hitem; omega
      split at hitem; simp at *
      rw [Array.getElem?_eq_getElem (by omega), heq] at hitem
      simp at hitem
      cases hitem
      simp
    subst item
    have h_other_neq_newItem : other ≠ newItem := by
      apply hneq other
      subst other; simp
    cases hor with
    | inl hlt =>
      cases YjsLeq'_or_YjsLt' (x := other) (y := newItem) harrsetinv hclosed (by assumption) (by simp [ArrSet]) with
      | inr hlt =>
        apply hlt
      | inl hleq =>
        have hlt : YjsLt' (YjsPtr.itemPtr other) (YjsPtr.itemPtr newItem) := by
          cases yjs_leq'_imp_eq_or_yjs_lt' hleq with
          | inr hlt =>
            apply hlt
          | inl heq =>
            have heq : other = newItem := by
              cases heq
              simp
            contradiction
        apply no_cross_origin hclosed harrsetinv at hlt <;> try (subst other; simp [ArrSet])
        cases hlt with
        | inl hleq =>
          have hle_leftIdx_oLeftIdx : leftIdx ≤ oLeftIdx := by
            apply YjsLeq'_findPtrIdx_leq _ _ (x := newItem.origin) (y := other.origin) _ harrinv _ _ _ heqleft hoLeftIdx
            . assumption
            . assumption
            . assumption
          omega
        | inr hleq =>
          have hle_leftIdx_oLeftIdx : leftIdx + (1 + ↑i) ≤ leftIdx := by
            apply YjsLeq'_findPtrIdx_leq _ _ (x := other) (y := newItem.origin) _ harrinv _ _ hleq _ heqleft
            . subst other; simp [ArrSet]
            . assumption
            . subst other
              rw [findPtrIdx_getElem] <;> try assumption
              simp; omega
          omega
    | inr hcond =>
      obtain ⟨ h_oLeftIdx_eq_leftIdx, h_oRightIdx_eq_rightIdx, h_other_id_lt_newItem_id ⟩ := hcond
      have h_id_lt_id' : newItem.id < other.id := by
        simp at h_other_id_lt_newItem_id
        rw [Nat.not_lt_eq, Nat.le_iff_lt_or_eq] at h_other_id_lt_newItem_id
        cases h_other_id_lt_newItem_id with
        | inl =>
          assumption
        | inr heq =>
          have hor : YjsLeq' (A := A) other newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin other := by
            apply hsameid_consistent other
            subst other; simp [ArrSet]
            rw [heq]
          cases hor with
          | inl hleq =>
            have hlt : YjsLt' (A := A) newItem.origin other := by
              apply findPtrIdx_lt_YjsLt' (arr := arr) (x := newItem.origin) (y := other) (j := (leftIdx + (1 + ↑i))) harrinv heqleft
              . subst other
                rw [findPtrIdx_getElem] <;> try assumption
                simp; omega
              . omega
            apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed (by assumption) (by assumption) hlt at hleq
            contradiction
          | inr hleq =>
            have hlt : YjsLt' (A := A) other newItem.rightOrigin:= by
              apply findPtrIdx_lt_YjsLt' (arr := arr) (x := other) (y := newItem.rightOrigin) (i := (leftIdx + (1 + ↑i))) harrinv _ heqright
              . omega
              . subst other
                rw [findPtrIdx_getElem] <;> try assumption
                simp; omega
            apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed (by subst other; simp [ArrSet]) hrorigin hlt at hleq
            contradiction
      subst h_oLeftIdx_eq_leftIdx h_oRightIdx_eq_rightIdx
      apply YjsLt'.ltConflict
      obtain ⟨ o, r, id, c ⟩ := newItem
      obtain ⟨ o', r', id', c' ⟩ := other
      have h_o_eq_o' : o = o' := by
        simp [YjsItem.origin] at *
        apply findPtrIdx_eq_ok_inj _ _ heqleft hoLeftIdx
      have h_r_eq_r' : r = r' := by
        simp [YjsItem.origin] at *
        apply findPtrIdx_eq_ok_inj _ _ heqright hoRightIdx
      subst o r
      apply ConflictLt'.ltOriginSame
      . apply YjsLt'.ltRightOrigin
        apply YjsLeq'.leqSame
      . apply YjsLt'.ltRightOrigin
        . apply YjsLeq'.leqSame
      . assumption
  | yield h =>
    simp [isBreak] at hitem
    rw [Int.max_eq_left  (by omega)] at hitem
    simp at hdone
    generalize hoffset : (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? = offset at hdone
    have heq : offset = none := by
      cases offset <;> try simp
      simp at hdone
    subst offset
    rw [List.getElem?_eq_none_iff] at heq
    simp at heq
    replace heq : (leftIdx + (↑i + 1) + 1) = rightIdx := by
      omega
    rw [heq] at hitem
    have hitem : item = newItem.rightOrigin := by
      unfold extGetElemExcept at hitem
      generalize h_rightOrigin : newItem.rightOrigin = rightOrigin at *
      cases rightOrigin with
      | itemPtr rightOrigin =>
        obtain ⟨ r, h_rightIdx_eq, h_rightOrigin_eq ⟩ := findPtrIdx_item_exists arr rightOrigin heqright
        have heq : r = rightIdx.toNat := by
          rw [Int.mem_toNat?] at h_rightIdx_eq
          omega
        subst heq
        rw [h_rightOrigin_eq] at hitem
        simp at hitem
        have hlt : rightIdx < arr.size := by
          rw [Array.getElem?_eq_some_iff] at h_rightOrigin_eq
          obtain ⟨ _, _, _ ⟩ := h_rightOrigin_eq
          omega
        split at hitem; omega
        split at hitem; omega
        split at hitem; omega
        cases hitem; simp
      | first =>
        obtain ⟨ _, horigin_consistent ⟩ := horigin_consistent
        apply not_ptr_lt_first hclosed at horigin_consistent <;> try assumption
        contradiction
        obtain ⟨ o, r, id, c ⟩ := newItem
        simp [YjsItem.origin]
        apply hclosed.closedLeft o r id c
        simp [ArrSet]
      | last =>
        simp [findPtrIdx] at heqright
        cases heqright
        split at hitem; omega
        split at hitem
        . cases hitem; simp
        . contradiction
    subst hitem
    obtain ⟨ o, r, id, c ⟩ := newItem
    simp [YjsItem.rightOrigin]
    apply YjsLt'.ltRightOrigin
    apply YjsLeq'.leqSame

theorem loopInv_preserve1
  (newItem : YjsItem A)
  (arr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin)
  (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (horigin_consistent : YjsLt' (A := A) newItem.origin newItem.rightOrigin)
  (hreachable_consistent : ∀ (x : YjsPtr A),
    OriginReachable (YjsPtr.itemPtr newItem) x →
    YjsLeq' (A := A) x newItem.origin ∨ YjsLeq' (A := A) newItem.rightOrigin x)
  (hsameid_consistent : ∀ (x : YjsItem A),
    ArrSet arr.toList (YjsPtr.itemPtr x) →
    x.id = newItem.id →
      YjsLeq' (A := A) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (A := A) newItem.rightOrigin (YjsPtr.itemPtr x))
  (hneq : ∀ x ∈ arr, x ≠ newItem)
  (harrinv : YjsArrInvariant arr.toList)
  (hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)))
  (harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList)))
  (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx)
  (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx)
  (hleftIdxrightIdx : leftIdx < rightIdx)
  (hrightIdx : rightIdx ≥ 0)
  (state : MProd ℤ Bool)
  (next : ForInStep (MProd ℤ Bool))
  (i : ℕ)
  (hlt : i < (List.range' 1 ((rightIdx - leftIdx).toNat - 1)).length)
  (hlt2 : i < (rightIdx - leftIdx).toNat - 1)
  (hinv : loopInv arr newItem leftIdx (↑rightIdx.toNat) (some (1 + i)) (ForInStep.yield state))
  (other : YjsItem A)
  (hother : getElemExcept arr (leftIdx + ↑(1 + i)).toNat = Except.ok other)
  (oLeftIdx : ℤ)
  (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx)
  (oRightIdx : ℤ)
  (hoRightIdx : findPtrIdx other.rightOrigin arr = Except.ok oRightIdx)
  (hbody : next = (if oLeftIdx < leftIdx then ForInStep.done ⟨state.fst, state.snd⟩
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then ForInStep.yield ⟨(leftIdx + ↑(1 + i)) ⊔ 0 + 1, false⟩
          else
            if oRightIdx = rightIdx then ForInStep.done ⟨state.fst, state.snd⟩
            else ForInStep.yield ⟨state.fst, true⟩
        else
          if state.snd = false then ForInStep.yield ⟨(leftIdx + ↑(1 + i)) ⊔ 0 + 1, state.snd⟩
          else ForInStep.yield ⟨state.fst, state.snd⟩)) :
  loopInv arr newItem leftIdx (↑rightIdx.toNat)
    (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? next := by
  obtain ⟨ dest, scanning ⟩ := state
  have hnext_dest :
    next.value.fst = if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then
            (leftIdx + ↑(1 + i)) ⊔ 0 + 1
          else
            if oRightIdx = rightIdx then dest
            else dest
        else
          if scanning = false then (leftIdx + ↑(1 + i)).toNat + 1
          else dest := by
    subst hbody
    split
    simp
    split
    split
    simp
    simp
    split
    simp
    simp
    simp
    split
    simp
    simp
  have hnext_scanning : next.value.snd =
    if oLeftIdx < leftIdx then scanning
    else
      if oLeftIdx = leftIdx then
        if other.id < newItem.id then
          false
        else
          if oRightIdx = rightIdx then scanning
          else true
      else
        if scanning = false then scanning
        else scanning := by
    subst hbody
    split
    simp
    split
    split
    simp
    split
    simp
    simp
    split
    simp
    simp
  have hinv' := hinv
  obtain ⟨ hidx, hdest_current, h_not_scanning, h_lt_item, h_tbd, h_cand, h_done ⟩ := hinv'
  have h_leftIdx : -1 <= leftIdx := by
    apply findPtrIdx_ge_minus_1 at heqleft
    omega
  have h_rightIdx : rightIdx <= arr.size := by
    apply findPtrIdx_le_size at heqright
    omega
  unfold loopInv
  generalize hnexteq : next.value = nextValue at *
  obtain ⟨ nDest, nScanning ⟩ := nextValue
  simp at *
  rw [max_eq_left (a := leftIdx + (1 + ↑i)) (b := 0) (by omega)] at *
  have nDest_eq : nDest = dest ∨ nDest = leftIdx + ↑(1 + i) + 1 := by
    split at hnext_dest
    . left; assumption
    split at hnext_dest
    . split at hnext_dest
      . right; simp; assumption
      . left; assumption
    . split at hnext_dest
      . right; assumption
      . left; assumption

  have hlt_current : (leftIdx + (1 + ↑i)).toNat < arr.size := by
    omega
  have heq : arr[(leftIdx + (1 + ↑i)).toNat] = other := by
    simp [getElemExcept] at hother
    rw [Array.getElem?_eq_getElem hlt_current] at hother
    simp [pure, Except.pure] at hother
    assumption
  have h_in_other : ArrSet (newItem :: arr.toList) other := by
    subst other
    simp [ArrSet]
  have h_in_other_origin : ArrSet (newItem :: arr.toList) other.origin := by
    obtain ⟨ o, r, id, c ⟩ := other
    apply hclosed.closedLeft _ _ _ _ h_in_other
  have h_other_origin_lt : YjsLt' (A := A) other.origin other := by
    obtain ⟨ o, r, id, c ⟩ := other
    simp only [YjsItem.origin]
    apply YjsLt'.ltOrigin
    apply YjsLeq'.leqSame
  constructor
  . cases Nat.lt_or_ge (i + 1) (((rightIdx - leftIdx).toNat) - 1) with
    | inl h_i_lt =>
      rw [List.getElem?_range'] <;> try assumption
      simp
      omega
    | inr h_i_ge =>
      rw [List.getElem?_eq_none]
      simp
      simp
      omega
  constructor
  . cases Nat.lt_or_ge (i + 1) ((rightIdx - leftIdx).toNat - 1) with
    | inl h_i_lt =>
      rw [List.getElem?_range'] <;> try assumption
      simp [offsetToIndex] at *
      subst next nDest
      split; simp [isBreak]; omega
      split
      . split; simp [isBreak]; omega
        split; simp [isBreak]; omega
        simp [isBreak]; omega
      . split; simp [isBreak]; omega
        simp [isBreak]; omega
    | inr h_i_ge =>
      simp [offsetToIndex] at *
      rw [List.getElem?_eq_none (by rw [List.length_range']; omega)]
      simp
      subst next nDest
      split; simp [isBreak]; omega
      split
      . split; simp [isBreak]; omega
        split; simp [isBreak]; omega
        simp [isBreak]; omega
      . split; simp [isBreak]; omega
        simp [isBreak]; omega
  have nDest_lt_size : nDest.toNat <= arr.size := by
    simp [offsetToIndex] at *
    omega
  constructor
  . intros h_scanning_eq_false h_is_done
    rw [Int.max_eq_left (by assumption)]
    rw [offsetToIndex_range'_getElem (by assumption) (by assumption) (by omega)]
    revert hbody
    split
    . intros
      subst next
      simp [isDone] at h_is_done
    . split
      . split
        . intros hbody
          subst next
          simp at hnexteq
          obtain ⟨ h_dest, h_scanning ⟩ := hnexteq
          subst h_dest h_scanning
          simp [isBreak]
          omega
        . split
          . intros hbody
            subst hbody
            simp [isDone] at h_is_done
          . intros hbody
            subst hbody
            cases hnexteq
            contradiction
      . split
        . intros hbody
          subst hbody
          cases hnexteq
          simp [isBreak]
          omega
        . intros hbody
          subst hbody
          cases hnexteq
          contradiction
  constructor
  . -- extract_goal using dest_lt_YjsLt'_preserve
    apply dest_lt_YjsLt'_preserve
      newItem arr horigin hrorigin horigin_consistent
      hreachable_consistent hsameid_consistent hneq harrinv hclosed harrsetinv leftIdx heqleft rightIdx heqright
      hleftIdxrightIdx next i hlt other hother oLeftIdx hoLeftIdx oRightIdx hoRightIdx dest scanning
      h_cand h_leftIdx nDest nScanning hnexteq hrightIdx hlt hinv hbody hidx hdest_current h_not_scanning
      h_lt_item h_tbd h_done hnext_dest hnext_scanning nDest_eq hlt_current heq h_in_other h_in_other_origin h_other_origin_lt
      nDest_lt_size
  constructor
  . -- extract_goal using nDest_geq_i_lt_current_arr_i_origin_eq_newItem_origin_or_arr_nDest_lt_arr_i_origin
    apply nDest_geq_i_lt_current_arr_i_origin_eq_newItem_origin_or_arr_nDest_lt_arr_i_origin
      newItem arr horigin hrorigin hsameid_consistent harrinv
      leftIdx heqleft rightIdx heqright hleftIdxrightIdx next i hlt other hother oLeftIdx hoLeftIdx
      oRightIdx hoRightIdx dest scanning h_cand h_leftIdx h_rightIdx nDest nScanning hnexteq hrightIdx hlt hinv
      hbody hidx hdest_current h_not_scanning h_lt_item h_tbd h_done hnext_dest hnext_scanning nDest_eq
      hlt_current heq h_in_other h_in_other_origin h_other_origin_lt nDest_lt_size
  constructor
  . -- extract_goal using scanning_dest_origin_eq_newItem_origin_preserve
    apply scanning_dest_origin_eq_newItem_origin_preserve
      newItem arr leftIdx heqleft rightIdx next i other oLeftIdx hoLeftIdx oRightIdx dest scanning
      h_cand h_leftIdx nDest nScanning hnexteq hinv hbody hdest_current h_not_scanning
      h_lt_item h_tbd h_done hnext_dest hnext_scanning nDest_eq hlt_current heq nDest_lt_size
  . intros hdone item hitem
    -- extract_goal using isDone_true_newItem_lt_item
    apply isDone_true_newItem_lt_item
      newItem arr horigin hrorigin horigin_consistent hreachable_consistent hsameid_consistent hneq harrinv
      hclosed harrsetinv leftIdx heqleft rightIdx heqright hleftIdxrightIdx next i hlt other hother oLeftIdx hoLeftIdx
      oRightIdx hoRightIdx dest scanning h_cand h_leftIdx h_rightIdx nDest nScanning hnexteq hrightIdx hlt hinv
      hbody hidx hdest_current h_not_scanning h_lt_item h_tbd h_done hnext_dest hnext_scanning nDest_eq
      hlt_current heq h_in_other h_in_other_origin h_other_origin_lt hdone item hitem
