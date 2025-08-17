import Mathlib.Tactic.WLOG
import Mathlib.Tactic.ExtractGoal

import LeanYjs.ListExtra
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ActorId
import LeanYjs.ItemOrder
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity
import LeanYjs.AntiSymmetry
import LeanYjs.Integrate
import LeanYjs.YjsArray
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

def offsetToIndex (leftIdx : ℤ) (rightIdx : ℤ) (offset : Option ℕ) (isBreak: Bool): ℕ :=
  let back := if isBreak then 1 else 0
  match offset with
  | none => rightIdx.toNat - back
  | some o => (leftIdx + o).toNat - back

def isBreak (state : ForInStep (MProd ℤ Bool)) : Bool :=
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def isDone (state : ForInStep (MProd ℤ Bool)) (x : Option ℕ) : Bool :=
  (match x with
  | none => true
  | some _ => false) ||
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def scannedItem arr (item newItem destItem : YjsItem A) :=
  (item.origin = newItem.origin ∧ newItem.id < item.id ∨ YjsLt' (ArrSet arr) destItem item.origin)

def extGetElemExcept (arr : Array (YjsItem A)) (idx : Int) : Except IntegrateError (YjsPtr A) :=
  if idx = -1 then
    Except.ok YjsPtr.first
  else if idx = arr.size then
    Except.ok YjsPtr.last
  else
    if idx < 0 || idx >= arr.size then
      Except.error IntegrateError.notFound
    else
      match arr[idx.toNat]? with
      | some item => return item
      | none => Except.error IntegrateError.notFound

def loopInv (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ) (x : Option ℕ) (state : ForInStep (MProd ℤ Bool)) :=
  -- when x is none, we are done so current is rightIdx
  -- when break from loop, current goes back by 1
  let current := offsetToIndex leftIdx rightIdx x (isBreak state)
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDone state x
  (match x with
    | none => True
    | some x => 0 < x ∧ x < rightIdx - leftIdx) ∧
  (dest ≤ current) ∧
  (!scanning → !done -> dest = current) ∧
  let dest := dest.toNat;
  (∀ i : ℕ, i < dest -> (h_i_lt : i < arr.size)-> YjsLt' (ArrSet $ newItem :: arr.toList) arr[i] newItem) ∧
  (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
    ∃ (i_lt_size : i < arr.size) (h_dest_lt : dest < arr.size),
      (arr[i].origin = newItem.origin ∧ newItem.id < arr[i].id ∨
        YjsLt' (ArrSet $ newItem :: arr.toList) arr[dest] arr[i].origin)) ∧
  (scanning -> ∃ h_dest_lt : dest < arr.size, arr[dest].origin = newItem.origin) ∧
  (done -> ∀item : YjsPtr A, extGetElemExcept arr current = Except.ok item -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem item)

omit [DecidableEq A] in theorem not_rightOrigin_first (P : YjsPtr A -> Prop) (item : YjsItem A) :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  P item ->
  item.rightOrigin ≠ YjsPtr.first := by
  intros hclosed hinv hin heq
  have hlt : YjsLt' P item item.rightOrigin := by
    exists 1
    obtain ⟨ o, r, id, c ⟩ := item
    apply YjsLt.ltRightOrigin <;> try assumption
    left
    apply hclosed.closedRight <;> assumption
  obtain ⟨ _, hlt ⟩ := hlt
  rw [heq] at hlt
  apply not_ptr_lt_first at hlt <;> assumption

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
  ((hlt : current < arr.size) -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[current]) ->
  ∀ j : ℕ, (h_j_dest : state.value.fst ≤ j) ->
    (h_j_i : j ≤ current) -> (h_j_size : j < arr.size) ->
    YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[j] := by

  intros hclosed hinv harrinv hloopinv hleftIdx hrightIdx hcurrent hcurrent_lt hi_lt j h_j_dest h_j_i h_j_size
  generalize hsize : arr[j].size = size
  revert j
  generalize h_dest_def : state.value.fst = dest
  generalize h_scanning : state.value.snd = scanning
  apply Nat.strongRec' (p := fun size => ∀ (j : ℕ), dest ≤ j → (h_j_i : j ≤ current) -> (h_j_size : j < arr.size) -> arr[j].size = size → YjsLt' _ newItem (YjsPtr.itemPtr arr[j]) )
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

    have ⟨ _, hlt_ro ⟩ : YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[j].rightOrigin := by
      generalize h_ro_eq : arr[j].rightOrigin = ro at heq
      cases ro with
      | first =>
        apply not_rightOrigin_first _ arr[j] hclosed hinv at h_ro_eq
        contradiction
        simp [ArrSet]
      | last =>
        constructor
        apply YjsLt.ltOriginOrder
        simp [ArrSet]
        simp [ArrSet]
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
            have hlt : YjsLt' (ArrSet $ arr.toList) arr[j] arr[roIdx] := by
              rw [h_ro_in]
              generalize heq : arr[j] = arrj at *
              obtain ⟨ o, r, id, c ⟩ := arrj
              simp [YjsItem.rightOrigin] at h_ro_eq
              subst h_ro_eq
              exists 1
              have harrin : ArrSet arr.toList (YjsItem.item o (YjsPtr.itemPtr ro) id c) := by
                rw [<-heq]
                simp [ArrSet]
              apply YjsLt.ltRightOrigin <;> try assumption
              apply YjsLeq.leqSame
              apply harrinv.closed.closedRight <;> assumption

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
          have hlt : YjsLeq' (ArrSet $ newItem :: arr.toList) arr[offsetToIndex leftIdx rightIdx offset (isBreak state)] ro := by
            subst h_ro_in
            apply yjs_leq'_mono (P := ArrSet arr.toList) (Q := ArrSet $ newItem :: arr.toList) <;> try assumption
            . apply harrinv.closed
            . apply harrinv.item_set_inv
            . intros a; cases a <;> try simp [ArrSet]
              intros; right; assumption
            apply getElem_leq_YjsLeq' arr (offsetToIndex leftIdx rightIdx offset (isBreak state)) roIdx harrinv (by omega) (by omega)
          apply yjs_leq'_p_trans2 hinv _ _ _ hclosed (hi_lt (by omega)) hlt

    have ⟨ _, hlt_ro' ⟩ : YjsLt' (ArrSet $ newItem :: arr.toList) arr[j] newItem.rightOrigin := by
      have hlt : j < rightIdx := by
        cases offset <;> simp [offsetToIndex] at h_j_i <;> omega
      have heq : findPtrIdx arr[j] arr = Except.ok j := by
        apply findPtrIdx_getElem; assumption
      -- obtain x := findPtrIdx_lt_YjsLt' _ harrinv heq hrightIdx hlt
      -- apply yjs_lt'_mono (P := ArrSet arr.toList) (Q := ArrSet $ newItem :: arr.toList) <;> try assumption
      -- apply harrinv.closed
      -- apply harrinv.item_set_inv
      -- intros a; cases a <;> try simp [ArrSet]
      -- intros; right; assumption
      apply findPtrIdx_lt_YjsLt' _ harrinv heq hrightIdx hlt
      intros; simp; right; assumption
    -- rw [heq]
    -- rw [heq] at hlt_ro hlt_ro'
    obtain ⟨ o, r, id, c ⟩ := newItem
    generalize arr[j] = item at *
    obtain ⟨ oo, or, oid, oc ⟩ := item
    simp [YjsItem.origin, YjsItem.rightOrigin] at h_origin_eq hlt_ro hlt_ro'
    rw [h_origin_eq]
    rw [h_origin_eq] at hlt_ro'
    constructor
    apply YjsLt.ltConflict
    apply ConflictLt.ltOriginSame <;> try assumption
  | inr x =>
    sorry

omit [DecidableEq A] in theorem insertIdxIfInBounds_mem {arr : Array (YjsItem A)} :
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
  (horigin_consistent : YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin)
  (hreachable_consistent :
    ∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
        YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))
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
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr newItem) item)
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
  (h_other_origin_lt : YjsLt' (ArrSet (newItem :: arr.toList)) other.origin (YjsPtr.itemPtr other))
  (nDest_lt_size : nDest.toNat ≤ arr.size) : ∀ (i : ℕ),
  ↑i < nDest →
    ∀ (h_i_lt : i < arr.size),
      YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem) := by
  intros j h_j_lt h_j_lt_size
  subst nDest
  have h_j_dest :  j < dest.toNat → YjsLt' (ArrSet (newItem :: arr.toList)) arr[j] newItem := by
    intros
    obtain hlt := h_lt_item j (by omega) (by omega)
    assumption
  have h_newItem_origin_lt_other : YjsLt' (ArrSet (newItem :: arr.toList)) newItem.origin other := by
    apply findPtrIdx_lt_YjsLt' (i := leftIdx) (j := (leftIdx + (1 + ↑i)).toNat)  <;> try assumption
    . intros; simp; right; assumption
    . subst other; rw [findPtrIdx_getElem]; assumption
    . omega
  have h_other_lt_newItem_rightOrigin : YjsLt' (ArrSet (newItem :: arr.toList)) other newItem.rightOrigin := by
    apply findPtrIdx_lt_YjsLt' (i := (leftIdx + (1 + ↑i)).toNat) (j := rightIdx) <;> try assumption
    . intros; simp; right; assumption
    . subst other; rw [findPtrIdx_getElem]; assumption
    . omega
  split at h_j_lt <;> try (apply h_j_dest (by omega))
  split at h_j_lt
  . split at h_j_lt
    on_goal 2 => apply h_j_dest (by omega)
    apply yjs_leq'_p_trans1 (y := other) <;> try assumption
    -- . simp [ArrSet]
    -- . subst other; simp [ArrSet]
    -- . simp [ArrSet]
    . apply yjs_leq'_mono (P := ArrSet arr.toList)
      . apply harrinv.closed
      . apply harrinv.item_set_inv
      . intros a hlt;
        cases a <;> try simp [ArrSet] at *
        right; assumption
      subst other
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
      apply YjsLt'.ltOrigin <;> try assumption
      . simp [ArrSet]
      . simp [YjsItem.origin]
        exists 0; apply YjsLeq.leqSame; try assumption
        apply hclosed.closedLeft
        left
    . intros; simp; right; assumption
    . simp
  . -- leftIdx < oLeftIdx cases
    split at h_j_lt
    . apply yjs_leq'_p_trans1 (y := other) <;> try assumption
      . apply yjs_leq'_mono (P := ArrSet arr.toList) (Q := (ArrSet (newItem :: arr.toList))) <;> try assumption
        . apply harrinv.closed
        . apply harrinv.item_set_inv
        . intros a ha
          cases a with
          | first => simp [ArrSet]
          | last => simp [ArrSet]
          | itemPtr a =>
            simp [ArrSet] at ha
            simp [ArrSet]
            right; assumption
        subst other
        apply getElem_leq_YjsLeq' arr j (leftIdx + (1 + ↑i)).toNat harrinv
        omega
      . apply findPtrIdx_origin_leq_newItem_YjsLt' _ _ _ hclosed harrsetinv harrinv _ (by assumption) (by assumption) <;> try assumption
        . omega
        . omega
        . generalize h_other_origin_eq : other.origin = otherOrigin at *
          cases otherOrigin with
          | first =>
            apply YjsLt'.ltOriginOrder
            simp [ArrSet]
            simp [ArrSet]
            apply OriginLt.lt_first
          | last =>
            subst other
            obtain ⟨ _, h_other_origin_lt ⟩ := h_other_origin_lt
            apply not_last_lt_ptr harrsetinv at h_other_origin_lt; try assumption
            contradiction
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
            have otherOrigin_lt : YjsLt' (ArrSet arr.toList) otherOrigin arr[(leftIdx + (1 + ↑i)).toNat] := by
              rw [<-h_other_origin_eq]
              generalize h_other_eq : arr[(leftIdx + (1 + ↑i)).toNat] = other at *
              obtain ⟨ o, r, id, c ⟩ := other
              simp [YjsItem.origin]
              apply YjsLt'.ltOrigin
              rw [<-h_other_eq]
              simp [ArrSet]
              subst other; apply YjsLeq'.leqSame
              apply harrinv.closed.closedLeft o r id c
              rw [<-h_other_eq]
              simp [ArrSet]
            have h_lt : k < (leftIdx + (1 + ↑i)).toNat := by
              apply getElem_YjsLt'_index_lt arr k (leftIdx + (1 + i)).toNat harrinv
              rw [<-h_otherOrigin_arr_k] at otherOrigin_lt
              assumption
            omega
        . intros; simp; right; assumption
        . simp
    apply h_j_dest (by omega)

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
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr newItem) item)
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

omit [DecidableEq A] in theorem YjsLt_subset_in (P : ItemSet A) :
  IsClosedItemSet Q ->
  Q x -> Q y ->
  -- (∀x, Q x -> P x) ->
  YjsLt P h x y → YjsLt Q h x y := by
  intros hclosed hx hy hlt
  revert hlt x y
  apply Nat.strongRec' (p := fun h => ∀ x y, Q x -> Q y -> YjsLt P h x y → YjsLt Q h x y)
  intros n ih x y hx hy hlt
  cases hlt with
  | ltOrigin h x o r id c hPitem hleq =>
    apply YjsLt.ltOrigin <;> try assumption
    cases hleq with
    | leqSame _ hPx =>
      apply YjsLeq.leqSame; assumption
    | leqLt h _ _ hlt =>
      apply YjsLeq.leqLt; try assumption
      apply ih <;> try assumption
      omega
      apply hclosed.closedLeft; assumption
  | ltRightOrigin h x o r id c hPitem hleq =>
    apply YjsLt.ltRightOrigin <;> try assumption
    cases hleq with
    | leqSame _ hPx =>
      apply YjsLeq.leqSame; assumption
    | leqLt h _ _ hlt =>
      apply YjsLeq.leqLt ; try assumption
      apply ih <;> try assumption
      omega
      apply hclosed.closedRight; assumption
  | ltConflict h i1 i2 hlt =>
    apply YjsLt.ltConflict; try assumption
    cases hlt with
    | ltOriginDiff h1 h2 h3 h4 l1 l2 l3 l4 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
      apply ConflictLt.ltOriginDiff <;> try assumption
      . apply ih<;> try assumption
        . simp [max4]; omega
        . apply hclosed.closedLeft; assumption
        . apply hclosed.closedLeft; assumption
      . apply ih<;> try assumption
        . simp [max4]; omega
        . apply hclosed.closedRight; assumption
      . apply ih<;> try assumption
        . simp [max4]; omega
        . apply hclosed.closedLeft; assumption
      . apply ih<;> try assumption
        . simp [max4]; omega
        . apply hclosed.closedRight; assumption
    | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 hidlt =>
      apply ConflictLt.ltOriginSame <;> try assumption
      . apply ih<;> try assumption
        . omega
        . apply hclosed.closedRight; assumption
      . apply ih <;> try assumption
        . omega
        . apply hclosed.closedRight; assumption
  | ltOriginOrder hpx hpy hlt =>
    apply YjsLt.ltOriginOrder <;> try assumption

omit [DecidableEq A] in theorem YjsLt'_subset_in (P : ItemSet A) :
  IsClosedItemSet Q ->
  Q x -> Q y ->
  YjsLt' P x y → YjsLt' Q x y := by
  intros hclosed hx hy hlt
  obtain ⟨ h, hlt ⟩ := hlt
  exists h
  apply YjsLt_subset_in P hclosed hx hy hlt

omit [DecidableEq A] in theorem YjsLeq'_subset_in (P : ItemSet A) :
  IsClosedItemSet Q ->
  Q x -> Q y ->
  YjsLeq' P x y → YjsLeq' Q x y := by
  intros hclosed hx hy hleq
  apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
  cases hleq with
  | inl heq =>
    subst heq
    exists 0
    apply YjsLeq.leqSame; assumption
  | inr hlt =>
    apply YjsLt'_subset_in P hclosed hx hy at hlt
    apply YjsLeq'.leqLt _ _ _ hlt

theorem isDone_true_newItem_lt_item {A : Type} [inst : DecidableEq A] (newItem : YjsItem A) (arr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin) (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (horigin_consistent : YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin)
  (hreachable_consistent :
    ∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
        YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  (hsameid_consistent :
    ∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
        x.id = newItem.id →
          YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
            YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))
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
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr newItem))
  (h_tbd :
    ∀ (i_1 : ℕ),
      dest ≤ ↑i_1 →
        i_1 < offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩)) →
          ∃ (i_lt_size : i_1 < arr.size) (h_dest_lt : dest.toNat < arr.size),
            arr[i_1].origin = newItem.origin ∧ newItem.id < arr[i_1].id ∨
              YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr arr[dest.toNat]) arr[i_1].origin)
  (h_done :
    isDone (ForInStep.yield ⟨dest, scanning⟩) (some (1 + i)) = true →
      ∀ (item : YjsPtr A),
        extGetElemExcept arr
              ↑(offsetToIndex leftIdx (max rightIdx 0) (some (1 + i)) (isBreak (ForInStep.yield ⟨dest, scanning⟩))) =
            Except.ok item →
          YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr newItem) item)
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
  (h_other_origin_lt : YjsLt' (ArrSet (newItem :: arr.toList)) other.origin (YjsPtr.itemPtr other))
  (hdone : isDone next (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? = true) (item : YjsPtr A)
  (hitem :
    extGetElemExcept arr
        (offsetToIndex leftIdx (max rightIdx 0) (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]?
          (isBreak next)) =
      Except.ok item) :
  YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr newItem) item := by
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
        have hlt : YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr other) (YjsPtr.itemPtr newItem) := by
          cases yjs_leq'_imp_eq_or_yjs_lt' hleq with
          | inr hlt =>
            apply hlt
          | inl heq =>
            have heq : other = newItem := by
              cases heq
              simp
            contradiction
        apply no_cross_origin hclosed harrsetinv at hlt
        cases hlt with
        | inl hleq =>
          have hle_leftIdx_oLeftIdx : leftIdx ≤ oLeftIdx := by
            apply YjsLeq'_findPtrIdx_leq _ _ (x := newItem.origin) (y := other.origin) _ harrinv _ heqleft hoLeftIdx
            apply YjsLeq'_subset_in _ harrinv.closed horigin harr_other_origin hleq
          omega
        | inr hleq =>
          have hleq : YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr other) newItem.origin := by
            apply YjsLeq'_subset_in _ harrinv.closed <;> try assumption
          have hle_leftIdx_oLeftIdx : leftIdx + (1 + ↑i) ≤ leftIdx := by
            apply YjsLeq'_findPtrIdx_leq _ _ (x := other) (y := newItem.origin) _ harrinv hleq _ heqleft
            subst other
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
          have hor : YjsLeq' (ArrSet arr.toList) other newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin other := by
            apply hsameid_consistent other
            subst other; simp [ArrSet]
            rw [heq]
          cases hor with
          | inl hleq =>
            have hlt : YjsLt' (ArrSet arr.toList) newItem.origin other := by
              apply findPtrIdx_lt_YjsLt' (arr := arr) (x := newItem.origin) (y := other) (j := (leftIdx + (1 + ↑i))) _ harrinv heqleft
              . subst other
                rw [findPtrIdx_getElem] <;> try assumption
                simp; omega
              . omega
              . intros; simp; assumption
            apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed hlt at hleq
            contradiction
          | inr hleq =>
            have hlt : YjsLt' (ArrSet arr.toList) other newItem.rightOrigin:= by
              apply findPtrIdx_lt_YjsLt' (arr := arr) (x := other) (y := newItem.rightOrigin) (i := (leftIdx + (1 + ↑i))) _ harrinv _ heqright
              . omega
              . intros; simp; assumption
              . subst other
                rw [findPtrIdx_getElem] <;> try assumption
                simp; omega
            apply yjs_lt_of_not_leq harrinv.item_set_inv _ _ harrinv.closed hlt at hleq
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
        . simp [ArrSet]
        . apply YjsLeq'.leqSame
          . apply hclosed.closedRight o' r' id c
            simp [ArrSet]
      . apply YjsLt'.ltRightOrigin
        . rw [<-heq]; simp [ArrSet]
        . apply YjsLeq'.leqSame
          . apply hclosed.closedRight o' r' id c
            simp [ArrSet]
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
        apply not_ptr_lt_first at horigin_consistent <;> try assumption
        contradiction
        apply harrinv.item_set_inv
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
    apply YjsLt'.ltRightOrigin <;> try simpa
    simp [ArrSet]
    apply YjsLeq'.leqSame
    apply hclosed.closedRight o r id c
    simp [ArrSet]

theorem loopInv_preserve1
  (newItem : YjsItem A)
  (arr newArr : Array (YjsItem A))
  (horigin : ArrSet arr.toList newItem.origin)
  (hrorigin : ArrSet arr.toList newItem.rightOrigin)
  (horigin_consistent : YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin)
  (hreachable_consistent : ∀ (x : YjsPtr A),
    OriginReachable (YjsPtr.itemPtr newItem) x →
    YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  (hsameid_consistent : ∀ (x : YjsItem A),
    ArrSet arr.toList (YjsPtr.itemPtr x) →
    x.id = newItem.id →
      YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))
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
  (resState : MProd ℤ Bool)
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
    sorry -- temporarily
    -- subst hbody
    -- split
    -- simp
    -- split
    -- split
    -- simp
    -- simp
    -- split
    -- simp
    -- simp
    -- simp
    -- split
    -- simp
    -- simp
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
    sorry -- temporarily
    -- subst hbody
    -- split
    -- simp
    -- split
    -- split
    -- simp
    -- split
    -- simp
    -- simp
    -- split
    -- simp
    -- simp
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
  have h_other_origin_lt : YjsLt' (ArrSet (newItem :: arr.toList)) other.origin other := by
    obtain ⟨ o, r, id, c ⟩ := other
    simp only [YjsItem.origin]
    apply YjsLt'.ltOrigin
    . apply h_in_other
    apply YjsLeq'.leqSame
    . apply h_in_other_origin
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
  . sorry -- temporary
  -- . intros h_scanning_eq_false h_is_done
  --   rw [Int.max_eq_left (by assumption)]
  --   rw [offsetToIndex_range'_getElem (by assumption) (by assumption) (by omega)]
  --   revert hbody
  --   split
  --   . intros
  --     subst next
  --     simp [isDone] at h_is_done
  --   . split
  --     . split
  --       . intros hbody
  --         subst next
  --         simp at hnexteq
  --         obtain ⟨ h_dest, h_scanning ⟩ := hnexteq
  --         subst h_dest h_scanning
  --         omega
  --       . split
  --         . intros hbody
  --           subst hbody
  --           simp [isDone] at h_is_done
  --         . intros hbody
  --           subst hbody
  --           cases hnexteq
  --           contradiction
  --     . split
  --       . intros hbody
  --         subst hbody
  --         cases hnexteq
  --         omega
  --       . intros hbody
  --         subst hbody
  --         cases hnexteq
  --         contradiction
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
  . sorry
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

theorem YjsArrInvariant_insertIdxIfInBounds (arr : Array (YjsItem A)) (newItem : YjsItem A) (i : ℕ) :
  IsClosedItemSet (ArrSet $ newItem :: arr.toList)
  -> ItemSetInvariant (ArrSet $ newItem :: arr.toList)
  -> YjsArrInvariant arr.toList
  -> (hisize : i ≤ arr.size)
  -> ((hizero : 0 < i) -> YjsLt' (ArrSet $ newItem :: arr.toList) arr[i - 1] newItem)
  -> ((hisize : i < arr.size) -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[i])
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
    . apply List.Pairwise_weaken (R := fun (a b : YjsItem A) => YjsLt' (ArrSet arr.toList) a b) <;> try assumption
      intros
      apply yjs_lt'_mono (P := ArrSet arr.toList) <;> assumption
    . intros j hji
      apply yjs_lt'_mono (P := ArrSet $ newItem :: arr.toList) <;> try assumption
      . intros
        rw [<-heqset]
        assumption
      . apply yjs_leq'_p_trans1 (y := arr[i - 1]) <;> try assumption
        . rw [List.pairwise_iff_getElem] at hsorted
          apply yjs_leq'_mono (P := ArrSet arr.toList) <;> try assumption
          cases Nat.lt_or_ge j (i - 1) with
          | inl hj_lt =>
            have hlt : YjsLt' (ArrSet arr.toList) (YjsPtr.itemPtr arr[j]) (YjsPtr.itemPtr arr[i - 1]) := by
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
            simp [ArrSet]
        . apply hlt1; omega
    . intros j hij hjlen
      apply yjs_lt'_mono (P := ArrSet $ newItem :: arr.toList) <;> try assumption
      . intros
        rw [<-heqset]
        assumption
      . simp at hjlen
        apply yjs_leq'_p_trans2 (y := YjsPtr.itemPtr arr[i]) <;> try assumption
        . apply hlt2
        . rw [List.pairwise_iff_getElem] at hsorted
          apply yjs_leq'_mono (P := ArrSet arr.toList) <;> try assumption
          cases Nat.lt_or_ge i j with
          | inl hj_lt =>
            have hlt : YjsLt' (ArrSet arr.toList) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr arr[j]) := by
              apply hsorted; try assumption
            obtain ⟨ h, hlt' ⟩ := hlt
            exists h + 1; right; assumption
          | inr hj_ge =>
            have heq : j = i := by omega
            subst heq
            simp
            exists 0; apply YjsLeq.leqSame; simp [ArrSet]
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

lemma findPtrIdx_lt_size_getElem {p : YjsPtr A} :
  findPtrIdx p arr = Except.ok idx →
  0 ≤ idx ->
  (h : idx.toNat < arr.size) →
  arr[idx.toNat] = p := by
  intros hfind hlt hsize
  unfold findPtrIdx at hfind
  cases p with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr p =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = p)) arr = idxOpt at hfind
    cases idxOpt <;> cases hfind
    rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, heq, _ ⟩ := heq
    simp at heq
    subst p
    simp

structure InsertOk (arr : Array (YjsItem A)) (newItem : YjsItem A) where
  origin_in : ArrSet arr.toList newItem.origin
  rightOrigin_in : ArrSet arr.toList newItem.rightOrigin
  origin_lt_rightOrigin : YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin
  reachable_YjsLeq' : (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
      YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  id_eq_YjsLeq' : (∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
      x.id = newItem.id →
      YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))
  not_mem : (∀ x ∈ arr, x ≠ newItem)

theorem YjsArrInvariant_integrate (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  -> InsertOk arr newItem
  -> integrate newItem arr = Except.ok newArr
  -> ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList := by
  intros harrinv h_InsertOk hintegrate
  obtain ⟨ horigin, hrorigin, horigin_consistent, hreachable_consistent, hsameid_consistent, hneq ⟩ :=
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
    apply YjsLt'_findPtrIdx_lt leftIdx rightIdx newItem.origin newItem.rightOrigin arr harrinv _ heqleft heqright
    apply horigin_consistent

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
      apply YjsLt'.ltOrigin _ _ _ _ _ _ (by simp [ArrSet])
      simp [YjsItem.origin] at *
      apply yjs_leq'_mono (P := ArrSet arr.toList) <;> try assumption
      . apply harrinv.closed
      . apply harrinv.item_set_inv
      . intros a hlt;
        simp [ArrSet] at *
        cases a <;> simp at *
        right; assumption

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
          . simp [ArrSet] at *
          . simp [ArrSet] at *
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
            . simp [ArrSet]
            . apply YjsLeq'.leqSame
              apply hclosed.closedRight o r id c
              simp [ArrSet]
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
      newItem arr newArr horigin hrorigin horigin_consistent hreachable_consistent hsameid_consistent hneq
      harrinv hclosed harrsetinv leftIdx heqleft rightIdx heqright hleftIdxrightIdx hrightIdx
      resState state hloop i hlt hlt2 hinv other hother oLeftIdx hoLeftIdx oRightIdx hoRightIdx hnext

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

theorem insertOk_mono (arr1 arr2 : Array (YjsItem A)) (x : YjsItem A) :
  YjsArrInvariant arr1.toList
  -> YjsArrInvariant arr2.toList
  -> (∀ a, a ∈ arr1 → a ∈ arr2)
  -> (∀ a, a ∈ arr2 → a ∉ arr1 -> a.id ≠ x.id)
  -> InsertOk arr1 x
  -> InsertOk arr2 x := by
  intros harrinv1 harrinv2 h_arr1_subset_arr2 h_id_neq h_InsertOk
  obtain ⟨ horigin, hrorigin, horigin_consistent, hreachable_consistent, hsameid_consistent, hneq ⟩ := h_InsertOk
  constructor <;> try assumption
  . apply subset_ArrSet h_arr1_subset_arr2
    assumption
  . apply subset_ArrSet h_arr1_subset_arr2
    assumption
  . apply yjs_lt'_mono (P := ArrSet arr1.toList)
    . apply harrinv1.closed
    . apply harrinv1.item_set_inv
    . intros
      apply subset_ArrSet h_arr1_subset_arr2; assumption
    apply horigin_consistent
  . intros y hreachable
    replace hreachable_consistent := hreachable_consistent y hreachable
    cases hreachable_consistent with
    | inl hleq =>
      left
      all_goals apply yjs_leq'_mono (P := ArrSet arr1.toList)
      . apply harrinv1.closed
      . apply harrinv1.item_set_inv
      . intros
        apply subset_ArrSet h_arr1_subset_arr2; assumption
      apply hleq
    | inr hleq =>
      right
      all_goals apply yjs_leq'_mono (P := ArrSet arr1.toList)
      . apply harrinv1.closed
      . apply harrinv1.item_set_inv
      . intros
        apply subset_ArrSet h_arr1_subset_arr2; assumption
      apply hleq
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
      all_goals apply yjs_leq'_mono (P := ArrSet arr1.toList)
      . apply harrinv1.closed
      . apply harrinv1.item_set_inv
      . intros
        apply subset_ArrSet h_arr1_subset_arr2; assumption
      apply hleq
    | inr hleq =>
      right
      all_goals apply yjs_leq'_mono (P := ArrSet arr1.toList)
      . apply harrinv1.closed
      . apply harrinv1.item_set_inv
      . intros
        apply subset_ArrSet h_arr1_subset_arr2; assumption
      apply hleq
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
  intros harrinv haid_neq_bid h_InsertOk_a h_InsertOk_b hintegrate_a hintegrate_b hintegrate_b' hintegrate_a'

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
    rw [heq] at haid_neq_bid
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
