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

variable {A : Type}
variable [DecidableEq A]

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
        . apply hbody (i := 0) at heq <;> try first | simpa | assumption
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
        apply hbody (i := 0) at heq <;> try first | simpa | assumption
        simp at heq
        exists xs[0]?, ForInStep.done res
        constructor; constructor; constructor <;> try assumption
        simp

def offsetToIndex (leftIdx : ℤ) (rightIdx : ℤ) (offset : Option ℕ) : ℕ :=
  match offset with
  | none => rightIdx.toNat
  | some o => (leftIdx + o).toNat

def isDone (state : ForInStep (MProd ℕ Bool)) (x : Option ℕ) : Bool :=
  (match x with
  | none => true
  | some _ => false) ||
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def scannedItem arr (item newItem destItem : YjsItem A) :=
  (item.origin = newItem.origin ∧ newItem.id < item.id ∨ YjsLt' (ArrSet arr) destItem item.origin)

def loopInv (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :=
  -- when x is none, we are done so current is rightIdx
  let current := offsetToIndex leftIdx rightIdx x
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDone state x
  (match x with
    | none => True
    | some x => 0 < x ∧ x < rightIdx - leftIdx) ∧
  (dest < current) ∧
  ∃ destItem,
    arr[dest]? = some destItem ∧
    (∀ i, i < dest -> ∃ other : YjsItem A, arr[i]? = some other ∧ YjsLt' (ArrSet $ newItem :: arr.toList) other newItem) ∧
    (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
      ∃ item : YjsItem A, arr[i]? = some item ∧
        (item.origin = newItem.origin ∧ newItem.id < item.id ∨
         YjsLt' (ArrSet $ newItem :: arr.toList) destItem item.origin)) ∧
    (scanning -> destItem.origin = newItem.origin) ∧
    (done -> ∀item : YjsItem A, getElemExcept arr current = Except.ok item -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem item)

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
theorem loopInv_YjsLt' {current} offset (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : ℤ) (state : ForInStep (MProd ℕ Bool)) :
  IsClosedItemSet (ArrSet (newItem :: arr.toList)) ->
  ItemSetInvariant (ArrSet (newItem :: arr.toList)) ->
  YjsArrInvariant arr.toList ->
  loopInv arr newItem leftIdx rightIdx offset state ->

  findPtrIdx newItem.origin arr = Except.ok leftIdx ->
  findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx ->

  current = offsetToIndex leftIdx rightIdx offset ->
  (hcurrentlt : current ≤ arr.size) ->
  ((hlt : current < arr.size) -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[current]) ->
  ∀ j, (h_j_dest : state.value.fst ≤ j) ->
  (h_j_i : j < current) ->
  YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[j] := by

  intros hclosed hinv harrinv hloopinv hleftIdx hrightIdx hcurrent hcurrent_lt hi_lt j h_j_dest h_j_i
  generalize hsize : arr[j].size = size
  revert j
  generalize h_dest_def : state.value.fst = dest
  generalize h_scanning : state.value.snd = scanning
  apply Nat.strongRec' (p := fun size => ∀ (j : ℕ), dest ≤ j → ∀ (h_j_i : j < current), arr[j].size = size → YjsLt' _ newItem (YjsPtr.itemPtr arr[j]) )
  intros n ih j h_j_dest h_j_i heq_n
  subst heq_n
  unfold loopInv at hloopinv
  have heq : state.value = ⟨dest, scanning⟩ := by
    subst h_dest_def
    subst h_scanning
    cases state <;> eq_refl
  rw [heq] at hloopinv
  obtain ⟨ hsize, hdest_current, destItem, h_dest, h_lt_item, h_tbd, h_cand, h_done ⟩ := hloopinv
  -- simp [offsetToIndex] at h_tbd hcurrent
  subst hcurrent
  obtain ⟨ item, heq, h_tbd ⟩ := h_tbd j h_j_dest h_j_i
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
          simp [YjsItem.rightOrigin, YjsItem.origin]
          intros h_ro_eq
          subst h_ro_eq
          simp [YjsItem.size, YjsPtr.size]
          omega

        have h_dest_k : dest ≤ roIdx := by
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

        cases Nat.lt_or_ge roIdx (offsetToIndex leftIdx rightIdx offset) with
        | inl h_k_current =>
          obtain x := ih (ro.size) hsize roIdx h_dest_k h_k_current (by rw [<-h_ro_in]; simp)
          simp at h_ro_in x
          rw [h_ro_in] at x
          assumption
        | inr h_k_current =>
          -- newItem < arr[current] <= arr[k]
          have hlt : YjsLeq' (ArrSet $ newItem :: arr.toList) arr[(offsetToIndex leftIdx rightIdx offset)] ro := by
            subst h_ro_in
            apply yjs_leq'_mono (P := ArrSet arr.toList) (Q := ArrSet $ newItem :: arr.toList) <;> try assumption
            . apply harrinv.closed
            . apply harrinv.item_set_inv
            . intros a; cases a <;> try simp [ArrSet]
              intros; right; assumption
            apply getElem_leq_YjsLeq' arr (offsetToIndex leftIdx rightIdx offset) roIdx harrinv (by omega) (by omega)
          apply yjs_leq'_p_trans2 hinv _ _ _ hclosed (hi_lt (by omega)) hlt

    have ⟨ _, hlt_ro' ⟩ : YjsLt' (ArrSet $ newItem :: arr.toList) arr[j] newItem.rightOrigin := by
      have hlt : j < rightIdx := by
        cases offset <;> simp [offsetToIndex] at h_j_i <;> omega
      have heq : findPtrIdx arr[j] arr = Except.ok j := by
        apply findPtrIdx_getElem; assumption
      obtain x := findPtrIdx_lt_YjsLt' arr _ _ harrinv heq hrightIdx hlt
      apply yjs_lt'_mono (P := ArrSet arr.toList) (Q := ArrSet $ newItem :: arr.toList) <;> try assumption
      apply harrinv.closed
      apply harrinv.item_set_inv
      intros a; cases a <;> try simp [ArrSet]
      intros; right; assumption

    rw [Array.getElem?_eq_some_iff] at heq
    obtain ⟨ _, heq ⟩ := heq
    rw [heq]
    rw [heq] at hlt_ro hlt_ro'
    obtain ⟨ o, r, id, c ⟩ := newItem
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
    cases x <;> try simp [ArrSet]
    rw [List.insertIdxIfInBounds_toArray]
    simp
    rw [List.mem_insertIdx]
    simp
    assumption

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
  (hneq : ∀ x ∈ arr.toList, x ≠ newItem)
  (harrinv : YjsArrInvariant arr.toList)
  (hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)))
  (harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList)))
  (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx)
  (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx)
  (hleftIdxrightIdx : leftIdx < rightIdx)
  (hrightIdx : rightIdx ≥ 0)
  (resState : MProd ℕ Bool)
  (state : MProd ℕ Bool)
  (next : ForInStep (MProd ℕ Bool))
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
  (hbody : next = (if oLeftIdx < leftIdx then (ForInStep.done (α := MProd ℕ Bool) ⟨state.fst, state.snd⟩)
            else
              if oLeftIdx = leftIdx then
                if other.id < newItem.id then (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, false⟩)
                else
                  if oRightIdx = rightIdx then (ForInStep.done ⟨state.fst, state.snd⟩)
                  else (ForInStep.yield ⟨state.fst, true⟩)
              else
                if state.snd = false then (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, state.snd⟩)
                else (ForInStep.yield ⟨state.fst, state.snd⟩))) :
  loopInv arr newItem leftIdx (↑rightIdx.toNat)
    (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? next := by
  obtain ⟨ dest, scanning ⟩ := state
  have hnext_dest :
    next.value.fst = if oLeftIdx < leftIdx then dest
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then (leftIdx + ↑(1 + i)).toNat
          else
            if oRightIdx = rightIdx then dest
            else dest
        else
          if scanning = false then (leftIdx + ↑(1 + i)).toNat
          else dest := by
    sorry
    -- subst hbody
    -- split
    -- simp
    -- split
    -- split
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
        if other.id < newItem.id then false
        else
          if oRightIdx = rightIdx then scanning
          else true
      else
        if scanning = false then scanning
        else scanning := by
    sorry
    -- subst hbody
    -- split
    -- simp
    -- split
    -- split
    -- simp
    -- split
    -- simp
    -- simp
    -- simp
    -- split
    -- simp
    -- simp
  have hinv' := hinv
  obtain ⟨ hidx, hdest_current, destItem, h_dest, h_lt_item, h_tbd, h_cand, h_done ⟩ := hinv'
  have h_leftIdx : -1 <= leftIdx := by
    apply findPtrIdx_ge_minus_1 at heqleft
    omega
  have h_leftIdx : rightIdx <= arr.size := by
    apply findPtrIdx_le_size at heqright
    omega

  unfold loopInv
  generalize hnexteq : next.value = nextValue at *
  obtain ⟨ nDest, nScanning ⟩ := nextValue
  simp at *
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
  . cases Nat.lt_or_ge (i + 1) (((rightIdx - leftIdx).toNat) - 1) with
    | inl h_i_lt =>
      rw [List.getElem?_range'] <;> try assumption
      simp [offsetToIndex] at *
      subst nDest
      split <;> omega
    | inr h_i_ge =>
      simp [offsetToIndex] at *
      rw [List.getElem?_eq_none (by rw [List.length_range']; omega)]
      subst nDest
      simp
      split <;> omega
  have nDest_lt_size : nDest < arr.size := by
    simp [offsetToIndex] at *
    subst nDest
    split <;> omega
  exists arr[nDest]
  constructor
  . simp
  constructor
  . -- ∀ i < nDest, ∃ other,
    --   arr[i]? = some other ∧ YjsLt' (ArrSet (newItem :: arr.toList)) (YjsPtr.itemPtr other) (YjsPtr.itemPtr newItem)
    intros j h_j_lt
    exists arr[j]
    constructor
    . simp
    . subst nDest
      split at h_j_lt
      . obtain ⟨ other, heq, hlt ⟩ := h_lt_item j h_j_lt
        have heq : other = arr[j] := by
          rw [Array.getElem?_eq_some_iff] at heq
          obtain ⟨ _, heq ⟩ := heq
          subst heq
          simp
        subst other
        assumption
      . sorry
  sorry

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
  have heqset : ∀ x, ArrSet (newItem :: arr.toList) x ↔ ArrSet (List.insertIdx i newItem arr.toList) x := by
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

  have hsubset a : (ArrSet arr.toList) a -> (ArrSet (List.insertIdx i newItem arr.toList)) a := by
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
      simp [ArrSet]
      subst heq
      simp

theorem if_app (α β : Type) (f : α -> β) (P : Prop) [Decidable P] (x y : α):
  f (if decide P then x else y) = if decide P then f x else f y := by
  cases decide P with
  | true => simp
  | false => simp

theorem integrate_preserve (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  ArrSet arr.toList newItem.origin
  -> ArrSet arr.toList newItem.rightOrigin
  -> YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin
  -> (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
      YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  -> (∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
      x.id = newItem.id →
      YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))
  -> (∀ x ∈ arr.toList, x ≠ newItem)
  -> YjsArrInvariant arr.toList
  -> integrate newItem arr = Except.ok newArr
  -> YjsArrInvariant newArr.toList := by
  intros horigin hrorigin horigin_consistent hreachable_consistent hsameid_consistent hneq harrinv hintegrate
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
    forIn (α := ℕ) (m := Except IntegrateError) (β := MProd ℕ Bool) (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1) ⟨(leftIdx + 1).toNat, false⟩ (fun offset r => do
      let other ← getElemExcept arr (leftIdx + ↑offset).toNat
      let oLeftIdx ← findPtrIdx other.origin arr
      let oRightIdx ← findPtrIdx other.rightOrigin arr
      if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
        else
          if oLeftIdx = leftIdx then
            if other.id < newItem.id then pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, false⟩)
            else
              if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
              else pure (ForInStep.yield ⟨r.fst, true⟩)
          else
            if r.snd = false then pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
            else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = l at hintegrate

  obtain ⟨ _ ⟩ | ⟨ resState ⟩ := l; cases hintegrate
  apply for_in_list_loop_invariant (I := fun x state => loopInv arr newItem leftIdx rightIdx.toNat x state) at hloop
  . -- Here, we prove that the array is still pairwise ordered after the integration.
    -- So, what we need is arr[res.first] < newItem < arr[res.first + 1] (and also, 0 <= res.first <= arr.size)
    simp at hintegrate
    rw [<-hintegrate]
    obtain ⟨ offset, res', hres', hloopInv, hdone ⟩ := hloop
    have h_resState : resState.fst ≤ arr.size := by
      apply findPtrIdx_le_size at heqright
      unfold loopInv at *
      sorry
    apply YjsArrInvariant_insertIdxIfInBounds arr newItem resState.fst hclosed harrsetinv harrinv h_resState
    . intros hi0
      simp [loopInv] at hloopInv
      obtain ⟨ hidx, hdest_current, dest, hdest, hlt, htbd1, htbd2, hdone ⟩ := hloopInv
      subst hres'
      obtain ⟨ other, hothereq, hlt ⟩  := hlt (res'.value.fst - 1) (by omega)
      rw [Array.getElem?_eq_some_iff] at hothereq
      obtain ⟨ _, hothereq ⟩ := hothereq
      rw [hothereq]
      assumption
    . have current_lt : offsetToIndex leftIdx rightIdx offset ≤ arr.size := by
        obtain ⟨ hidx, dest, hdest, hlt, htbd1, htbd2, hdone ⟩ := hloopInv
        apply findPtrIdx_le_size at heqright
        cases offset <;> simp [offsetToIndex] <;> omega
      intros hisize
      apply loopInv_YjsLt' (current := offsetToIndex leftIdx rightIdx offset) <;> try assumption
      . simp
        rw [max_eq_left hrightIdx]
        assumption
      . simp
        rw [max_eq_left hrightIdx]
      . intros hlt
        simp [loopInv] at hloopInv
        obtain ⟨ hidx, hdest_current, dest, hdest, hlt', htbd1, htbd2, hdone' ⟩ := hloopInv
        apply hdone'
        . cases hdone with
          | inl hdone =>
            subst hdone
            simp [isDone]
          | inr hdone =>
            subst hdone
            simp [isDone]
        . rw [max_eq_left hrightIdx]
          simp [getElemExcept]
          rw [Array.getElem?_eq_getElem hlt]
          simp
          eq_refl
      . subst hres'
        simp
      . subst hres'
        obtain ⟨ hidx, hdest_current, dest, hdest, hlt', htbd1, htbd2, hdone' ⟩ := hloopInv
        assumption
    . intros
      apply hneq
      simp
      assumption
  . -- initial
    sorry
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

    let next : (ForInStep (MProd ℕ Bool)) :=
      if oLeftIdx < leftIdx then (ForInStep.done (α := MProd ℕ Bool) ⟨state.fst, state.snd⟩)
      else
        if oLeftIdx = leftIdx then
          if other.id < newItem.id then (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, false⟩)
          else
            if oRightIdx = rightIdx then (ForInStep.done ⟨state.fst, state.snd⟩)
            else (ForInStep.yield ⟨state.fst, true⟩)
        else
          if state.snd = false then (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, state.snd⟩)
          else (ForInStep.yield ⟨state.fst, state.snd⟩)
    have hnext : hloop = next := by
      suffices Except.ok (ε := IntegrateError) hloop = Except.ok next by
        simp at this
        assumption
      rw [<-hbody]
      unfold next
      simp
      repeat' rw [ok_bind]
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

theorem integrate_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
