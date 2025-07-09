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

def loopInv (P : ItemSet A) (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :=
  -- when x is none, we are done so current is rightIdx
  let current := offsetToIndex leftIdx rightIdx x
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDone state x
  (match x with
    | none => True
    | some x => 0 < x ∧ x < rightIdx - leftIdx) ∧
  ∃ destItem,
    arr[dest]? = some destItem ∧
    (∀ i, i < dest -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P other newItem) ∧
    (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
      ∃ item : YjsItem A, arr[i]? = some item ∧
        (item.origin = newItem.origin ∧ newItem.id < item.id ∨
         YjsLt' P destItem item.origin)) ∧
    (scanning -> destItem.origin = newItem.origin) ∧
    (done -> ∀item : YjsItem A, getElemExcept arr current = Except.ok item -> YjsLt' P item newItem)

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
theorem loop_invariant_item_ordered {current} offset (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : ℤ) (state : ForInStep (MProd ℕ Bool)) :
  IsClosedItemSet (ArrSet (newItem :: arr.toList)) ->
  ItemSetInvariant (ArrSet (newItem :: arr.toList)) ->
  YjsArrInvariant arr.toList ->
  loopInv (ArrSet $ newItem :: arr.toList) arr newItem leftIdx rightIdx (some offset) state ->

  findPtrIdx newItem.origin arr = Except.ok leftIdx ->
  findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx ->

  1 < offset ->
  offset < rightIdx - leftIdx ->
  current = offsetToIndex leftIdx rightIdx (some offset) ->

  (h_i_size : current < arr.size) ->
  YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[current] ->
  ∀ j, (h_j_dest : state.value.fst ≤ j) ->
  (h_j_i : j < current) ->
  YjsLt' (ArrSet $ newItem :: arr.toList) newItem arr[j] := by

  intros hclosed hinv harrinv hloopinv hleftIdx hrightIdx hoffset_gt hoffset_lt hcurrent h_i_size hi_lt j h_j_dest h_j_i
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
  obtain ⟨ hrange, destItem, h_dest, h_lt_item, h_tbd, h_cand, h_done ⟩ := hloopinv
  simp [offsetToIndex] at h_tbd hcurrent
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
        have ⟨ k, h_ro_in ⟩ : ∃ k : Fin arr.size, arr[k] = ro := by
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

        have h_dest_k : dest ≤ k := by
          obtain ⟨ k, _ ⟩ := k
          simp at *
          have hlt : j < k := by
            have hlt : YjsLt' (ArrSet $ arr.toList) arr[j] arr[k] := by
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
            have hltk : k < arr.size := by
              omega
            apply getElem_YjsLt'_index_lt arr j k harrinv hltj hltk hlt
          omega

        cases Nat.lt_or_ge k (leftIdx + offset).toNat with
        | inl h_k_current =>
          obtain x := ih (ro.size) hsize k h_dest_k h_k_current (by rw [<-h_ro_in]; simp)
          simp at h_ro_in x
          rw [h_ro_in] at x
          assumption
        | inr h_k_current =>
          -- newItem < arr[current] <= arr[k]
          have hlt : YjsLeq' (ArrSet $ newItem :: arr.toList) arr[(leftIdx + offset).toNat] ro := by
            subst h_ro_in
            apply yjs_leq'_mono (P := ArrSet arr.toList) (Q := ArrSet $ newItem :: arr.toList) <;> try assumption
            . apply harrinv.closed
            . apply harrinv.item_set_inv
            . intros a; cases a <;> try simp [ArrSet]
              intros; right; assumption
            apply getElem_leq_YjsLeq' arr (leftIdx + offset).toNat k harrinv (by omega) (by omega)
          apply yjs_leq'_p_trans2 hinv _ _ _ hclosed hi_lt hlt

    have ⟨ _, hlt_ro' ⟩ : YjsLt' (ArrSet $ newItem :: arr.toList) arr[j] newItem.rightOrigin := by
      have hlt : j < rightIdx := by
        omega
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
  (harrinv : YjsArrInvariant arr.toList)
  (hclosed : IsClosedItemSet (ArrSet (newItem :: arr.toList)))
  (harrsetinv : ItemSetInvariant (ArrSet (newItem :: arr.toList)))
  (leftIdx : ℤ)
  (heqleft : findPtrIdx newItem.origin arr = Except.ok leftIdx)
  (rightIdx : ℤ)
  (heqright : findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx)
  (hleftIdxrightIdx : leftIdx < rightIdx)
  (res : MProd ℕ Bool)
  (hintegrate : (fun a => arr.insertIdxIfInBounds a.fst newItem) <$> Except.ok (ε := IntegrateError) res = Except.ok newArr)
  (state : MProd ℕ Bool)
  (hloop : ForInStep (MProd ℕ Bool))
  (i : ℕ)
  (hinv : loopInv (ArrSet arr.toList) arr newItem leftIdx (↑rightIdx.toNat) (some (1 + i)) (ForInStep.yield state))
  (other : YjsItem A)
  (hother : getElemExcept arr (leftIdx + ↑(1 + i)).toNat = Except.ok other)
  -- h✝ : state.snd = false
  (oLeftIdx : ℤ)
  (hoLeftIdx : findPtrIdx other.origin arr = Except.ok oLeftIdx)
  (oRightIdx : ℤ)
  (hoRightIdx : findPtrIdx other.rightOrigin arr = Except.ok oRightIdx)
  -- hbody : (if oLeftIdx < leftIdx then pure (ForInStep.done ⟨(leftIdx + ↑(1 + i)).toNat, state.snd⟩)
  --   else
  --     if oLeftIdx = leftIdx then
  --       if other.id < newItem.id then pure (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, false⟩)
  --       else
  --         if oRightIdx = rightIdx then pure (ForInStep.done ⟨(leftIdx + ↑(1 + i)).toNat, state.snd⟩)
  --         else pure (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, true⟩)
  --     else pure (ForInStep.yield ⟨(leftIdx + ↑(1 + i)).toNat, state.snd⟩)) =
  --   Except.ok hloop
  : loopInv P arr newItem leftIdx (↑rightIdx.toNat) (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[i + 1]? hloop := by
  sorry

theorem integrate_sound (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
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
  -> YjsArrInvariant arr.toList
  -> integrate newItem arr = Except.ok newArr
  -> YjsArrInvariant newArr.toList := by
  intros horigin hrorigin horigin_consistent hreachable_consistent hsameid_consistent harrinv hintegrate
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

  simp at hintegrate

  generalize hloop :
    forIn (α := ℕ) (m := Except IntegrateError) (β := MProd ℕ Bool) (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1) ⟨(leftIdx + 1).toNat, false⟩ (fun offset r => do
      let other ← getElemExcept arr (leftIdx + ↑offset).toNat
      if r.snd = false then do
          let oLeftIdx ← findPtrIdx other.origin arr
          let oRightIdx ← findPtrIdx other.rightOrigin arr
          if oLeftIdx < leftIdx then pure (ForInStep.done ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
            else
              if oLeftIdx = leftIdx then
                if other.id < newItem.id then pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, false⟩)
                else
                  if oRightIdx = rightIdx then pure (ForInStep.done ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
                  else pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, true⟩)
              else pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
        else do
          let oLeftIdx ← findPtrIdx other.origin arr
          let oRightIdx ← findPtrIdx other.rightOrigin arr
          if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
            else
              if oLeftIdx = leftIdx then
                if other.id < newItem.id then pure (ForInStep.yield ⟨r.fst, false⟩)
                else
                  if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
                  else pure (ForInStep.yield ⟨r.fst, true⟩)
              else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = l at hintegrate

  obtain ⟨ _ ⟩ | ⟨ res ⟩ := l; cases hintegrate
  apply for_in_list_loop_invariant (I := fun x state => loopInv (ArrSet arr.toList) arr newItem leftIdx rightIdx.toNat x state) at hloop
  . simp at hintegrate
    rw [<-hintegrate]
    -- Here, we prove that the array is still pairwise ordered after the integration.
    -- So, what we need is arr[res.first] < newItem < arr[res.first + 1] (and also, 0 <= res.first <= arr.size)
    obtain ⟨ current, res, hreseq, hloopinv, hdone ⟩ :=  hloop
    constructor
    apply IsClosedItemSet.eq_set <;> try assumption
    . intros
      apply insertIdxIfInBounds_mem
      -- inserted position is in bounds
      sorry
    . apply ItemSetInvariant.eq_set <;> try assumption
      intros
      apply insertIdxIfInBounds_mem
      sorry
    . -- sorted
      sorry
    . -- unique
      sorry
  . -- initial
    sorry
  . intros x state hloop i hlt heq hinv hbody
    rw [List.getElem_range'] at heq; simp at heq
    subst heq
    generalize hother : getElemExcept arr (leftIdx + ↑(1 + i)).toNat = other at hbody
    obtain ⟨ _ ⟩ | ⟨ other ⟩ := other; cases hbody
    rw [ok_bind] at hbody

    split at hbody
    all_goals (generalize hoLeftIdx : findPtrIdx other.origin arr = oLeftIdx at hbody)
    all_goals (obtain ⟨ _ ⟩ | ⟨ oLeftIdx ⟩ := oLeftIdx; cases hbody)
    all_goals (rw [ok_bind] at hbody)

    all_goals (generalize hoRightIdx : findPtrIdx other.rightOrigin arr = oRightIdx at hbody)
    all_goals (obtain ⟨ _ ⟩ | ⟨ oRightIdx ⟩ := oRightIdx; cases hbody)
    all_goals (rw [ok_bind] at hbody)

    . simp at hbody
      split at hbody
      . -- case 1: oLeftIdx < leftIdx
        cases hbody
        simp [loopInv]
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

    . sorry

theorem integrate_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
