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
variable [BEq A]

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
        simp at hforin
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

def loop_invariant (P : ItemSet A) (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :=
  -- when x is none, we are done so current is rightIdx
  let current := offsetToIndex leftIdx rightIdx x
  let ⟨ dest, scanning ⟩ := state.value
  ∃ destItem,
    arr[dest]? = some destItem ∧
    (∀ i, i < dest -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P other newItem) ∧
    (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
      ∃ item : YjsItem A, arr[i]? = some item ∧
        (item.origin = newItem.origin ∧ newItem.id < item.id ∨
         YjsLt' P destItem item.origin)) ∧
    (scanning -> destItem.origin = newItem.origin) ∧
    (∀item : YjsItem A, getExcept arr current = Except.ok item -> YjsLt' P item newItem)

omit [BEq A] in theorem not_rightOrigin_first (P : YjsPtr A -> Prop) (item : YjsItem A) :
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

-- 補題: itemとの大小関係が保留の区間 [dest, i) について、もしarr[i] < item なら∀j ∈ [dest, i) でarr[j] < item
-- つまりループの終了条件が満たされたら[dest, i)のすべてでarr[j] < item
theorem loop_invariant_item_ordered {current} offset (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : ℤ) (state : ForInStep (MProd ℕ Bool)) :
  IsClosedItemSet (ArrSet (newItem :: arr.toList)) ->
  ItemSetInvariant (ArrSet (newItem :: arr.toList)) ->
  YjsArrInvariant arr.toList ->
  loop_invariant (ArrSet $ newItem :: arr.toList) arr newItem leftIdx rightIdx (some offset) state ->

  findIdx newItem.origin arr = Except.ok leftIdx ->
  findIdx newItem.rightOrigin arr = Except.ok rightIdx ->

  1 < offset ->
  offset < rightIdx - leftIdx ->
  current = offsetToIndex leftIdx rightIdx (some offset) ->

  (h_i_size : current < arr.size) ->
  YjsLt' (ArrSet $ newItem :: arr.toList) arr[current] newItem ->
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
  unfold loop_invariant at hloopinv
  have heq : state.value = ⟨dest, scanning⟩ := by
    subst h_dest_def
    subst h_scanning
    cases state <;> eq_refl
  rw [heq] at hloopinv
  obtain ⟨ destItem, h_dest, h_lt_item, h_tbd, h_cand, h_done ⟩ := hloopinv
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
        apply not_rightOrigin_first _ _ hclosed hinv at h_ro_eq
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
          sorry

        have h_k_current : k < (leftIdx + offset).toNat := by
          sorry

        obtain x := ih (ro.size) hsize k h_dest_k h_k_current (by rw [<-h_ro_in]; simp)
        simp at h_ro_in x
        rw [h_ro_in] at x
        assumption

    have ⟨ _, hlt_ro' ⟩ : YjsLt' (ArrSet $ newItem :: arr.toList) arr[j] newItem.rightOrigin := by
      have hlt : j < rightIdx := by
        omega
      have heq : findIdx arr[j] arr = Except.ok j := by
        sorry
      obtain x := findIdx_lt_YjsLt' arr _ _ harrinv heq hrightIdx hlt
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

theorem integrate_sound (A: Type) [BEq A] (P : ItemSet A) (inv : ItemSetInvariant P) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  -> integrate newItem arr = Except.ok newArr
  -> YjsArrInvariant newArr.toList := by
  intros hsorted hintegrate
  unfold integrate at hintegrate

  generalize heqleft : findIdx newItem.origin arr = leftIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ leftIdx ⟩ := leftIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  generalize heqright : findIdx newItem.rightOrigin arr = rightIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ rightIdx ⟩ := rightIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  simp at hintegrate

  generalize hloop :
    forIn (α := ℕ) (m := Except IntegrateError) (β := MProd ℕ Bool) (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1) ⟨(leftIdx + 1).toNat, false⟩ (fun offset r => do
      let other ← getExcept arr (leftIdx + ↑offset).toNat
      if r.snd = false then do
          let oLeftIdx ← findIdx other.origin arr
          let oRightIdx ← findIdx other.rightOrigin arr
          if oLeftIdx < leftIdx then pure (ForInStep.done ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
            else
              if oLeftIdx = leftIdx then
                if other.id < newItem.id then pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, false⟩)
                else
                  if oRightIdx = rightIdx then pure (ForInStep.done ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
                  else pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, true⟩)
              else pure (ForInStep.yield ⟨(leftIdx + ↑offset).toNat, r.snd⟩)
        else do
          let oLeftIdx ← findIdx other.origin arr
          let oRightIdx ← findIdx other.rightOrigin arr
          if oLeftIdx < leftIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
            else
              if oLeftIdx = leftIdx then
                if other.id < newItem.id then pure (ForInStep.yield ⟨r.fst, false⟩)
                else
                  if oRightIdx = rightIdx then pure (ForInStep.done ⟨r.fst, r.snd⟩)
                  else pure (ForInStep.yield ⟨r.fst, true⟩)
              else pure (ForInStep.yield ⟨r.fst, r.snd⟩)) = l at hintegrate

  obtain ⟨ _ ⟩ | ⟨ res ⟩ := l; cases hintegrate
  apply for_in_list_loop_invariant (I := fun x state => loop_invariant P arr newItem rightIdx.toNat x state) at hloop

  simp at hintegrate
  rw [<-hintegrate]
  -- Here, we prove that the array is still pairwise ordered after the integration.
  -- So, what we need is arr[res.first] < newItem < arr[res.first + 1] (and also, 0 <= res.first <= arr.size)
  . sorry
  . sorry
  . intros x state hloop i hlt heq hinv hbody
    rw [List.getElem_range'] at heq; simp at heq
    subst heq
    generalize hother : getExcept arr (leftIdx + ↑(1 + i)).toNat = other at hbody
    obtain ⟨ _ ⟩ | ⟨ other ⟩ := other; cases hbody
    rw [ok_bind] at hbody

    split at hbody
    all_goals (generalize hoLeftIdx : findIdx other.origin arr = oLeftIdx at hbody)
    all_goals (obtain ⟨ _ ⟩ | ⟨ oLeftIdx ⟩ := oLeftIdx; cases hbody)
    all_goals (rw [ok_bind] at hbody)

    all_goals (generalize hoRightIdx : findIdx other.rightOrigin arr = oRightIdx at hbody)
    all_goals (obtain ⟨ _ ⟩ | ⟨ oRightIdx ⟩ := oRightIdx; cases hbody)
    all_goals (rw [ok_bind] at hbody)

    simp at hbody
    rw [Int.toNat_add] at hbody
    rw [Int.toNat_add] at hbody
    simp at hbody

    simp at hlt


theorem integrate_commutative (A: Type) [BEq A] (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
