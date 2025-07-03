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

lemma ok_bind {α β ε : Type} (x : α) (f : α -> Except β ε) :
  (do
    let x <- Except.ok x
    f x) = f x := by
  eq_refl

lemma for_in_list_loop_invariant {α β ε : Type} (ls : List α) (init : β) (body : α -> β -> Except ε (ForInStep β)) (I : Option α -> ForInStep β -> Prop) :
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

def loop_invariant (P : ItemSet A) (arr : Array (YjsItem A)) (newItem : YjsItem A) (rightIdx : ℕ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :=
  let isDone := match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false
  -- when x is none, we are done so current is rightIdx
  let current := x.getD rightIdx
  -- when break, loop invariant is not satisfied, so we use last value of current
  let lastChecked := if isDone then current - 1 else current
  let ⟨ dest, scanning ⟩ := state.value
  ∃ destItem,
    arr[dest]? = some destItem ∧
    (∀ i, i < dest -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P other newItem) ∧
    (∀ i, dest ≤ i -> i < lastChecked ->
      ∃ item : YjsItem A, some item = arr[i]? ∧
      (item.origin = newItem.origin ∧ newItem.id < item.id) ∨
      (YjsLt' P destItem item.origin)) ∧
    (scanning -> destItem.origin = newItem.origin) ∧
    (isDone -> ∃ item : YjsItem A, arr[current]? = some item ∧ YjsLt' P item newItem)

-- 補題: itemとの大小関係が保留の区間 [dest, i) について、もしarr[i] < item なら∀j ∈ [dest, i) でarr[j] < item
-- つまりループの終了条件が満たされたら[dest, i)のすべてでarr[j] < item
lemma loop_invariant_item_ordered (P : ItemSet A) (arr : Array (YjsItem A)) (newItem : YjsItem A) (rightIdx : ℕ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :
  loop_invariant P arr newItem rightIdx (some i) state ->
  (h_i_size : i < arr.size) ->
  YjsLt' P arr[i] newItem ->
  (∀ j, (h_j_dest : state.value.fst ≤ j) -> (h_j_i : j < i) -> YjsLt' P arr[j] newItem) := by
  intros hinv h_i_size hi_lt j h_j_dest h_j_i
  generalize hsize : arr[j].size = size
  revert j
  generalize h_dest_def : state.value.fst = dest
  apply Nat.strongRec' (p := fun size => ∀ (j : ℕ), dest ≤ j → ∀ (h_j_i : j < i), arr[j].size = size → YjsLt' P (YjsPtr.itemPtr arr[j]) (YjsPtr.itemPtr newItem))
  intros n ih j h_j_dest h_j_i heq_n
  subst heq_n

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
