import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ItemOriginOrder
import LeanYjs.ActorId
import LeanYjs.ItemOrder
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity
import LeanYjs.AntiSymmetry
import LeanYjs.Integrate

variable {A : Type}
variable [BEq A]

def ArrSet (arr : Array (YjsItem A)) : YjsPtr A -> Prop :=
  fun a => match a with
  | YjsPtr.itemPtr item => item ∈ arr
  | YjsPtr.first => True
  | YjsPtr.last => True

def ArrSetClosed (arr : Array (YjsItem A)) : Prop :=
  IsClosedItemPredicate _ (ArrSet arr)

inductive ArrayPairwise {α : Type} (f : α -> α -> Prop) : Array α -> Prop where
| empty : ArrayPairwise f #[] -- empty array is pairwise
| push : ∀ (a : α) (arr : Array α),
  ArrayPairwise f arr -> (∀ b : α, b ∈ arr -> f b a)
  -> ArrayPairwise f (Array.push arr a) -- if the tail is pairwise, then adding an element is pairwise

lemma ok_bind {α β ε : Type} (x : α) (f : α -> Except β ε) :
  (do
    let x <- Except.ok x
    f x) = f x := by
  eq_refl

lemma for_in_list_loop_invariant {α β ε : Type} (ls : List α) (init : β) (body : α -> β -> Except ε (ForInStep β)) (I : Option α -> ForInStep β -> Prop) :
  I ls.head? (ForInStep.yield init) ->
  (∀ x (y : β) res i (hlt : i < ls.length),
    x = ls.get (Fin.mk i hlt) ->
    I x (ForInStep.yield y) ->
    body x y = Except.ok res ->
    I ls[i + 1]? res) ->
  ∀ res, forIn ls init body = Except.ok res ->
  ∃ x res', res'.value = res ∧ I x res' := by
  intros hinit hbody res hforin
  induction ls generalizing init with
  | nil =>
    cases hforin
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
        constructor; constructor; constructor <;> try assumption
        simp

def loop_invariant (P : ClosedPredicate A) (arr : Array (YjsItem A)) (newItem : YjsItem A) (rightIdx : ℕ) (x : Option ℕ) (state : ForInStep (MProd ℕ Bool)) :=
  let breaked := match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false
  let current := x.orElse (fun () => rightIdx)
  let ⟨ dest, scanning ⟩ := state.value
  (∀ i, i < dest -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P other newItem) ∧
  (scanning -> ∀ i, dest ≤ i -> i < current -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P newItem other.rightOrigin ->  YjsLt' P other newItem) ∧
  (scanning -> ∃ (destItem : YjsItem A), arr[dest]? = some destItem ∧ destItem.origin = newItem.origin)

theorem integrate_sound (A: Type) [BEq A] (P : ClosedPredicate A) (inv : ItemSetInvariant P) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  ArrayPairwise (fun (x y : YjsItem A) => YjsLt' P x y) arr
  -> integrate newItem arr = Except.ok newArr
  -> ArrayPairwise (fun (x y : YjsItem A) => YjsLt' P x y) newArr := by
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
    @forIn (Except IntegrateError) (List ℕ) ℕ instForInOfForIn' (MProd ℕ Bool) Except.instMonad
    (List.range' (leftIdx.toNat + 1) (rightIdx.toNat - (leftIdx.toNat + 1)) 1) ⟨leftIdx.toNat + 1, false⟩ (fun i r => do
      let other ← getExcept arr i
      if r.snd = false then do
          let oLeftIdx ← findIdx other.origin arr
          let oRightIdx ← findIdx other.rightOrigin arr
          if oLeftIdx < max leftIdx 0 then pure (ForInStep.done ⟨i, r.snd⟩)
            else
              if oLeftIdx = max leftIdx 0 then
                if other.id < newItem.id then pure (ForInStep.yield ⟨i, false⟩)
                else
                  if oRightIdx = max rightIdx 0 then pure (ForInStep.done ⟨i, r.snd⟩) else pure (ForInStep.yield ⟨i, true⟩)
              else pure (ForInStep.yield ⟨i, r.snd⟩)
        else do
          let oLeftIdx ← findIdx other.origin arr
          let oRightIdx ← findIdx other.rightOrigin arr
          if oLeftIdx < max leftIdx 0 then pure (ForInStep.done ⟨r.fst, r.snd⟩)
            else
              if oLeftIdx = max leftIdx 0 then
                if other.id < newItem.id then pure (ForInStep.yield ⟨r.fst, false⟩)
                else
                  if oRightIdx = max rightIdx 0 then pure (ForInStep.done ⟨r.fst, r.snd⟩)
                  else pure (ForInStep.yield ⟨r.fst, true⟩)
              else pure (ForInStep.yield (⟨r.fst, r.snd⟩ : MProd ℕ Bool))) = l at hintegrate

  obtain ⟨ _ ⟩ | ⟨ res ⟩ := l; cases hintegrate
  apply for_in_list_loop_invariant (I := fun x state => loop_invariant P arr newItem rightIdx.toNat x state) at hloop

  simp at hintegrate
  rw [<-hintegrate]
  -- Here, we prove that the array is still pairwise ordered after the integration.
  -- So, what we need is arr[res.first] < newItem < arr[res.first + 1] (and also, 0 <= res.first <= arr.size)

theorem integrate_commutative (A: Type) [BEq A] (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
