import LeanYjs.Item
import LeanYjs.ItemSet
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
  IsClosedItemSet (ArrSet arr)

omit [BEq A] in lemma arr_set_closed_push (arr : Array (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr ->
  ArrSet arr item.origin ->
  ArrSet arr item.rightOrigin ->
  ArrSetClosed (Array.push arr item) := by
  intros hclosed horigin hright
  constructor <;> try simp [ArrSet, IsClosedItemSet]
  . intros o r id c hor
    cases o with
    | itemPtr item' =>
      simp
      cases hor with
      | inl hitem =>
        left
        apply hclosed.closedLeft at hitem
        assumption
      | inr heq =>
        subst heq
        left
        assumption
    | first =>
      simp
    | last =>
      simp
  . intros o r id c hor
    cases r with
    | itemPtr item' =>
      simp
      cases hor with
      | inl hitem =>
        left
        apply hclosed.closedRight at hitem
        assumption
      | inr heq =>
        subst heq
        left
        assumption
    | first =>
      simp
    | last =>
      simp

lemma yjs_lt_mono (P Q : ItemSet A) (x y : YjsItem A) :
  IsClosedItemSet P ->
  IsClosedItemSet Q ->
  ItemSetInvariant P ->
  ItemSetInvariant Q ->
  (∀ a, P a -> Q a) ->
  YjsLt' P x y ->
  YjsLt' Q x y := by
  intros hclosedP hclosedQ hinvP hinvQ hsubset hlt
  apply yjs_lt'_cases at hlt
  rcases hlt with
  cases hlt with
  | inl heq =>
    subst heq
    simp [YjsLt', ItemSetInvariant] at *
    assumption
  | inr hlt' =>
    apply yjs_lt'_p1 hlt'
    assumption

lemma item_set_invariant_push (arr : Array (YjsItem A)) (item : YjsItem A) :
  ItemSetInvariant (ArrSet arr) ->
  ArrSetClosed arr ->
  YjsLt' (ArrSet arr) item.origin item.rightOrigin ->
  ItemSetInvariant (ArrSet (Array.push arr item)) := by
  intros hinv hclosed horigin
  constructor
  . intros o r c id hitem
    simp [ArrSet] at hitem
    cases hitem with
    | inl hin =>
      apply hinv.origin_not_leq at hin
  . intros x y hxy
    apply yjs_lt'_imp_eq_or_yjs_lt' at hxy
    cases hxy with
    | inl heq =>
      subst heq
      simp [ArrSet]
    | inr hlt =>
      apply yjs_lt'_p1 hlt; assumption

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
  (∀ i, i < dest -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P other newItem) ∧
  (∀ i, dest ≤ i -> i < lastChecked -> ∃ other : YjsItem A, some other = arr[i]? ∧ YjsLt' P newItem other.rightOrigin ->  YjsLt' P other newItem) ∧
  (scanning -> ∃ (destItem : YjsItem A), arr[dest]? = some destItem ∧ destItem.origin = newItem.origin) ∧
  (isDone -> ∃ item : YjsItem A, arr[current]? = some item ∧ YjsLt' P item newItem)

theorem integrate_sound (A: Type) [BEq A] (P : ItemSet A) (inv : ItemSetInvariant P) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
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
