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

lemma for_in_list_loop_invariant (m : Type -> Type) [Monad m] (ls : List α) (init : β) (body : α -> β -> m (ForInStep β)) (I : m β -> Prop) :
  (∀ (x : α) (y : β), I (pure y) -> body x y) -> I (pure init) -> I (forIn ls init body) := by
  sorry

theorem integrate_sound (A: Type) [BEq A] (P : ClosedPredicate A) (inv : ItemSetInvariant P) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  ArrayPairwise (fun (x y : YjsItem A) => YjsLt' P x y) arr
  -> integrate newItem arr = Except.ok newArr
  -> ArrayPairwise (fun (x y : YjsItem A) => YjsLt' P x y) newArr := by
  intros hsorted hintegrate
  unfold integrate at hintegrate

  generalize findIdx newItem.origin arr = leftIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ leftIdx ⟩ := leftIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  generalize findIdx newItem.rightOrigin arr = rightIdx at hintegrate
  obtain ⟨ _ ⟩ | ⟨ rightIdx ⟩ := rightIdx; cases hintegrate
  rw [ok_bind] at hintegrate

  simp at hintegrate



theorem integrate_commutative (A: Type) [BEq A] (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
