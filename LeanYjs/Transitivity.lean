import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant

variable {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P}

lemma yjs_lt_item (x : YjsItem A) (y : YjsPtr A) :
  YjsLt P h x y -> (∃ y', y = YjsPtr.itemPtr y') ∨ y = YjsPtr.last := by
  intros hlt
  revert x y
  apply Nat.strongRecOn' (P := fun h => ∀ (x : YjsItem A) (y : YjsPtr A), YjsLt P h (YjsPtr.itemPtr x) y → (∃ y', y = YjsPtr.itemPtr y') ∨ y = YjsPtr.last) h
  intros n ih x y hlt
  cases hlt with
  | ltConflict h x y hlt =>
    cases hlt with
    | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
      left; constructor; eq_refl
    | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
      left; constructor; eq_refl
  | ltOriginOrder x y hpx hpy hlt =>
    cases hlt with
    | lt_left o r id c =>
      left; constructor; eq_refl
    | lt_right o r id c




lemma yjs_lt_transitivity {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P} :
  ∀ (x y z : YjsPtr A), P.val x -> P.val y -> P.val z ->
  YjsLt' P x y -> YjsLt' P y z -> YjsLt' P x z := by
  intros x y z hx hy hz hxy hyz
  unfold YjsLt' at *
  obtain ⟨ P, hP ⟩ := P
  obtain ⟨ h0, hxy ⟩ := hxy
  obtain ⟨ h1, hyz ⟩ := hyz
  generalize hsize : x.size + y.size + z.size = total_size
  revert x y z
  simp
  apply @Nat.strongRecOn' (P := fun ts => ∀ x y z,
    P x → P y → P z →
    YjsLt ⟨ P, hP ⟩ h0 x y → YjsLt ⟨ P, hP ⟩ h1 y z → x.size + y.size + z.size = ts → ∃ h, YjsLt ⟨P, hP⟩ h x z) total_size
  intros total_size ih x y z hx hy hz hxy hyz hsize
  cases hxy with
  | ltOriginOrder _ _ hpx hpy hxy =>
    simp at *
    cases hxy with
    | lt_left o r id c =>
      simp [YjsPtr.size, YjsItem.size] at hsize
