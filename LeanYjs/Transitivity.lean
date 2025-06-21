import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant

variable {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P}

-- lemma yjs_lt_item (x : YjsItem A) (y : YjsPtr A) :
--   YjsLt P h x y -> (∃ y', y = YjsPtr.itemPtr y') ∨ y = YjsPtr.last := by
--   intros hlt
--   revert x y
--   apply Nat.strongRecOn' (P := fun h => ∀ (x : YjsItem A) (y : YjsPtr A), YjsLt P h (YjsPtr.itemPtr x) y → (∃ y', y = YjsPtr.itemPtr y') ∨ y = YjsPtr.last) h
--   intros n ih x y hlt
--   cases hlt with
--   | ltConflict h x y hlt =>
--     cases hlt with
--     | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
--       left; constructor; eq_refl
--     | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
--       left; constructor; eq_refl
--   | ltOriginOrder x y hpx hpy hlt =>
--     cases hlt with
--     | lt_left o r id c =>
--       left; constructor; eq_refl
--     | lt_right o r id c

lemma yjs_lt_transitivity {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P} :
  ∀ (x y z : YjsPtr A), P.val x -> P.val y -> P.val z ->
  YjsLt' P x y -> YjsLt' P y z -> YjsLt' P x z := by
  intros x y z hx hy hz hxy hyz
  unfold YjsLt' at *
  obtain ⟨ P, hP ⟩ := P
  obtain ⟨ h0, hxy ⟩ := hxy
  obtain ⟨ h1, hyz ⟩ := hyz
  generalize hsize : x.size + y.size + z.size = total_size
  revert x y z h0 h1
  simp
  apply @Nat.strongRecOn' (P := fun ts => ∀ x y z,
    P x → P y → P z →
    ∀ h0, YjsLt ⟨ P, hP ⟩ h0 x y → ∀ h1, YjsLt ⟨ P, hP ⟩ h1 y z → x.size + y.size + z.size = ts → ∃ h, YjsLt ⟨P, hP⟩ h x z) total_size
  intros total_size ih x y z hx hy hz h0 hxy h1 hyz hsize
  -- first, we prove the corner cases x = first or y = first/last, or z = last
  rcases yjs_lt_cases _ _ _ _ _ hxy with
  ⟨ hxeq, hylast | ⟨ y', hy' ⟩ ⟩
  | ⟨ hyeq, _ ⟩
  | hxycases
  -- | ⟨ x', hx'eq, hx'y ⟩
  -- | ⟨ y', hy'eq, hyy' ⟩
  -- | hconflict
  . -- x = first and y = last
    subst hylast
    apply not_last_lt_ptr inv at hyz
    cases hyz
  . -- x = first and y = itemPtr y'
    subst hxeq hy'
    cases z with
    | first =>
      apply not_ptr_lt_first inv at hyz
      cases hyz
    | last =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply hP.baseFirst
      apply hP.baseLast
      apply OriginLt.lt_first_last
    | itemPtr y' =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply hP.baseFirst
      assumption
      apply OriginLt.lt_first
  . -- y = last
    subst hyeq; apply not_last_lt_ptr inv at hyz
    cases hyz
  rcases yjs_lt_cases _ _ _ _ _ hyz with
  ⟨ hyeq, _ ⟩
  | ⟨ hzeq, hyfirst | ⟨ y', hy' ⟩ ⟩
  | hyzcases
  . -- y = first
    subst hyeq
    apply not_ptr_lt_first inv at hxy
    cases hxy
  . -- y = first and z = last
    subst hyfirst
    apply not_ptr_lt_first inv at hxy
    cases hxy
  . -- y = itemPtr y' and z = last
    subst hzeq hy'
    cases x with
    | first =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply hP.baseFirst
      apply hP.baseLast
      apply OriginLt.lt_first_last
    | last =>
      apply not_last_lt_ptr inv at hxy
      cases hxy
    | itemPtr x' =>
      exists 0
      apply YjsLt.ltOriginOrder
      assumption
      apply hP.baseLast
      apply OriginLt.lt_last
  -- then, we prove the main parts
  rcases hxycases with
  ⟨ x', hxeq, hleq ⟩
  | ⟨ y', hyeq, hxy, hleq  ⟩
  | hxyconflict
  . subst hxeq
    obtain ⟨ o, r, id, c ⟩ := x'
    simp [YjsItem.rightOrigin] at hleq
    obtain ⟨ h', hleq ⟩ := hleq
    cases hleq with
    | inl heq =>
      subst heq
      constructor
      apply YjsLt.ltRightOrigin <;> assumption
    | inr hlt =>
      have hsize : r.size + y.size + z.size < total_size := by
        simp [YjsItem.size, YjsPtr.size] at hsize
        omega
      have hpr : P r := by
        apply hP.closedRight; assumption
      obtain ⟨ h, hlt ⟩ := ih (r.size + y.size + z.size) hsize r y z hpr hy hz _ hlt _ hyz (refl _)
      constructor
      apply YjsLt.ltRightOrigin <;> assumption
  . subst hyeq
    rcases hyzcases with
    ⟨ y', hyeq, hyz, hleq' ⟩
    | ⟨ z', hzeq, hyz, hleq' ⟩
    | hyzconflict
    . obtain ⟨ o, r, id, c ⟩ := y'
      simp [YjsItem.origin] at hleq
      cases hyeq
      simp [YjsItem.rightOrigin] at hleq'
      have ⟨ hor, horlt ⟩ : YjsLt' ⟨ P, hP ⟩ o r := by
        apply inv.origin_not_leq <;> assumption
      cases hleq with
      | inl heq =>
        subst heq
        cases hleq' with
        | inl heq' =>
          subst heq'
          constructor; assumption
        | inr hlt' =>
          apply ih (x.size + r.size + z.size) _ x r z _ _ _ _ horlt _ hlt' <;> try assumption
          simp
          simp [YjsItem.size, YjsPtr.size] at hsize
          omega
          apply hP.closedRight; assumption
      | inr hlt =>
        cases hleq' with
        | inl heq' =>
          subst heq'
          apply ih (x.size + o.size + r.size) _ x o r _ _ _ _ hlt _ horlt <;> try assumption
          simp
          simp [YjsItem.size, YjsPtr.size] at hsize
          omega
          apply hP.closedLeft; assumption
        | inr hlt' =>
          have ⟨ h', hoz ⟩ : YjsLt' ⟨ P, hP ⟩ o z := by
            apply ih (o.size + r.size + z.size) _ o r z _ _ _ _ horlt _ hlt' <;> try assumption
            simp
            simp [YjsItem.size, YjsPtr.size] at hsize
            omega
            apply hP.closedLeft; assumption
            apply hP.closedRight; assumption
          apply ih (x.size + o.size + z.size) _ x o z _ _ _ _ hlt _ hoz <;> try assumption
          simp
          simp [YjsItem.size, YjsPtr.size] at hsize
          omega
          apply hP.closedLeft; assumption
    . subst hzeq
      obtain ⟨ o, r, id, c ⟩ := z'
      cases hleq' with
      | inl heq =>
        subst heq
        constructor
        apply YjsLt.ltOrigin <;> try assumption
      | inr hlt' =>
        have hsize : x.size + (YjsPtr.itemPtr y').size + o.size < total_size := by
          simp [YjsItem.size, YjsPtr.size] at *
          omega
        have hpo : P o := by
          apply hP.closedLeft; assumption
        obtain ⟨ h, hlt ⟩ := ih (x.size + (YjsPtr.itemPtr y').size + o.size) hsize x y' o hx hy hpo _ hxy _ hlt' (refl _)
        constructor
        apply YjsLt.ltOrigin <;> try assumption
    . obtain ⟨ _, hyzconflict ⟩ := hyzconflict
      have ⟨ _, hlt' ⟩ : YjsLt' ⟨ P, hP ⟩ y'.origin z := by
        cases hyzconflict with
        | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 =>
          simp [YjsItem.origin] at *
          constructor; assumption
        | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
          simp [YjsItem.origin] at *
          constructor
          apply YjsLt.ltOriginOrder <;> try assumption
          apply hP.closedLeft; assumption
          apply OriginLt.lt_left
      cases hleq with
      | inl heq =>
        subst heq
        constructor; assumption
      | inr hlt =>
        apply ih (x.size + y'.origin.size + z.size) _ x y'.origin z _ _ _ _ hlt _ hlt' (refl _) <;> try assumption
        . obtain ⟨ o, r, id, c ⟩ := y'
          simp [ YjsItem.origin, YjsItem.size, YjsPtr.size] at *
          omega
        . obtain ⟨ o, r, id, c ⟩ := y'
          apply hP.closedLeft; assumption
  .
