import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.AntiSymmetry

import Mathlib.Order.Defs.Unbundled

variable {A : Type}
variable (P : ItemSet A)

theorem no_cross_origin (x y : YjsItem A) :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  YjsLt' P x y ->
  YjsLeq' P y.origin x.origin ∨ YjsLeq' P x y.origin := by
  intros hP hinv hxy
  generalize hsize : x.size + y.size = hsize
  revert x y
  apply Nat.strongRec' (p := fun hsize => ∀ (x y : YjsItem A),
    YjsLt' P (YjsPtr.itemPtr x) (YjsPtr.itemPtr y) →
      x.size + y.size = hsize → YjsLeq' P y.origin x.origin ∨ YjsLeq' P (YjsPtr.itemPtr x) y.origin)
  intros n ih x y hlt hsize
  have hpx : P x := by
    apply yjs_lt'_p1; assumption
  have hpy : P y := by
    apply yjs_lt'_p2; assumption
  apply yjs_lt'_cases at hlt
  rcases hlt with
  ⟨ heqfirst, _ ⟩
  | ⟨ heqlast, _ ⟩
  | ⟨ x', hx, hleq' ⟩
  | ⟨ y', hy, hleq' ⟩
  | hconflict
  . cases heqfirst
  . cases heqlast
  . cases hx
    -- apply yjs_leq'_imp_eq_or_yjs_lt' at hleq'
    obtain ⟨ xo, xr, xid, xc ⟩ := x
    cases xr with
    | first =>
      have ⟨ _, horlt ⟩ := hinv.origin_not_leq _ _ _ _ hpx
      apply not_ptr_lt_first hinv at horlt
      cases horlt
    | last =>
      simp [YjsItem.rightOrigin] at hleq'
      have ⟨ _, hleq' ⟩ := hleq'
      cases hleq' with
      | inl hleq =>
        cases hleq
      | inr hlt' =>
        apply (not_last_lt_ptr hinv) at hlt'
        cases hlt'
    | itemPtr xr =>
      simp [YjsItem.rightOrigin] at hleq'
      apply yjs_leq'_imp_eq_or_yjs_lt' at hleq'
      cases hleq' with
      | inl hleq =>
        cases hleq
        have hreachable : OriginReachable A (YjsPtr.itemPtr (YjsItem.item xo (YjsPtr.itemPtr y) xid xc)) y.origin := by
          apply @Relation.TransGen.tail (b := YjsPtr.itemPtr y)
          . apply @Relation.TransGen.single
            apply OriginReachableStep.reachable_right
          . obtain ⟨ yo, yr, yid, yc ⟩ := y
            apply OriginReachableStep.reachable
        cases hinv.origin_nearest_reachable (x := y.origin) _ _ _ _ hpx hreachable with
        | inl hleq =>
          left
          assumption
        | inr hleq =>
          apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
          cases hleq with
          | inr hlt =>
            have hltorigin : YjsLt' P y.origin y := by
              obtain ⟨ yo, yr, yid, yc ⟩ := y
              constructor; apply YjsLt.ltOriginOrder <;> try assumption
              . apply hP.closedLeft; assumption
              . apply OriginLt.lt_left
            cases yjs_lt_anti_symm hP hinv y.origin y hltorigin hlt
          | inl heq =>
            obtain ⟨ yo, yr, yid, yc ⟩ := y
            simp [YjsItem.origin] at heq
            cases heq
      | inr hlt =>
        have hsize' : xr.size + y.size < n := by
          simp [YjsPtr.size, YjsItem.size] at hsize
          omega
        cases ih (xr.size + y.size) hsize' xr y hlt (by simp) with
        | inl hleq =>
          obtain ⟨ h, hleq ⟩ := hleq
          left
          have hreachable : OriginReachable A (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)) xr.origin := by
            apply Relation.TransGen.tail
            apply Relation.TransGen.single
            apply OriginReachableStep.reachable_right
            obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
            apply OriginReachableStep.reachable
          have ⟨ _, hlt ⟩ : YjsLeq' P xr.origin xo := by
            cases hinv.origin_nearest_reachable _ _ _ _ _ hpx hreachable with
            | inl hleq => assumption
            | inr hleq =>
              have hlt : YjsLt' P xr.origin xr := by
                obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
                constructor; apply YjsLt.ltOriginOrder <;> try assumption
                . apply hP.closedLeft
                  apply hP.closedRight
                  assumption
                . apply hP.closedRight
                  assumption
                apply OriginLt.lt_left
              apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
              cases hleq with
              | inl heq =>
                rw [heq] at hlt
                cases yjs_lt_anti_symm hP hinv _ _ hlt hlt
              | inr hlt' =>
                cases yjs_lt_anti_symm hP hinv _ _ hlt hlt'
          apply yjs_leq_p_trans hinv _ _ _ _ _ hP hleq
          assumption
        | inr hlt =>
          obtain ⟨ _, hlt ⟩ := hlt
          right
          have ⟨ _, hlt' ⟩ : YjsLt' P (YjsPtr.itemPtr (YjsItem.item xo (YjsPtr.itemPtr xr) xid xc)) xr := by
            constructor; apply YjsLt.ltOriginOrder <;> try assumption
            . apply hP.closedRight; assumption
            . apply OriginLt.lt_right
          apply yjs_leq_p_trans (inv := hinv) (y := xr) <;> try assumption
          right
          assumption
  . cases hy
    right; assumption
  . obtain ⟨ _, hconflict ⟩ := hconflict
    cases hconflict with
    | ltOriginDiff =>
      left
      constructor
      right
      assumption
    | ltOriginSame =>
      left
      exists 0
      left
      eq_refl
