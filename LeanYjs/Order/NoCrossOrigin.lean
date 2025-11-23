import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Asymmetry

import Mathlib.Order.Defs.Unbundled

variable {A : Type}
variable {P : ItemSet A}
variable [DecidableEq A]

theorem no_cross_origin {x y : YjsItem A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  P x -> P y ->
  YjsLt' (A := A) x y ->
  YjsLeq' y.origin x.origin ∨ YjsLeq' x y.origin := by
  intros hP hinv hpx hpy hltxy
  generalize hsize : x.size + y.size = hsize
  revert x y
  apply Nat.strongRec' (p := fun hsize => ∀ (x y : YjsItem A),
    P x -> P y ->
    YjsLt' (YjsPtr.itemPtr x) (YjsPtr.itemPtr y) →
      x.size + y.size = hsize → YjsLeq' y.origin x.origin ∨ YjsLeq' (YjsPtr.itemPtr x) y.origin)
  intros n ih x y hpx hpy hlt hsize
  have hpy_origin : P y.origin := by
    obtain ⟨ yo, yr, yid, yc ⟩ := y
    apply hP.closedLeft; assumption
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
    have hpxo : P xo := by
      apply hP.closedLeft at hpx; assumption
    have hpxr : P xr := by
      apply hP.closedRight at hpx; assumption
    cases xr with
    | first =>
      have ⟨ _, horlt ⟩ := hinv.origin_not_leq _ _ _ _ hpx
      apply not_ptr_lt_first hP hinv at horlt
      cases horlt
      apply hP.closedLeft at hpx; assumption
    | last =>
      simp [YjsItem.rightOrigin] at hleq'
      have ⟨ _, hleq' ⟩ := hleq'
      cases hleq' with
      | leqLt h _ _ hlt' =>
        apply not_last_lt_ptr hP hinv at hlt'
        cases hlt'
        assumption
    | itemPtr xr =>
      have hpxr_origin : P xr.origin := by
        obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
        apply hP.closedLeft; assumption
      simp [YjsItem.rightOrigin] at hleq'
      apply yjs_leq'_imp_eq_or_yjs_lt' at hleq'
      cases hleq' with
      | inl hleq =>
        cases hleq
        have hreachable : OriginReachable (YjsPtr.itemPtr (YjsItem.item xo (YjsPtr.itemPtr y) xid xc)) y.origin := by
          apply OriginReachable.reachable_head (y := YjsPtr.itemPtr y)
          . apply OriginReachableStep.reachable_right
          . obtain ⟨ yo, yr, yid, yc ⟩ := y
            apply OriginReachable.reachable_single
            apply OriginReachableStep.reachable
        cases hinv.origin_nearest_reachable (x := y.origin) _ _ _ _ hpx hreachable with
        | inl hleq =>
          left
          assumption
        | inr hleq =>
          apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
          cases hleq with
          | inr hlt =>
            have hltorigin : YjsLt' y.origin y := by
              obtain ⟨ yo, yr, yid, yc ⟩ := y
              constructor; apply YjsLt.ltOrigin <;> try assumption
              apply YjsLeq.leqSame
            by_contra
            apply yjs_lt_asymm hP hinv y.origin y hpy_origin hpy hltorigin hlt
          | inl heq =>
            obtain ⟨ yo, yr, yid, yc ⟩ := y
            simp [YjsItem.origin] at heq
            cases heq
      | inr hlt =>
        have hsize' : xr.size + y.size < n := by
          simp [YjsPtr.size, YjsItem.size] at hsize
          omega
        have hpxr : P xr := by
          apply hP.closedRight at hpx; assumption
        cases ih (xr.size + y.size) hsize' xr y hpxr hpy hlt (by simp) with
        | inl hleq =>
          obtain ⟨ h, hleq ⟩ := hleq
          left
          have hreachable : OriginReachable (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)) xr.origin := by
            apply OriginReachable.reachable_head
            apply OriginReachableStep.reachable_right
            . apply OriginReachable.reachable_single
              obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
              apply OriginReachableStep.reachable
          have ⟨ _, hlt ⟩ : YjsLeq' xr.origin xo := by
            cases hinv.origin_nearest_reachable _ _ _ _ _ hpx hreachable with
            | inl hleq => assumption
            | inr hleq =>
              have hlt : YjsLt' xr.origin xr := by
                obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
                constructor; apply YjsLt.ltOrigin <;> try assumption
                . apply YjsLeq.leqSame
              apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
              cases hleq with
              | inl heq =>
                by_contra
                obtain ⟨ xro, xrr, xrid, xrc ⟩ := xr
                simp [YjsItem.origin] at *
                cases heq
              | inr hlt' =>
                cases yjs_lt_asymm hP hinv _ _ hpxr_origin hpxr hlt hlt'
          apply yjs_leq_p_trans hinv _ _ _ _ _ _ _ _ hP hleq <;> try assumption

        | inr hlt =>
          obtain ⟨ _, hlt ⟩ := hlt
          right
          have ⟨ h', hlt' ⟩ : YjsLt' (YjsPtr.itemPtr (YjsItem.item xo (YjsPtr.itemPtr xr) xid xc)) xr := by
            constructor; apply YjsLt.ltRightOrigin <;> try assumption
            . apply YjsLeq.leqSame
          apply yjs_leq_p_trans (h1 := h' + 1) (inv := hinv) (y := xr) <;> try assumption
          apply YjsLeq.leqLt; assumption
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
