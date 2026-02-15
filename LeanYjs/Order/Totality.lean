import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.Order.ItemSetInvariant

@[simp] theorem first_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> P YjsPtr.first := by
  intros hclosed
  unfold ItemSet at *
  apply hclosed.baseFirst

@[simp] theorem last_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> P YjsPtr.last := by
  intros hclosed
  unfold ItemSet at *
  apply hclosed.baseLast

-- theorem yjs_origin_leq_lt {A : Type} {P : ItemSet A} :
--   IsClosedItemSet P ->
--   ∀ (x : YjsPtr A) (y : YjsItem A) h, P x → P y →
--     YjsLeq P h x y.origin -> ∃ h, YjsLt P h x y := by
--   intros hclosed x y h hx hy hleq
--   have hpyo : P y.origin := by
--     apply origin_p_valid <;> assumption
--   cases hleq with
--   | inl heq =>
--     rw [heq]
--     constructor
--     apply YjsLt.ltOriginOrder <;> try assumption
--     obtain ⟨ o, r, id, c ⟩ := y
--     apply OriginLt.lt_left
--   | inr hlt =>
--     obtain ⟨ o, r, id, c ⟩ := y
--     constructor
--     apply YjsLt.ltOrigin <;> try assumption

-- theorem yjs_right_origin_leq_lt {A : Type} {P : ItemSet A} :
--   IsClosedItemSet P ->
--   ∀ (x : YjsItem A) (y : YjsPtr A) h, P x → P y →
--     YjsLeq P h x.rightOrigin y -> ∃ h, YjsLt P h x y := by
--   intros hclosed x y h hx hy hleq
--   have hpxo : P x.rightOrigin := by
--     apply right_origin_p_valid <;> assumption
--   cases hleq with
--   | inl heq =>
--     rw [<-heq]
--     constructor
--     apply YjsLt.ltOriginOrder <;> try assumption
--     obtain ⟨ o, r, id, c ⟩ := x
--     apply OriginLt.lt_right
--   | inr hlt =>
--     obtain ⟨ o, r, id, c ⟩ := x
--     constructor
--     apply YjsLt.ltRightOrigin <;> try assumption

theorem YjsId_lt_total {x y : YjsId} :
  x < y ∨ y < x ∨ x = y := by
  obtain ⟨ xClientId, xClock ⟩ := x
  obtain ⟨ yClientId, yClock ⟩ := y
  simp only [LT.lt]
  unfold ClientId at *
  split
  . rw [beq_iff_eq] at *; subst xClientId
    rw [beq_self_eq_true]; simp
    omega
  . rw [Bool.beq_comm]
    split
    . contradiction
    . simp
      have h : (xClientId == yClientId) = false := by
        generalize h : (xClientId == yClientId) = eqb at *
        cases eqb <;> simp
        contradiction
      rw [beq_eq_false_iff_ne] at h
      omega


theorem yjs_lt_total {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y : YjsPtr A), P x -> P y ->
    (∃ h, @YjsLeq A h x y) ∨ (∃ h, @YjsLt A h y x) := by
  intros hclosed x y hx hy
  generalize heqxy : x.size + y.size = size
  revert x y
  apply Nat.strongRecOn' (P := fun s => ∀ (x y : YjsPtr A), P x → P y → x.size + y.size = s → (∃ h, YjsLeq h x y) ∨ ∃ h, YjsLt h y x) size
  intros n ih x y hx hy hpeq
  cases x with
  | first =>
    cases y with
    | first =>
      left
      exists 0
      left
    | last =>
      left
      exists 1
      apply YjsLeq.leqLt
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_first_last
    | itemPtr item =>
      left
      exists 1
      apply YjsLeq.leqLt
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_first
  | last =>
    cases y with
    | first =>
      right
      exists 0
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_first_last
    | last =>
      left
      exists 0
      apply YjsLeq.leqSame
    | itemPtr item =>
      right
      exists 0
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_last
  | itemPtr x =>
    cases y with
    | first =>
      right
      exists 0
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_first
    | last =>
      left
      exists 1
      right
      apply YjsLt.ltOriginOrder; try assumption
      apply OriginLt.lt_last
    | itemPtr y =>
      generalize heqx : x = x'
      obtain ⟨ xo, xr, xid, xc ⟩ := x
      generalize heqy : y = y'
      obtain ⟨ yo, yr, yid, yc ⟩ := y
      unfold ItemSet at *
      have hxo : P xo := by
        apply origin_p_valid hclosed (YjsItem.mk xo xr xid xc) hx
      have hyo : P yo := by
        apply origin_p_valid hclosed (YjsItem.mk yo yr yid yc) hy
      have hxr : P xr := by
        apply right_origin_p_valid hclosed (YjsItem.mk xo xr xid xc) hx
      have hyr : P yr := by
        apply right_origin_p_valid hclosed (YjsItem.mk yo yr yid yc) hy
      have hdec : (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)).size + yo.size < n := by
        rw [<-hpeq]
        simp [YjsPtr.size, YjsItem.size]
        omega
      have hleq : (∃ h', YjsLeq h' (YjsItem.mk xo xr xid xc) yo) ∨ (∃ h', YjsLt h' yo (YjsItem.mk xo xr xid xc)) := by
        apply ih ((YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)).size + yo.size) <;> try assumption
        simp
      cases hleq with
      | inl hleq =>
        obtain ⟨ h, hleq ⟩ := hleq
        left
        suffices (∃ h, YjsLt h (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)) (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc))) from by
          obtain ⟨ h, hlt ⟩ := this
          exists h + 1
          right
          rw [<-heqx, <-heqy]
          assumption
        constructor
        apply YjsLt.ltOrigin <;> assumption
      | inr hltyox =>
        have hdec : yr.size + (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)).size < n := by
          rw [<-hpeq]
          simp [YjsPtr.size, YjsItem.size]
          omega
        have hleq : (∃ h, YjsLeq h yr (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc))) ∨ ∃ h, YjsLt h (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)) yr := by
          apply ih (yr.size + (YjsPtr.itemPtr (YjsItem.mk xo xr xid xc)).size) <;> try assumption
          simp
        cases hleq with
        | inl hleq =>
          obtain ⟨ h, hleq ⟩ := hleq
          right
          rw [<-heqx, <-heqy]
          constructor
          apply YjsLt.ltRightOrigin <;> assumption
        | inr hltxyr =>
          have hleq : (∃ h, YjsLeq h (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc)) xo) ∨
            ∃ h, YjsLt h xo (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc)) := by
            apply ih ((YjsPtr.itemPtr (YjsItem.mk yo yr yid yc)).size + xo.size) _ _ _ hy hxo _ <;> try assumption
            . simp [YjsPtr.size, YjsItem.size] at *
              omega
            . simp
          cases hleq with
          | inl hleq =>
            obtain ⟨ h, hleq ⟩ := hleq
            right
            rw [<-heqx, <-heqy]
            constructor
            apply YjsLt.ltOrigin <;> assumption
          | inr hltxoy =>
            have hleq : (∃ h, YjsLeq h xr (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc))) ∨
              ∃ h, YjsLt h (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc)) xr := by
              apply ih (xr.size + (YjsPtr.itemPtr (YjsItem.mk yo yr yid yc)).size) <;> try assumption
              . simp [YjsPtr.size, YjsItem.size] at *
                omega
              . simp
            cases hleq with
            | inl hleq =>
              obtain ⟨ h, hleq ⟩ := hleq
              left
              rw [<-heqx, <-heqy]
              obtain hlt := YjsLt.ltRightOrigin h xo xr xid xc (YjsItem.mk yo yr yid yc) hleq
              constructor
              right
              apply hlt
            | inr hltyxr =>
              obtain ⟨ h1, hlt_yo_x ⟩ := hltyox
              obtain ⟨ h2, hlt_x_yo ⟩ := hltxoy
              obtain ⟨ h3, hlt_x_yr ⟩ := hltxyr
              obtain ⟨ h4, hlt_y_xr ⟩ := hltyxr
              have hleq : (∃ h, YjsLeq h xo yo) ∨ ∃ h, YjsLt h yo xo := by
                apply ih (xo.size + yo.size) _ _ _ hxo hyo _
                . simp [YjsPtr.size, YjsItem.size] at *
                  omega
                . simp
              cases hleq with
              | inr hlt =>
                obtain ⟨ h5, hlt_yo_xr ⟩ := hlt
                left
                exists (max4 h5 h3 h2 h4 + 1 + 1 + 1)
                right
                apply YjsLt.ltConflict
                rw [<-heqx, <-heqy]
                apply ConflictLt.ltOriginDiff <;> try first | assumption
              | inl hleq =>
                obtain ⟨ h5, hlt_yo_xr ⟩ := hleq
                cases hlt_yo_xr with
                | leqLt h5 _ _ hlt =>
                  right
                  constructor
                  apply YjsLt.ltConflict
                  rw [<-heqx, <-heqy]
                  apply ConflictLt.ltOriginDiff <;> try first | simp | assumption
                | leqSame _ =>
                  -- rw [heq] at hlt_yo_x hlt_x_yo hlt_x_yr
                  have hid : xid < yid ∨ yid < xid ∨ xid = yid := by
                    apply YjsId_lt_total
                  cases hid with
                  | inl hlt =>
                    left
                    constructor
                    right
                    apply YjsLt.ltConflict
                    rw [<-heqx, <-heqy]
                    apply ConflictLt.ltOriginSame <;> try assumption
                  | inr hleq =>
                    cases hleq with
                    | inl hlt =>
                      right
                      exists max h4 h3 + 1 + 1
                      apply YjsLt.ltConflict
                      rw [<-heqx, <-heqy]
                      apply ConflictLt.ltOriginSame <;> try assumption
                    | inr heq =>
                      rw [<-heqx, <-heqy, heq]
                      have heqneq : (YjsItem.mk xo xr yid xc) = (YjsItem.mk xo yr yid yc) ∨ (YjsItem.mk xo xr yid xc) ≠ (YjsItem.mk xo yr yid yc) := by
                        cases (inferInstance : Decidable (YjsItem.mk xo xr yid xc = YjsItem.mk xo yr yid yc)) with
                        | isTrue _ => left; assumption
                        | isFalse _ => right; assumption
                      cases heqneq with
                      | inl heq =>
                        left
                        exists 0
                        cases heq
                        rw [<-heq]
                        left
                      | inr hneq =>
                        rw [<-heq]
                        rw [<-heq] at hy
                        rw [<-heq] at *
                        have h_id_eq : (YjsItem.mk xo xr xid xc).id = (YjsItem.mk xo yr xid yc).id := by
                          simp [YjsItem.id]
                        have h_x_eq_y := inv.id_unique _ _ h_id_eq hx hy
                        contradiction

theorem YjsLeq'_or_YjsLt' {A : Type} [DecidableEq A] {P : ItemSet A} {x y : YjsPtr A} :
  ItemSetInvariant P -> IsClosedItemSet P -> P x -> P y -> (YjsLeq' x y) ∨ (YjsLt' y x) := by
  intros inv hP hx hy
  cases yjs_lt_total (inv := inv) hP x y hx hy with
  | inl hleq =>
    left
    obtain ⟨ h, hleq ⟩ := hleq
    constructor; assumption
  | inr hlt =>
    right
    obtain ⟨ h, hlt ⟩ := hlt
    constructor; assumption
