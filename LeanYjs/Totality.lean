import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet

@[simp] lemma first_p_valid {A} {P : ClosedPredicate A} : P.val YjsPtr.first := by
  unfold ClosedPredicate at *
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  assumption

@[simp] lemma last_p_valid {A} {P : ClosedPredicate A} : P.val YjsPtr.last := by
  unfold ClosedPredicate at *
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  assumption

lemma yjs_lt_total {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P} {x y : YjsPtr A} (hx : P.val x) (hy : P.val y) :
  (∃ h, @YjsLeq A P h x y) ∨ (∃ h, @YjsLt A P h y x) :=
  match x with
  | YjsPtr.first =>
    match y with
    | YjsPtr.first => by
      left
      exists 0
      left
      simp
    | YjsPtr.last => by
      left
      exists 0
      right
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try simp
      apply OriginLtStep.lt_first_last
    | YjsPtr.itemPtr item => by
      left
      exists 0
      right
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try first | simp | assumption
      apply OriginLtStep.lt_first
  | YjsPtr.last =>
    match y with
    | YjsPtr.first => by
      right
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try first | simp | assumption
      apply OriginLtStep.lt_first_last
    | YjsPtr.last => by
      left
      exists 0
      left
      simp
    | YjsPtr.itemPtr item => by
      right
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try first | simp | assumption
      apply OriginLtStep.lt_last
  | YjsPtr.itemPtr x =>
    match y with
    | YjsPtr.first => by
      right
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try first | simp | assumption
      apply OriginLtStep.lt_first
    | YjsPtr.last => by
      left
      exists 0
      right
      apply YjsLt.ltOriginOrder
      apply OriginLt.ltOrigin <;> try first | simp | assumption
      apply OriginLtStep.lt_last
    | YjsPtr.itemPtr y => by
      obtain ⟨ xo, xr, xid, xc ⟩ := x
      obtain ⟨ yo, yr, yid, yc ⟩ := y
      unfold ClosedPredicate at *
      have hxo : P.val xo := by
        apply origin_p_valid (YjsItem.item xo xr xid xc) hx
      have hyo : P.val yo := by
        apply origin_p_valid (YjsItem.item yo yr yid yc) hy
      have hxr : P.val xr := by
        apply right_origin_p_valid (YjsItem.item xo xr xid xc) hx
      have hyr : P.val yr := by
        apply right_origin_p_valid (YjsItem.item yo yr yid yc) hy
      obtain hleq := yjs_lt_total hx hyo (inv := inv)
      cases hleq with
      | inl hleq =>
        obtain ⟨ h, hleq ⟩ := hleq
        left
        suffices (∃ h, YjsLt _ h (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)) (YjsPtr.itemPtr (YjsItem.item yo yr yid yc))) from by
          obtain ⟨ h, hlt ⟩ := this
          exists h
          right
          assumption
        apply yjs_leq_p_trans1 inv _ _ _ _ 0 hleq _
        apply YjsLt.ltOriginOrder
        apply OriginLt.ltOrigin <;> try first | assumption | simp
        apply OriginLtStep.lt_left
      | inr hltyox =>
        obtain hleq := yjs_lt_total hyr hx (inv := inv)
        cases hleq with
        | inl hleq =>
          obtain ⟨ h, hleq ⟩ := hleq
          right
          apply yjs_leq_p_trans2 inv _ _ _ 0 _ _ hleq
          apply YjsLt.ltOriginOrder
          apply OriginLt.ltOrigin <;> try first | assumption | simp
          apply OriginLtStep.lt_right
        | inr hltxyr =>
          obtain hleq := yjs_lt_total hy hxo (inv := inv)
          cases hleq with
          | inl hleq =>
            obtain ⟨ h, hleq ⟩ := hleq
            right
            apply yjs_leq_p_trans1 inv _ _ _ _ 0 hleq _
            apply YjsLt.ltOriginOrder
            apply OriginLt.ltOrigin <;> try first | assumption | simp
            apply OriginLtStep.lt_left
          | inr hltxoy =>
            obtain hleq := yjs_lt_total hxr hy (inv := inv)
            cases hleq with
            | inl hleq =>
              obtain ⟨ h, hleq ⟩ := hleq
              left
              apply yjs_leq_p_trans inv _ _ _ 0 _ _ hleq
              right
              apply YjsLt.ltOriginOrder
              apply OriginLt.ltOrigin <;> try first | assumption | simp
              apply OriginLtStep.lt_right
            | inr hltyxr =>
              obtain ⟨ h1, hlt_yo_x ⟩ := hltyox
              obtain ⟨ h2, hlt_x_yo ⟩ := hltxoy
              obtain ⟨ h3, hlt_x_yr ⟩ := hltxyr
              obtain ⟨ h4, hlt_y_xr ⟩ := hltyxr
              obtain hleq := yjs_lt_total hxo hyo (inv := inv)
              cases hleq with
              | inr hlt =>
                obtain ⟨ h5, hlt_yo_xr ⟩ := hlt
                left
                exists (max4 h5 h3 h2 h4 + 1 + 1)
                right
                apply YjsLt.ltConflict
                apply ConflictLt.ltOriginDiff <;> try first | assumption | simp
              | inl hleq =>
                obtain ⟨ h5, hlt_yo_xr ⟩ := hleq
                cases hlt_yo_xr with
                | inr hlt =>
                  right
                  exists (max4 h5 h4 h1 h3 + 1 + 1)
                  apply YjsLt.ltConflict
                  apply ConflictLt.ltOriginDiff <;> try first | simp | assumption
                | inl heq =>
                  rw [heq] at hlt_yo_x hlt_x_yo hlt_x_yr
                  rw [heq]
                  have hid : xid < yid ∨ yid < xid ∨ xid = yid := by
                    unfold ActorId; omega
                  cases hid with
                  | inl hlt =>
                    left
                    exists max h3 h4 + 1 + 1
                    right
                    apply YjsLt.ltConflict
                    apply ConflictLt.ltOriginSame <;> try assumption
                  | inr hleq =>
                    cases hleq with
                    | inl hlt =>
                      right
                      exists max h4 h3 + 1 + 1
                      apply YjsLt.ltConflict
                      apply ConflictLt.ltOriginSame <;> try assumption
                    | inr heq =>
                      sorry
