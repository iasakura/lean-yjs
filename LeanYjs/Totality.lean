import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant

@[simp] lemma first_p_valid {A} {P : ClosedPredicate A} : P.val YjsPtr.first := by
  unfold ClosedPredicate at *
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  assumption

@[simp] lemma last_p_valid {A} {P : ClosedPredicate A} : P.val YjsPtr.last := by
  unfold ClosedPredicate at *
  obtain ⟨ p, ⟨ hp, hp', hp'', hp''' ⟩ ⟩ := P
  assumption

lemma yjs_lt_total {A : Type} {P : ClosedPredicate A} {inv : ItemSetInvariant P} :forall (x y : YjsPtr A) (hx : P.val x) (hy : P.val y),
  (∃ h, @YjsLeq A P h x y) ∨ (∃ h, @YjsLt A P h y x) :=
  fun (x : YjsPtr A) (y : YjsPtr A) (hx : P.val x) (hy : P.val y) =>
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
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_first_last
    | YjsPtr.itemPtr item => by
      left
      exists 0
      right
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_first
  | YjsPtr.last =>
    match y with
    | YjsPtr.first => by
      right
      exists 0
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_first_last
    | YjsPtr.last => by
      left
      exists 0
      left
      simp
    | YjsPtr.itemPtr item => by
      right
      exists 0
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_last
  | YjsPtr.itemPtr x =>
    match y with
    | YjsPtr.first => by
      right
      exists 0
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_first
    | YjsPtr.last => by
      left
      exists 0
      right
      apply YjsLt.ltOriginOrder <;> try assumption
      apply OriginLt.lt_last
    | YjsPtr.itemPtr y => by
      generalize heqx : x = x'
      obtain ⟨ xo, xr, xid, xc ⟩ := x
      generalize heqy : y = y'
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
      have hdec : (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)).size + yo.size < (YjsPtr.itemPtr x').size + (YjsPtr.itemPtr y').size := by
        rw [<-heqx, <-heqy]
        simp [YjsPtr.size, YjsItem.size]
        omega
      obtain hleq := yjs_lt_total _ _ hx hyo (inv := inv)
      cases hleq with
      | inl hleq =>
        obtain ⟨ h, hleq ⟩ := hleq
        left
        suffices (∃ h, YjsLt _ h (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)) (YjsPtr.itemPtr (YjsItem.item yo yr yid yc))) from by
          obtain ⟨ h, hlt ⟩ := this
          exists h
          right
          rw [<-heqx, <-heqy]
          assumption
        apply yjs_leq_p_trans1 inv _ _ _ _ 0 hleq _
        apply YjsLt.ltOriginOrder <;> try assumption
        apply OriginLt.lt_left
      | inr hltyox =>
        obtain hleq := yjs_lt_total _ _ hyr hx (inv := inv)
        cases hleq with
        | inl hleq =>
          obtain ⟨ h, hleq ⟩ := hleq
          right
          apply yjs_leq_p_trans2 inv _ _ _ 0 _ _ hleq
          apply YjsLt.ltOriginOrder <;> try assumption
          apply OriginLt.lt_right
        | inr hltxyr =>
          obtain hleq := yjs_lt_total _ _ hy hxo (inv := inv)
          cases hleq with
          | inl hleq =>
            obtain ⟨ h, hleq ⟩ := hleq
            right
            apply yjs_leq_p_trans1 inv _ _ _ _ 0 hleq _
            apply YjsLt.ltOriginOrder <;> try assumption
            apply OriginLt.lt_left
          | inr hltxoy =>
            obtain hleq := yjs_lt_total _ _ hxr hy (inv := inv)
            cases hleq with
            | inl hleq =>
              obtain ⟨ h, hleq ⟩ := hleq
              left
              apply yjs_leq_p_trans inv _ _ _ 0 _ _ hleq
              right
              apply YjsLt.ltOriginOrder <;> try assumption
              apply OriginLt.lt_right
            | inr hltyxr =>
              obtain ⟨ h1, hlt_yo_x ⟩ := hltyox
              obtain ⟨ h2, hlt_x_yo ⟩ := hltxoy
              obtain ⟨ h3, hlt_x_yr ⟩ := hltxyr
              obtain ⟨ h4, hlt_y_xr ⟩ := hltyxr
              obtain hleq := yjs_lt_total _ _ hxo hyo (inv := inv)
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
termination_by x y => x.size + y.size
