import LeanYjs.Order.BoundaryV2

variable {A : Type}

theorem YjsId_lt_trans_v2 {x y z : YjsId} :
    x < y -> y < z -> x < z := by
  intro hxy hyz
  obtain ⟨ xClientId, xClock ⟩ := x
  obtain ⟨ yClientId, yClock ⟩ := y
  obtain ⟨ zClientId, zClock ⟩ := z
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hxy
  · subst xClientId
    split at hyz
    · subst yClientId
      simp
      omega
    · split
      · omega
      · omega
  · split at hyz
    · subst zClientId
      split
      · omega
      · omega
    · split
      · omega
      · omega

theorem conflictLtV2_x_origin_lt_y {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S x.origin y.toRef := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ hItemY _ _ hlt3 _ =>
      exact ⟨ _, hlt3 ⟩
  | ltOriginSame _ _ _ hItemY hOrigin _ _ _ =>
      simpa [YjsItemV2.toRef, hOrigin] using
        (YjsLtV2'.ltOrigin hItemY (YjsLeqV2'.leqSame y.origin))

theorem conflictLtV2_y_origin_lt_x {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S y.origin x.toRef := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ hItemX _ hlt1 _ _ _ =>
      exact YjsLtV2'.ltOrigin hItemX (YjsLeqV2'.leqLt ⟨ _, hlt1 ⟩)
  | ltOriginSame _ _ hItemX _ hOrigin _ _ _ =>
      simpa [YjsItemV2.toRef, hOrigin] using
        (YjsLtV2'.ltOrigin hItemX (YjsLeqV2'.leqSame x.origin))

theorem conflictLtV2_y_lt_x_rightOrigin {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S y.toRef x.rightOrigin := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ _ _ _ _ hlt4 =>
      exact ⟨ _, hlt4 ⟩
  | ltOriginSame _ _ _ _ _ _ hlt2 _ =>
      exact ⟨ _, hlt2 ⟩

theorem conflictLtV2_x_lt_y_rightOrigin {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S x.toRef y.rightOrigin := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ _ _ hlt2 _ _ =>
      exact ⟨ _, hlt2 ⟩
  | ltOriginSame _ _ _ _ _ hlt1 _ _ =>
      exact ⟨ _, hlt1 ⟩
