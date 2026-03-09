import LeanYjs.ItemSetV2

variable {A : Type}

def max4V2 (x y z w : Nat) : Nat :=
  max (max x y) (max z w)

inductive OriginLtV2 (S : ItemSetV2 A) : ItemRef -> ItemRef -> Prop where
  | lt_first {id : YjsId} :
      S.IdIn id ->
      OriginLtV2 S .first (.idRef id)
  | lt_last {id : YjsId} :
      S.IdIn id ->
      OriginLtV2 S (.idRef id) .last
  | lt_first_last :
      OriginLtV2 S .first .last

inductive OriginReachableStepV2 (S : ItemSetV2 A) : ItemRef -> ItemRef -> Prop where
  | left {item : YjsItemV2 A} :
      S.ItemIn item ->
      OriginReachableStepV2 S item.toRef item.origin
  | right {item : YjsItemV2 A} :
      S.ItemIn item ->
      OriginReachableStepV2 S item.toRef item.rightOrigin

inductive OriginReachableV2 (S : ItemSetV2 A) : ItemRef -> ItemRef -> Prop where
  | single {x y : ItemRef} :
      OriginReachableStepV2 S x y ->
      OriginReachableV2 S x y
  | tail {x y z : ItemRef} :
      OriginReachableStepV2 S x y ->
      OriginReachableV2 S y z ->
      OriginReachableV2 S x z

inductive OriginReachableFromV2 (S : ItemSetV2 A) (item : YjsItemV2 A) : ItemRef -> Prop where
  | origin :
      OriginReachableFromV2 S item item.origin
  | rightOrigin :
      OriginReachableFromV2 S item item.rightOrigin
  | tail_origin {x : ItemRef} :
      OriginReachableV2 S item.origin x ->
      OriginReachableFromV2 S item x
  | tail_rightOrigin {x : ItemRef} :
      OriginReachableV2 S item.rightOrigin x ->
      OriginReachableFromV2 S item x

mutual
  inductive YjsLtV2 (S : ItemSetV2 A) : Nat -> ItemRef -> ItemRef -> Prop where
    | ltConflict h {item1 item2 : YjsItemV2 A} :
        ConflictLtV2 S h item1 item2 ->
        YjsLtV2 S (h + 1) item1.toRef item2.toRef
    | ltOriginOrder {x y : ItemRef} :
        OriginLtV2 S x y ->
        YjsLtV2 S 0 x y
    | ltOrigin h {x : ItemRef} {item : YjsItemV2 A} :
        S.ItemIn item ->
        YjsLeqV2 S h x item.origin ->
        YjsLtV2 S (h + 1) x item.toRef
    | ltRightOrigin h {item : YjsItemV2 A} {x : ItemRef} :
        S.ItemIn item ->
        YjsLeqV2 S h item.rightOrigin x ->
        YjsLtV2 S (h + 1) item.toRef x

  inductive YjsLeqV2 (S : ItemSetV2 A) : Nat -> ItemRef -> ItemRef -> Prop where
    | leqSame (x : ItemRef) : YjsLeqV2 S h x x
    | leqLt h {x y : ItemRef} :
        YjsLtV2 S h x y ->
        YjsLeqV2 S (h + 1) x y

  inductive ConflictLtV2 (S : ItemSetV2 A) : Nat -> YjsItemV2 A -> YjsItemV2 A -> Prop where
    | ltOriginDiff h1 h2 h3 h4 {item1 item2 : YjsItemV2 A} :
        S.ItemIn item1 ->
        S.ItemIn item2 ->
        YjsLtV2 S h1 item2.origin item1.origin ->
        YjsLtV2 S h2 item1.toRef item2.rightOrigin ->
        YjsLtV2 S h3 item1.origin item2.toRef ->
        YjsLtV2 S h4 item2.toRef item1.rightOrigin ->
        ConflictLtV2 S (max4V2 h1 h2 h3 h4 + 1) item1 item2
    | ltOriginSame h1 h2 {item1 item2 : YjsItemV2 A} :
        S.ItemIn item1 ->
        S.ItemIn item2 ->
        item1.origin = item2.origin ->
        YjsLtV2 S h1 item1.toRef item2.rightOrigin ->
        YjsLtV2 S h2 item2.toRef item1.rightOrigin ->
        item1.id < item2.id ->
        ConflictLtV2 S (max h1 h2 + 1) item1 item2
end

def ConflictLtV2' (S : ItemSetV2 A) (item1 item2 : YjsItemV2 A) : Prop :=
  ∃ h, ConflictLtV2 S h item1 item2

def YjsLtV2' (S : ItemSetV2 A) (x y : ItemRef) : Prop :=
  ∃ h, YjsLtV2 S h x y

def YjsLeqV2' (S : ItemSetV2 A) (x y : ItemRef) : Prop :=
  ∃ h, YjsLeqV2 S h x y

def yjsLeqV2_imp_eq_or_yjsLtV2 {S : ItemSetV2 A} {x y : ItemRef} :
    YjsLeqV2' S x y -> x = y ∨ YjsLtV2' S x y := by
  intro hLeq
  rcases hLeq with ⟨ h, hLeq ⟩
  cases hLeq with
  | leqSame _ =>
      exact Or.inl rfl
  | leqLt _ hLt =>
      exact Or.inr ⟨ _, hLt ⟩

theorem yjsLtV2_cases (S : ItemSetV2 A) (h : Nat) (x y : ItemRef) :
    YjsLtV2 S h x y ->
      (x = .first ∧ (y = .last ∨ ∃ id, y = .idRef id ∧ S.IdIn id)) ∨
      (y = .last ∧ (x = .first ∨ ∃ id, x = .idRef id ∧ S.IdIn id)) ∨
      (∃ item, x = item.toRef ∧ S.ItemIn item ∧ YjsLeqV2' S item.rightOrigin y) ∨
      (∃ item, y = item.toRef ∧ S.ItemIn item ∧ YjsLeqV2' S x item.origin) ∨
      (∃ item1 item2, x = item1.toRef ∧ y = item2.toRef ∧ ConflictLtV2' S item1 item2) := by
  intro hLt
  cases hLt with
  | ltConflict _ hConflict =>
      right
      right
      right
      right
      refine ⟨ _, _, rfl, rfl, ?_ ⟩
      exact ⟨ _, hConflict ⟩
  | ltOriginOrder hOrigin =>
      cases hOrigin with
      | lt_first hIdIn =>
          left
          exact ⟨ rfl, Or.inr ⟨ _, rfl, hIdIn ⟩ ⟩
      | lt_last hIdIn =>
          right
          left
          exact ⟨ rfl, Or.inr ⟨ _, rfl, hIdIn ⟩ ⟩
      | lt_first_last =>
          left
          exact ⟨ rfl, Or.inl rfl ⟩
  | ltOrigin _ hItem hLeq =>
      right
      right
      right
      left
      refine ⟨ _, rfl, hItem, ?_ ⟩
      exact ⟨ _, hLeq ⟩
  | ltRightOrigin _ hItem hLeq =>
      right
      right
      left
      refine ⟨ _, rfl, hItem, ?_ ⟩
      exact ⟨ _, hLeq ⟩

theorem yjsLtV2'_cases (S : ItemSetV2 A) (x y : ItemRef) :
    YjsLtV2' S x y ->
      (x = .first ∧ (y = .last ∨ ∃ id, y = .idRef id ∧ S.IdIn id)) ∨
      (y = .last ∧ (x = .first ∨ ∃ id, x = .idRef id ∧ S.IdIn id)) ∨
      (∃ item, x = item.toRef ∧ S.ItemIn item ∧ YjsLeqV2' S item.rightOrigin y) ∨
      (∃ item, y = item.toRef ∧ S.ItemIn item ∧ YjsLeqV2' S x item.origin) ∨
      (∃ item1 item2, x = item1.toRef ∧ y = item2.toRef ∧ ConflictLtV2' S item1 item2) := by
  intro hLt
  rcases hLt with ⟨ h, hLt ⟩
  exact yjsLtV2_cases S h x y hLt

private theorem itemIn_withItem_of_itemIn_of_fresh {S : ItemSetV2 A}
    {item newItem : YjsItemV2 A} :
    S.lookup newItem.id = none ->
    S.ItemIn item ->
    (S.withItem newItem).ItemIn item := by
  intro hFresh hItem
  by_cases hEq : item.id = newItem.id
  · have hLookup : S.lookup newItem.id = some item := by
      simpa [hEq] using hItem
    rw [hFresh] at hLookup
    cases hLookup
  · exact ItemSetV2.itemIn_withItem_of_itemIn hEq hItem

private theorem originLtV2_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A} :
    OriginLtV2 S x y -> OriginLtV2 (S.withItem newItem) x y := by
  intro hOrigin
  cases hOrigin with
  | lt_first hId =>
      rename_i id
      exact OriginLtV2.lt_first (by
        simpa using
          (ItemSetV2.refIn_withItem_of_refIn
            (S := S) (item := newItem) (ref := .idRef id) hId))
  | lt_last hId =>
      rename_i id
      exact OriginLtV2.lt_last (by
        simpa using
          (ItemSetV2.refIn_withItem_of_refIn
            (S := S) (item := newItem) (ref := .idRef id) hId))
  | lt_first_last =>
      exact OriginLtV2.lt_first_last

theorem yjsLtV2_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A}
    (hFresh : S.lookup newItem.id = none) :
    YjsLtV2 S h x y -> YjsLtV2 (S.withItem newItem) h x y := by
  intro hLt
  refine YjsLtV2.recOn
      (motive_1 := fun h x y _ => YjsLtV2 (S.withItem newItem) h x y)
      (motive_2 := fun h x y _ => YjsLeqV2 (S.withItem newItem) h x y)
      (motive_3 := fun h item1 item2 _ => ConflictLtV2 (S.withItem newItem) h item1 item2)
      hLt
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h item1 item2 hConflict ihConflict
    exact YjsLtV2.ltConflict (h := h) ihConflict
  · intro x y hOrigin
    exact YjsLtV2.ltOriginOrder (originLtV2_withItem (newItem := newItem) hOrigin)
  · intro h x item hItem hLeq ihLeq
    exact YjsLtV2.ltOrigin (h := h)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem)
      ihLeq
  · intro h item x hItem hLeq ihLeq
    exact YjsLtV2.ltRightOrigin (h := h)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem)
      ihLeq
  · intro h x
    exact YjsLeqV2.leqSame x
  · intro h x y hLt ihLt
    exact YjsLeqV2.leqLt (h := h) ihLt
  · intro h1 h2 h3 h4 item1 item2 hItem1 hItem2 hLt1 hLt2 hLt3 hLt4 ih1 ih2 ih3 ih4
    exact ConflictLtV2.ltOriginDiff (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem1)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem2)
      ih1
      ih2
      ih3
      ih4
  · intro h1 h2 item1 item2 hItem1 hItem2 hOrigin hLt1 hLt2 hId ih1 ih2
    exact ConflictLtV2.ltOriginSame (h1 := h1) (h2 := h2)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem1)
      (itemIn_withItem_of_itemIn_of_fresh hFresh hItem2)
      hOrigin
      ih1
      ih2
      hId

theorem yjsLeqV2_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A}
    (hFresh : S.lookup newItem.id = none) :
    YjsLeqV2 S h x y -> YjsLeqV2 (S.withItem newItem) h x y := by
  intro hLeq
  cases hLeq with
  | leqSame x =>
      exact YjsLeqV2.leqSame x
  | leqLt h hLt =>
      exact YjsLeqV2.leqLt (h := h) (yjsLtV2_withItem hFresh hLt)

theorem conflictLtV2_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A}
    (hFresh : S.lookup newItem.id = none) :
    ConflictLtV2 S h item1 item2 ->
    ConflictLtV2 (S.withItem newItem) h item1 item2 := by
  intro hConflict
  cases hConflict with
  | ltOriginDiff h1 h2 h3 h4 hItem1 hItem2 hLt1 hLt2 hLt3 hLt4 =>
      exact ConflictLtV2.ltOriginDiff (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4)
        (itemIn_withItem_of_itemIn_of_fresh hFresh hItem1)
        (itemIn_withItem_of_itemIn_of_fresh hFresh hItem2)
        (yjsLtV2_withItem hFresh hLt1)
        (yjsLtV2_withItem hFresh hLt2)
        (yjsLtV2_withItem hFresh hLt3)
        (yjsLtV2_withItem hFresh hLt4)
  | ltOriginSame h1 h2 hItem1 hItem2 hOrigin hLt1 hLt2 hId =>
      exact ConflictLtV2.ltOriginSame (h1 := h1) (h2 := h2)
        (itemIn_withItem_of_itemIn_of_fresh hFresh hItem1)
        (itemIn_withItem_of_itemIn_of_fresh hFresh hItem2)
        hOrigin
        (yjsLtV2_withItem hFresh hLt1)
        (yjsLtV2_withItem hFresh hLt2)
        hId

theorem yjsLtV2'_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A} :
    S.lookup newItem.id = none ->
    YjsLtV2' S x y ->
    YjsLtV2' (S.withItem newItem) x y := by
  intro hFresh hLt
  rcases hLt with ⟨ h, hLt ⟩
  exact ⟨ h, yjsLtV2_withItem hFresh hLt ⟩

theorem yjsLeqV2'_withItem {S : ItemSetV2 A} {newItem : YjsItemV2 A} :
    S.lookup newItem.id = none ->
    YjsLeqV2' S x y ->
    YjsLeqV2' (S.withItem newItem) x y := by
  intro hFresh hLeq
  rcases hLeq with ⟨ h, hLeq ⟩
  exact ⟨ h, yjsLeqV2_withItem hFresh hLeq ⟩

private theorem not_refIn_toRef_of_lookup_none {S : ItemSetV2 A} {newItem : YjsItemV2 A} :
    S.lookup newItem.id = none ->
    ¬ S.RefIn newItem.toRef := by
  intro hFresh hRef
  rcases hRef with ⟨ item, hLookup ⟩
  rw [hFresh] at hLookup
  cases hLookup

theorem originReachableStepV2_of_withItem_of_ne {S : ItemSetV2 A} {newItem : YjsItemV2 A}
    :
    OriginReachableStepV2 (S.withItem newItem) x y ->
    x ≠ newItem.toRef ->
    OriginReachableStepV2 S x y := by
  intro hStep hStartNe
  cases hStep with
  | left hItem =>
      rename_i item
      have hIdNe : item.id ≠ newItem.id := by
        intro hEq
        apply hStartNe
        simp [YjsItemV2.toRef, hEq]
      have hItemOld : S.ItemIn item := by
        rw [ItemSetV2.ItemIn] at hItem ⊢
        rw [ItemSetV2.lookup_withItem_of_ne (S := S) (item := newItem) (id := item.id) hIdNe] at hItem
        exact hItem
      exact OriginReachableStepV2.left <|
        hItemOld
  | right hItem =>
      rename_i item
      have hIdNe : item.id ≠ newItem.id := by
        intro hEq
        apply hStartNe
        simp [YjsItemV2.toRef, hEq]
      have hItemOld : S.ItemIn item := by
        rw [ItemSetV2.ItemIn] at hItem ⊢
        rw [ItemSetV2.lookup_withItem_of_ne (S := S) (item := newItem) (id := item.id) hIdNe] at hItem
        exact hItem
      exact OriginReachableStepV2.right <|
        hItemOld

private theorem originReachableStepV2_target_ne_withItem
    {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) {newItem : YjsItemV2 A}
    (hFresh : S.lookup newItem.id = none) :
    OriginReachableStepV2 (S.withItem newItem) x y ->
    x ≠ newItem.toRef ->
    y ≠ newItem.toRef := by
  intro hStep hStartNe hEq
  have hStepOld :=
    originReachableStepV2_of_withItem_of_ne (S := S) (newItem := newItem) hStep hStartNe
  have hRefIn : S.RefIn y := by
    cases hStepOld with
    | left hItem =>
        exact hClosed.closedLeft hItem
    | right hItem =>
        exact hClosed.closedRight hItem
  subst y
  exact not_refIn_toRef_of_lookup_none (S := S) (newItem := newItem) hFresh hRefIn

theorem originReachableV2_of_withItem_of_ne
    {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) {newItem : YjsItemV2 A}
    (hFresh : S.lookup newItem.id = none) :
    OriginReachableV2 (S.withItem newItem) x y ->
    x ≠ newItem.toRef ->
    OriginReachableV2 S x y := by
  intro hReach hStartNe
  induction hReach with
  | single hStep =>
      exact .single <|
        originReachableStepV2_of_withItem_of_ne (S := S) (newItem := newItem) hStep hStartNe
  | tail hStep hTail ih =>
      have hStepOld :=
        originReachableStepV2_of_withItem_of_ne (S := S) (newItem := newItem) hStep hStartNe
      have hMidNe :=
        originReachableStepV2_target_ne_withItem
          (S := S) hClosed (newItem := newItem) hFresh hStep hStartNe
      exact .tail hStepOld (ih hMidNe)

namespace OriginReachableV2

theorem of_origin {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item ->
    OriginReachableV2 S item.toRef item.origin := by
  intro hItem
  exact .single (.left hItem)

theorem of_rightOrigin {S : ItemSetV2 A} {item : YjsItemV2 A} :
    S.ItemIn item ->
    OriginReachableV2 S item.toRef item.rightOrigin := by
  intro hItem
  exact .single (.right hItem)

theorem target_refIn_of_step {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) :
    ∀ {x y : ItemRef}, OriginReachableStepV2 S x y -> S.RefIn y := by
  intro x y hStep
  cases hStep with
  | left hItem =>
      exact hClosed.closedLeft hItem
  | right hItem =>
      exact hClosed.closedRight hItem

theorem target_refIn {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S) :
    ∀ {x y : ItemRef}, OriginReachableV2 S x y -> S.RefIn y := by
  intro x y hReach
  induction hReach with
  | single hStep =>
      exact target_refIn_of_step hClosed hStep
  | tail hStep hReach ih =>
      exact ih

end OriginReachableV2

namespace OriginReachableFromV2

theorem target_refIn {S : ItemSetV2 A} (hClosed : ItemSetV2.IsClosedItemSetV2 S)
    {item : YjsItemV2 A} :
    S.RefIn item.origin ->
    S.RefIn item.rightOrigin ->
    ∀ {x : ItemRef}, OriginReachableFromV2 S item x -> S.RefIn x := by
  intro hOrigin hRight x hReach
  cases hReach with
  | origin =>
      exact hOrigin
  | rightOrigin =>
      exact hRight
  | tail_origin hReach =>
      exact OriginReachableV2.target_refIn hClosed hReach
  | tail_rightOrigin hReach =>
      exact OriginReachableV2.target_refIn hClosed hReach

end OriginReachableFromV2

namespace ConflictLtV2'

theorem ltOriginDiff {S : ItemSetV2 A} {item1 item2 : YjsItemV2 A} :
    S.ItemIn item1 ->
    S.ItemIn item2 ->
    YjsLtV2' S item2.origin item1.origin ->
    YjsLtV2' S item1.toRef item2.rightOrigin ->
    YjsLtV2' S item1.origin item2.toRef ->
    YjsLtV2' S item2.toRef item1.rightOrigin ->
    ConflictLtV2' S item1 item2 := by
  intro hItem1 hItem2 hlt1 hlt2 hlt3 hlt4
  rcases hlt1 with ⟨ h1', hlt1' ⟩
  rcases hlt2 with ⟨ h2', hlt2' ⟩
  rcases hlt3 with ⟨ h3', hlt3' ⟩
  rcases hlt4 with ⟨ h4', hlt4' ⟩
  exact ⟨ _, ConflictLtV2.ltOriginDiff (h1 := h1') (h2 := h2') (h3 := h3') (h4 := h4')
    hItem1 hItem2 hlt1' hlt2' hlt3' hlt4' ⟩

theorem ltOriginSame {S : ItemSetV2 A} {item1 item2 : YjsItemV2 A} :
    S.ItemIn item1 ->
    S.ItemIn item2 ->
    item1.origin = item2.origin ->
    YjsLtV2' S item1.toRef item2.rightOrigin ->
    YjsLtV2' S item2.toRef item1.rightOrigin ->
    item1.id < item2.id ->
    ConflictLtV2' S item1 item2 := by
  intro hItem1 hItem2 hOrigin hlt1 hlt2 hId
  rcases hlt1 with ⟨ h1', hlt1' ⟩
  rcases hlt2 with ⟨ h2', hlt2' ⟩
  exact ⟨ _, ConflictLtV2.ltOriginSame (h1 := h1') (h2 := h2')
    hItem1 hItem2 hOrigin hlt1' hlt2' hId ⟩

end ConflictLtV2'

namespace YjsLtV2'

theorem ltConflict {S : ItemSetV2 A} {item1 item2 : YjsItemV2 A} :
    ConflictLtV2' S item1 item2 ->
    YjsLtV2' S item1.toRef item2.toRef := by
  intro hConflict
  rcases hConflict with ⟨ h, hConflict ⟩
  exact ⟨ _, YjsLtV2.ltConflict (h := h) hConflict ⟩

theorem ltOriginOrder {S : ItemSetV2 A} {x y : ItemRef} :
    OriginLtV2 S x y ->
    YjsLtV2' S x y := by
  intro hOrigin
  exact ⟨ 0, YjsLtV2.ltOriginOrder hOrigin ⟩

theorem ltOrigin {S : ItemSetV2 A} {x : ItemRef} {item : YjsItemV2 A} :
    S.ItemIn item ->
    YjsLeqV2' S x item.origin ->
    YjsLtV2' S x item.toRef := by
  intro hItem hLeq
  rcases hLeq with ⟨ h, hLeq ⟩
  exact ⟨ _, YjsLtV2.ltOrigin (h := h) hItem hLeq ⟩

theorem ltRightOrigin {S : ItemSetV2 A} {item : YjsItemV2 A} {x : ItemRef} :
    S.ItemIn item ->
    YjsLeqV2' S item.rightOrigin x ->
    YjsLtV2' S item.toRef x := by
  intro hItem hLeq
  rcases hLeq with ⟨ h, hLeq ⟩
  exact ⟨ _, YjsLtV2.ltRightOrigin (h := h) hItem hLeq ⟩

end YjsLtV2'

namespace YjsLeqV2'

theorem leqSame {S : ItemSetV2 A} (x : ItemRef) :
    YjsLeqV2' S x x := by
  exact ⟨ 0, YjsLeqV2.leqSame x ⟩

theorem leqLt {S : ItemSetV2 A} {x y : ItemRef} :
    YjsLtV2' S x y ->
    YjsLeqV2' S x y := by
  intro hLt
  rcases hLt with ⟨ h, hLt ⟩
  exact ⟨ h + 1, YjsLeqV2.leqLt (h := h) hLt ⟩

end YjsLeqV2'
