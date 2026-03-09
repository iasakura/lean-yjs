import LeanYjs.ItemBridgeV2
import LeanYjs.Order.AsymmetryV2
import LeanYjs.Algorithm.Invariant.Basic

variable {A : Type}
variable [DecidableEq A]

namespace OldToV2

abbrev UniqueIdOld (arr : List (YjsItem A)) : Prop :=
  List.Pairwise (fun x y : YjsItem A => x.id ≠ y.id) arr

omit [DecidableEq A] in theorem arrSet_refIn_toRefV2 {arr : List (YjsItem A)} {p : YjsPtr A} :
    UniqueIdOld arr ->
    ArrSet arr p ->
    (ItemSetV2.ofOldItems arr).RefIn p.toRefV2 := by
  intro hUnique hIn
  cases p with
  | first =>
      exact trivial
  | last =>
      exact trivial
  | itemPtr item =>
      simpa [YjsPtr.toRefV2, ArrSet] using
        ItemSetV2.refIn_toRef_of_mem_of_pairwise (items := arr) (item := item) hUnique hIn

omit [DecidableEq A] in theorem arrSet_itemIn_toV2 {arr : List (YjsItem A)} {item : YjsItem A} :
    UniqueIdOld arr ->
    ArrSet arr item ->
    (ItemSetV2.ofOldItems arr).ItemIn item.toV2 := by
  intro hUnique hIn
  simpa [ArrSet] using
    ItemSetV2.itemIn_toV2_of_mem_of_pairwise (items := arr) (item := item) hUnique hIn

theorem originReachableStep_to_v2 {arr : List (YjsItem A)} :
    UniqueIdOld arr ->
    ∀ {x y : YjsPtr A},
      OriginReachableStep x y ->
      ArrSet arr x ->
      OriginReachableStepV2 (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2 := by
  intro hUnique x y hStep hIn
  cases x with
  | first =>
      cases hStep
  | last =>
      cases hStep
  | itemPtr item =>
      have hItemIn :
          (ItemSetV2.ofOldItems arr).ItemIn item.toV2 := by
        exact arrSet_itemIn_toV2 (arr := arr) (item := item) hUnique hIn
      cases hStep with
      | reachable o r id c =>
          simpa [YjsPtr.toRefV2, YjsItem.toV2] using
            (OriginReachableStepV2.left (S := ItemSetV2.ofOldItems arr) hItemIn)
      | reachable_right o r id c =>
          simpa [YjsPtr.toRefV2, YjsItem.toV2] using
            (OriginReachableStepV2.right (S := ItemSetV2.ofOldItems arr) hItemIn)

theorem originReachable_to_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ∀ {x y : YjsPtr A},
      OriginReachable x y ->
      ArrSet arr x ->
      OriginReachableV2 (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2 := by
  intro hClosed hUnique x y hReach
  induction hReach with
  | reachable_single x y hStep =>
      intro hIn
      exact .single (originReachableStep_to_v2 (arr := arr) hUnique hStep hIn)
  | reachable_head x y z hStep hTail ih =>
      intro hIn
      have hMid : ArrSet arr y := by
        cases x with
        | first =>
            cases hStep
        | last =>
            cases hStep
        | itemPtr item =>
            cases item with
            | mk o r id c =>
                cases hStep with
                | reachable =>
                    exact hClosed.closedLeft _ _ _ _ hIn
                | reachable_right =>
                    exact hClosed.closedRight _ _ _ _ hIn
      exact .tail
        (originReachableStep_to_v2 (arr := arr) hUnique hStep hIn)
        (ih hMid)

theorem yjsLt_to_v2' {arr : List (YjsItem A)} (hClosed : ArrSetClosed arr) (hUnique : UniqueIdOld arr) :
    ∀ {x y : YjsPtr A},
      YjsLt' x y ->
      ArrSet arr x ->
      ArrSet arr y ->
      YjsLtV2' (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2 := by
  intro x y hLt hx hy
  rcases hLt with ⟨ n, hLt ⟩
  let P : Nat -> Prop := fun n =>
    ∀ (x y : YjsPtr A),
      YjsLt n x y ->
      ArrSet arr x ->
      ArrSet arr y ->
      YjsLtV2' (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y hLt hx hy
    cases hLt with
  | ltOriginOrder _ _ hOrigin =>
      cases hOrigin with
      | lt_first item =>
          have hyRef :
              (ItemSetV2.ofOldItems arr).RefIn (.idRef item.id) := by
            simpa [YjsPtr.toRefV2, ArrSet] using
              ItemSetV2.refIn_toRef_of_mem_of_pairwise
                (items := arr) (item := item) hUnique hy
          simpa [YjsPtr.toRefV2] using
            (YjsLtV2'.first_lt_idRef (S := ItemSetV2.ofOldItems arr) hyRef)
      | lt_last item =>
          have hxRef :
              (ItemSetV2.ofOldItems arr).RefIn (.idRef item.id) := by
            simpa [YjsPtr.toRefV2, ArrSet] using
              ItemSetV2.refIn_toRef_of_mem_of_pairwise
                (items := arr) (item := item) hUnique hx
          simpa [YjsPtr.toRefV2] using
            (YjsLtV2'.idRef_lt_last (S := ItemSetV2.ofOldItems arr) hxRef)
      | lt_first_last =>
          simpa [YjsPtr.toRefV2] using
            (YjsLtV2'.first_lt_last (S := ItemSetV2.ofOldItems arr))
  | ltOrigin h x o r id c hLeq =>
      have hItemIn :
          (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk o r id c).toV2 := by
        exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk o r id c) hUnique hy
      have ho : ArrSet arr o := by
        exact hClosed.closedLeft _ _ _ _ hy
      have hLeqV2 :
          YjsLeqV2' (ItemSetV2.ofOldItems arr) x.toRefV2 o.toRefV2 := by
        cases hLeq with
        | leqSame _ =>
            exact YjsLeqV2'.leqSame _
        | leqLt h' _ _ hLt' =>
            exact YjsLeqV2'.leqLt <|
              ih h' (by omega) x o hLt' hx ho
      simpa [YjsPtr.toRefV2, YjsItem.toV2] using
        (YjsLtV2'.ltOrigin (S := ItemSetV2.ofOldItems arr) hItemIn hLeqV2)
  | ltRightOrigin h o r id c _ hLeq =>
      have hItemIn :
          (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk o r id c).toV2 := by
        exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk o r id c) hUnique hx
      have hr : ArrSet arr r := by
        exact hClosed.closedRight _ _ _ _ hx
      have hLeqV2 :
          YjsLeqV2' (ItemSetV2.ofOldItems arr) r.toRefV2 y.toRefV2 := by
        cases hLeq with
        | leqSame _ =>
            exact YjsLeqV2'.leqSame _
        | leqLt h' _ _ hLt' =>
            exact YjsLeqV2'.leqLt <|
              ih h' (by omega) r y hLt' hr hy
      simpa [YjsPtr.toRefV2, YjsItem.toV2] using
        (YjsLtV2'.ltRightOrigin (S := ItemSetV2.ofOldItems arr) hItemIn hLeqV2)
  | ltConflict h _ _ hConflict =>
      cases hConflict with
      | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
          have hxItemIn :
              (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk l1 r1 id1 c1).toV2 := by
            exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk l1 r1 id1 c1) hUnique hx
          have hyItemIn :
              (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk l2 r2 id2 c2).toV2 := by
            exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk l2 r2 id2 c2) hUnique hy
          have hl1 : ArrSet arr l1 := by
            exact hClosed.closedLeft _ _ _ _ hx
          have hr1 : ArrSet arr r1 := by
            exact hClosed.closedRight _ _ _ _ hx
          have hl2 : ArrSet arr l2 := by
            exact hClosed.closedLeft _ _ _ _ hy
          have hr2 : ArrSet arr r2 := by
            exact hClosed.closedRight _ _ _ _ hy
          have hlt1V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) l2.toRefV2 l1.toRefV2 := by
            exact ih h1 (by unfold max4; omega) l2 l1 hlt1 hl2 hl1
          have hlt2V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) (YjsItem.mk l1 r1 id1 c1).toV2.toRef r2.toRefV2 := by
            exact ih h2 (by unfold max4; omega) (YjsItem.mk l1 r1 id1 c1) r2 hlt2 hx hr2
          have hlt3V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) l1.toRefV2 (YjsItem.mk l2 r2 id2 c2).toV2.toRef := by
            exact ih h3 (by unfold max4; omega) l1 (YjsItem.mk l2 r2 id2 c2) hlt3 hl1 hy
          have hlt4V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) (YjsItem.mk l2 r2 id2 c2).toV2.toRef r1.toRefV2 := by
            exact ih h4 (by unfold max4; omega) (YjsItem.mk l2 r2 id2 c2) r1 hlt4 hy hr1
          simpa [YjsItem.toV2] using
            (YjsLtV2'.ltConflict <|
              ConflictLtV2'.ltOriginDiff (S := ItemSetV2.ofOldItems arr)
                hxItemIn hyItemIn hlt1V2 hlt2V2 hlt3V2 hlt4V2)
      | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 hId =>
          have hxItemIn :
              (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk l r1 id1 c1).toV2 := by
            exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk l r1 id1 c1) hUnique hx
          have hyItemIn :
              (ItemSetV2.ofOldItems arr).ItemIn (YjsItem.mk l r2 id2 c2).toV2 := by
            exact arrSet_itemIn_toV2 (arr := arr) (item := YjsItem.mk l r2 id2 c2) hUnique hy
          have hr1 : ArrSet arr r1 := by
            exact hClosed.closedRight _ _ _ _ hx
          have hr2 : ArrSet arr r2 := by
            exact hClosed.closedRight _ _ _ _ hy
          have hlt1V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) (YjsItem.mk l r1 id1 c1).toV2.toRef r2.toRefV2 := by
            exact ih h1 (by omega) (YjsItem.mk l r1 id1 c1) r2 hlt1 hx hr2
          have hlt2V2 :
              YjsLtV2' (ItemSetV2.ofOldItems arr) (YjsItem.mk l r2 id2 c2).toV2.toRef r1.toRefV2 := by
            exact ih h2 (by omega) (YjsItem.mk l r2 id2 c2) r1 hlt2 hy hr1
          simpa [YjsItem.toV2] using
            (YjsLtV2'.ltConflict <|
              ConflictLtV2'.ltOriginSame (S := ItemSetV2.ofOldItems arr)
                hxItemIn hyItemIn rfl hlt1V2 hlt2V2 hId)
  exact hP n x y hLt hx hy
theorem yjsLt_to_v2 {arr : List (YjsItem A)} (hClosed : ArrSetClosed arr) (hUnique : UniqueIdOld arr) :
    ∀ {h : Nat} {x y : YjsPtr A},
      YjsLt h x y ->
      ArrSet arr x ->
      ArrSet arr y ->
      YjsLtV2' (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2 := by
  intro h x y hLt hx hy
  exact yjsLt_to_v2' hClosed hUnique ⟨ h, hLt ⟩ hx hy

theorem yjsLeq_to_v2 {arr : List (YjsItem A)} (hClosed : ArrSetClosed arr) (hUnique : UniqueIdOld arr) :
    ∀ {h : Nat} {x y : YjsPtr A},
      YjsLeq h x y ->
      ArrSet arr x ->
      ArrSet arr y ->
      YjsLeqV2' (ItemSetV2.ofOldItems arr) x.toRefV2 y.toRefV2 := by
  intro h x y hLeq hx hy
  cases hLeq with
  | leqSame _ =>
      exact YjsLeqV2'.leqSame x.toRefV2
  | leqLt _ _ _ hLt =>
      exact YjsLeqV2'.leqLt (yjsLt_to_v2 hClosed hUnique hLt hx hy)

theorem origin_lt_rightOrigin_to_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ItemSetInvariant (ArrSet arr) ->
    ∀ {item : YjsItem A}, ArrSet arr item ->
      YjsLtV2' (ItemSetV2.ofOldItems arr) item.toV2.origin item.toV2.rightOrigin := by
  intro hClosed hUnique hInv item hItem
  rcases item with ⟨ o, r, id, c ⟩
  have hOld : YjsLt' o r := by
    simpa using hInv.origin_not_leq o r c id hItem
  rcases hOld with ⟨ h, hOld ⟩
  simpa [YjsItem.toV2] using
    (yjsLt_to_v2 hClosed hUnique hOld
      (show ArrSet arr o from hClosed.closedLeft _ _ _ _ hItem)
      (show ArrSet arr r from hClosed.closedRight _ _ _ _ hItem))

theorem origin_nearest_reachable_to_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ItemSetInvariant (ArrSet arr) ->
    ∀ {item : YjsItem A} {x : YjsPtr A},
      ArrSet arr item ->
      OriginReachable item x ->
      YjsLeqV2' (ItemSetV2.ofOldItems arr) x.toRefV2 item.toV2.origin ∨
      YjsLeqV2' (ItemSetV2.ofOldItems arr) item.toV2.rightOrigin x.toRefV2 := by
  intro hClosed hUnique hInv item x hItem hReach
  rcases item with ⟨ o, r, id, c ⟩
  have hx : ArrSet arr x := by
    exact reachable_in arr (YjsItem.mk o r id c) hClosed x hReach hItem
  have hOld :=
    hInv.origin_nearest_reachable o r c id x hItem hReach
  cases hOld with
  | inl hLeq =>
      rcases hLeq with ⟨ h, hLeq ⟩
      left
      simpa [YjsItem.toV2] using
        (yjsLeq_to_v2 hClosed hUnique hLeq hx
          (hClosed.closedLeft _ _ _ _ hItem))
  | inr hLeq =>
      rcases hLeq with ⟨ h, hLeq ⟩
      right
      simpa [YjsItem.toV2] using
        (yjsLeq_to_v2 hClosed hUnique hLeq
          (hClosed.closedRight _ _ _ _ hItem) hx)

end OldToV2
