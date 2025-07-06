import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality

variable {A : Type} {P : ItemSet A} {inv : ItemSetInvariant P}

theorem conflict_lt_x_origin_lt_y {A} {P : ItemSet A} (x : YjsItem A) y :
  IsClosedItemSet P ->
  ConflictLt P h x y -> YjsLt' P x.origin y := by
  intros hclosed hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor
    simp [YjsItem.origin] at *
    apply YjsLt.ltOrigin <;> try assumption
    . apply yjs_lt_p1 at hlt2
      assumption
    . apply YjsLeq.leqSame
      apply yjs_lt_p1 at hlt2
      apply hclosed.closedLeft at hlt2
      assumption

theorem conflict_lt_y_origin_lt_x {A} {P : ItemSet A} x (y : YjsItem A) :
  IsClosedItemSet P ->
  ConflictLt P h x y -> YjsLt' P y.origin x := by
  intros hclosed hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor
    apply YjsLt.ltOrigin
    . apply yjs_lt_p1; assumption
    . right; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor
    simp [YjsItem.origin] at *
    apply YjsLt.ltOrigin <;> try assumption
    . apply yjs_lt_p1 at hlt1
      assumption
    . apply YjsLeq.leqSame
      apply yjs_lt_p1 at hlt1
      apply hclosed.closedLeft at hlt1
      assumption

theorem conflict_lt_y_lt_x_right_origin {A} {P : ItemSet A} (x : YjsItem A) y :
  ConflictLt P h x y -> YjsLt' P y x.rightOrigin := by
  intros hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor; assumption

theorem conflict_lt_x_lt_y_right_origin {A} {P : ItemSet A} x (y : YjsItem A) :
  ConflictLt P h x y -> YjsLt' P x y.rightOrigin := by
  intros hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor; assumption

theorem conflict_lt_trans {A} {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A),
  (∀ m < x.size + y.size + z.size,
  ∀ (x y z : YjsPtr A),
    P x →
      P y →
        P z →
          ∀ (h0 : ℕ), YjsLt P h0 x y → ∀ (h1 : ℕ), YjsLt P h1 y z → x.size + y.size + z.size = m → ∃ h, YjsLt P h x z) ->
  ConflictLt P h1 x y -> ConflictLt P h2 y z -> YjsLt' P x z := by
  intros hclosed x y z ih hxy hyz
  have hP : P x := by
    apply conflict_lt_p1; assumption
  have hy : P y := by
    apply conflict_lt_p2; assumption
  have hz : P z := by
    apply conflict_lt_p2; assumption
  have ⟨ ⟨ xo, xr, xid, xc ⟩, heqx ⟩ : ∃ x' : YjsItem A, x = YjsPtr.itemPtr x' := by
    cases hxy <;> (constructor; eq_refl)
  have ⟨ ⟨ zo, zr, zid, zc ⟩, heqz ⟩ : ∃ z' : YjsItem A, z = YjsPtr.itemPtr z' := by
    cases hyz <;> (constructor; eq_refl)
  subst heqx heqz
  have hltxrz :
    YjsLeq' P xr (YjsItem.item zo zr zid zc) ∨ YjsLt' P (YjsItem.item zo zr zid zc) xr := by
    apply yjs_lt_total <;> try assumption
    apply hclosed.closedRight; assumption
  have hltxzo :
    YjsLeq' P (YjsItem.item xo xr xid xc) zo ∨ YjsLt' P zo (YjsItem.item xo xr xid xc) := by
    apply yjs_lt_total <;> try assumption
    apply hclosed.closedLeft; assumption

  have hyzr : YjsLt' P y zr := by
    cases hyz <;> try (constructor; assumption)

  have hxoy : YjsLt' P xo y := by
    cases hxy <;> try (constructor; assumption)
    constructor
    apply YjsLt.ltOrigin <;> try assumption
    left
    apply hclosed.closedLeft; assumption

  have hltxzr : YjsLt' P (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)) zr := by
    obtain ⟨ _, hyzr ⟩ := hyzr
    apply ih (y := y) ((YjsPtr.itemPtr (YjsItem.item xo xr xid xc)).size + y.size + zr.size) (by simp [YjsItem.size, YjsPtr.size] at *; omega) _ _ hP hy (by apply hclosed.closedRight; assumption) <;> try simp
    . apply YjsLt.ltConflict
      assumption
    . assumption

  have hltxoz : YjsLt' P xo (YjsPtr.itemPtr (YjsItem.item zo zr zid zc)) := by
    obtain ⟨ _, hxoy ⟩ := hxoy
    apply ih (y := y) (xo.size + y.size + (YjsPtr.itemPtr (YjsItem.item zo zr zid zc)).size) (by simp [YjsItem.size, YjsPtr.size] at *; omega) _ _ (by apply hclosed.closedLeft; assumption) hy hz <;> try simp
    . assumption
    . apply YjsLt.ltConflict
      assumption

  cases hltxrz with
  | inl hltxrz =>
    obtain ⟨ _, hltxrz ⟩ := hltxrz
    constructor
    apply YjsLt.ltRightOrigin <;> assumption
  | inr hltzxr =>
    cases hltxzo with
    | inl hltxzo =>
      obtain ⟨ _, hltxzo ⟩ := hltxzo
      constructor
      apply YjsLt.ltOrigin <;> assumption
    | inr hltzox =>
      cases hxy with
      | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
        cases hyz with
        | ltOriginDiff h5 h6 h7 h8 l3 l4 r3 r4 id3 id4 c3 c4 hlt5 hlt6 hlt7 hlt8 =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz
          have hlt : zo.size + l2.size + xo.size <
            (YjsPtr.itemPtr (YjsItem.item xo xr xid xc)).size +
            (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2)).size +
            (YjsPtr.itemPtr (YjsItem.item zo zr zid zc)).size := by
            simp [YjsItem.size, YjsPtr.size] at *
            omega
          obtain ⟨ _, hlt ⟩ := ih (y := l2) (zo.size + l2.size + xo.size) hlt zo xo (by apply hclosed.closedLeft; assumption) (by apply hclosed.closedLeft; assumption) (by apply hclosed.closedLeft; assumption) _ hlt5 _ hlt1 (refl _)
          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
        | ltOriginSame h5 h6 l3 r3 id3 id4 c3 c4 hlt5 hlt6 _ =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
      | ltOriginSame h1 h2 l1 r1 id1 id2 c1 c2 hlt1 hlt2 _ =>
        cases hyz with
        | ltOriginDiff h5 h6 h7 h8 l3 l4 r3 r4 id3 id4 c3 c4 hlt5 hlt6 hlt7 hlt8 =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
        | ltOriginSame h5 h6 l3 r3 id3 id4 c3 c4 hlt5 hlt6 _ =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginSame <;> try assumption
          unfold ActorId at *
          omega

theorem yjs_lt_trans {A : Type} {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' P x y -> YjsLt' P y z -> YjsLt' P x z := by
  intros hP x y z hx hy hz hxy hyz
  unfold YjsLt' at *
  obtain ⟨ h0, hxy ⟩ := hxy
  obtain ⟨ h1, hyz ⟩ := hyz
  generalize hsize : x.size + y.size + z.size = total_size
  revert x y z h0 h1
  apply @Nat.strongRecOn' (P := fun ts => ∀ x y z,
    P x → P y → P z →
    ∀ h0, YjsLt P h0 x y → ∀ h1, YjsLt P h1 y z → x.size + y.size + z.size = ts → ∃ h, YjsLt P h x z) total_size
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
  | ⟨ y', hyeq, h, hleq  ⟩
  | hxyconflict
  . subst hxeq
    obtain ⟨ o, r, id, c ⟩ := x'
    simp [YjsItem.rightOrigin] at hleq
    obtain ⟨ h', hleq ⟩ := hleq
    cases hleq with
    | leqSame =>
      constructor
      apply YjsLt.ltRightOrigin (h1 + 1) <;> try assumption
      right; assumption
    | leqLt h _ _ hlt =>
      have hsize : r.size + y.size + z.size < total_size := by
        simp [YjsItem.size, YjsPtr.size] at hsize
        omega
      have hpr : P r := by
        apply hP.closedRight; assumption
      obtain ⟨ h, hlt ⟩ := ih (r.size + y.size + z.size) hsize r y z hpr hy hz _ hlt _ hyz (refl _)
      constructor
      apply YjsLt.ltRightOrigin (h + 1) <;> try assumption
      right; assumption
  . subst hyeq
    rcases hyzcases with
    ⟨ y', hyeq, hyz, hleq' ⟩
    | ⟨ z', hzeq, hyz, hleq' ⟩
    | hyzconflict
    . obtain ⟨ o, r, id, c ⟩ := y'
      simp [YjsItem.origin] at hleq
      cases hyeq
      simp [YjsItem.rightOrigin] at hleq'
      have ⟨ hor, horlt ⟩ : YjsLt' P o r := by
        apply inv.origin_not_leq <;> assumption
      cases hleq with
      | leqSame =>
        cases hleq' with
        | leqSame =>
          constructor; assumption
        | leqLt h _ _ hlt' =>
          apply ih (o.size + r.size + z.size) _ o r z _ _ _ _ horlt _ hlt' <;> try assumption
          simp
          simp [YjsItem.size, YjsPtr.size] at hsize
          omega
          apply hP.closedRight; assumption
      | leqLt h _ _ hlt =>
        cases hleq' with
        | leqSame =>
          apply ih (x.size + o.size + z.size) _ x o z _ _ _ _ hlt _ horlt <;> try assumption
          simp
          simp [YjsItem.size, YjsPtr.size] at hsize
          omega
          apply hP.closedLeft; assumption
        | leqLt h _ _ hlt' =>
          have ⟨ h', hoz ⟩ : YjsLt' P o z := by
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
      | leqSame =>
        constructor
        apply YjsLt.ltOrigin (h0 + 1) _ _ _ _ <;> try assumption
        right; assumption
      | leqLt h _ _ hlt' =>
        have hsize : x.size + (YjsPtr.itemPtr y').size + o.size < total_size := by
          simp [YjsItem.size, YjsPtr.size] at *
          omega
        have hpo : P o := by
          apply hP.closedLeft; assumption
        obtain ⟨ h, hlt ⟩ := ih (x.size + (YjsPtr.itemPtr y').size + o.size) hsize x y' o hx hy hpo _ hxy _ hlt' (refl _)
        constructor
        apply YjsLt.ltOrigin (h + 1) <;> try assumption
        right; assumption
    . obtain ⟨ _, hyzconflict ⟩ := hyzconflict
      apply conflict_lt_x_origin_lt_y _ _ hP at hyzconflict
      obtain ⟨ _, hlt' ⟩ := hyzconflict
      cases hleq with
      | leqSame =>
        constructor; assumption

      | leqLt h _ _ hlt =>
        apply ih (x.size + y'.origin.size + z.size) _ x y'.origin z _ _ _ _ hlt _ hlt' (refl _) <;> try assumption
        . obtain ⟨ o, r, id, c ⟩ := y'
          simp [ YjsItem.origin, YjsItem.size, YjsPtr.size] at *
          omega
        . obtain ⟨ o, r, id, c ⟩ := y'
          apply hP.closedLeft; assumption
  . rcases hyzcases with
    ⟨ y', hyeq, hyz, hleq' ⟩
    | ⟨ z', hzeq, hyz, hleq' ⟩
    | hyzconflict
    . subst hyeq
      obtain ⟨ o, r, id, c ⟩ := y'
      simp [YjsItem.rightOrigin] at hleq'
      obtain ⟨ h', hxyconflict ⟩ := hxyconflict
      apply conflict_lt_x_lt_y_right_origin at hxyconflict
      obtain ⟨ _, hltxy ⟩ := hxyconflict
      cases hleq' with
      | leqSame =>
        constructor; assumption
      | leqLt h _ _ hlt' =>
        apply ih (x.size + r.size + z.size) _ x r z _ _ _ _ hltxy _ hlt' <;> try assumption
        simp
        simp [YjsItem.size, YjsPtr.size] at hsize
        omega
        apply hP.closedRight; assumption
    . subst hzeq
      suffices YjsLt' P  x z'.origin by
        obtain ⟨ h', this ⟩ := this
        obtain ⟨ o, r, id, c ⟩ := z'
        constructor
        apply YjsLt.ltOrigin (h' + 1) <;> try assumption
        right; assumption
      cases hleq' with
      | leqSame =>
        constructor; assumption
      | leqLt h _ _ hlt' =>
        obtain ⟨ o, r, id, c ⟩ := z'
        apply ih (x.size + y.size + o.size) _ x y o _ _ _ _ hxy _ hlt' (refl _) <;> try assumption
        . simp [YjsItem.origin, YjsItem.size, YjsPtr.size] at *
          omega
        . apply hP.closedLeft; assumption
    . obtain ⟨ _, hxyconflict ⟩ := hxyconflict
      obtain ⟨ _, hyzconflict ⟩ := hyzconflict
      subst hsize
      apply conflict_lt_trans hP _ _ _ ih hxyconflict hyzconflict; assumption

theorem yjs_leq_p_trans1 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  IsClosedItemSet P -> @YjsLeq A P h1 x y -> @YjsLt A P h2 y z -> ∃ h, @YjsLt A P h x z := by
  intros hclosed hleq hlt
  have hpy : P y := by
    apply yjs_lt_p1; assumption
  have hpz : P z := by
    apply yjs_lt_p2; assumption
  have hpx : P x := by
    apply yjs_leq_p1 <;> assumption
  cases hleq with
  | leqSame =>
    exists h2
  | leqLt h _ _ hlt =>
    apply yjs_lt_trans (y := y) <;> try assumption
    constructor; assumption
    constructor; assumption

theorem yjs_leq_p_trans2 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  IsClosedItemSet P -> @YjsLt A P h1 x y -> @YjsLeq A P h2 y z -> ∃ h, @YjsLt A P h x z := by
  intros hclosed hlt hleq
  have hpx : P x := by
    apply yjs_lt_p1 <;> assumption
  have hpy : P y := by
    apply yjs_lt_p2; assumption
  have hpz : P z := by
    apply yjs_leq_p2 <;> assumption
  cases hleq with
  | leqSame =>
    exists h1
  | leqLt h _ _ hlt =>
    apply yjs_lt_trans hclosed (y := y) <;> try assumption
    constructor; assumption
    constructor; assumption

theorem yjs_leq_p_trans {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  IsClosedItemSet P -> @YjsLeq A P h1 x y -> @YjsLeq A P h2 y z -> ∃ h, @YjsLeq A P h x z := by
  intros hclosed hleq1 hleq2
  cases hleq1 with
  | leqSame =>
    exists h2
  | leqLt h _ _ hlt =>
    cases hleq2 with
    | leqSame =>
      constructor
      right
      assumption
    | leqLt h _ _ hlt =>
      have hpx : P x := by
        apply yjs_lt_p1 <;> assumption
      have hpy : P y := by
        apply yjs_lt_p2; assumption
      have hpz : P z := by
        apply yjs_lt_p2; assumption
      have ⟨ _, hlt ⟩ : YjsLt' P x z := by
        apply yjs_lt_trans (y := y) <;> try assumption
        constructor; assumption
        constructor; assumption
      constructor
      right
      assumption
