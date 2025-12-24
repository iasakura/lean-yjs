import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality

variable {A : Type} {P : ItemSet A} {inv : ItemSetInvariant P}

theorem conflict_lt_x_origin_lt_y {A} {P : ItemSet A} (x : YjsItem A) y :
  IsClosedItemSet P ->
  ConflictLt h x y -> YjsLt' x.origin y := by
  intros hclosed hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor
    simp [YjsItem.origin] at *
    apply YjsLt.ltOrigin <;> try assumption
    apply YjsLeq.leqSame

theorem conflict_lt_y_origin_lt_x {A} {P : ItemSet A} x (y : YjsItem A) :
  IsClosedItemSet P ->
  ConflictLt h x y -> YjsLt' y.origin x := by
  intros hclosed hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor
    apply YjsLt.ltOrigin
    . right; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor
    simp [YjsItem.origin] at *
    apply YjsLt.ltOrigin <;> try assumption
    apply YjsLeq.leqSame

theorem conflict_lt_y_lt_x_right_origin {A} (x : YjsItem A) y :
  ConflictLt h x y -> YjsLt' y x.rightOrigin := by
  intros hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor; assumption

theorem conflict_lt_x_lt_y_right_origin {A} x (y : YjsItem A) :
  ConflictLt h x y -> YjsLt' x y.rightOrigin := by
  intros hlt
  cases hlt with
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 hlt1 hlt2 hlt3 hlt4 =>
    constructor; assumption
  | ltOriginSame h1 h2 l r1 r2 id1 id2 c1 c2 hlt1 hlt2 _ =>
    constructor; assumption

theorem YjsId_lt_trans {x y z : YjsId} :
  x < y → y < z → x < z := by
  intro hxy hyz
  obtain ⟨ x_clientId, x_clock ⟩ := x
  obtain ⟨ y_clientId, y_clock ⟩ := y
  obtain ⟨ z_clientId, z_clock ⟩ := z
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hxy
  . subst x_clientId
    split at hyz
    . subst y_clientId
      simp; omega
    . split
      . omega
      . omega
  . split at hyz
    . subst z_clientId
      split
      . omega
      . omega
    . split
      . omega
      . omega

theorem conflict_lt_trans {A} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A),
  P x ->
    P y ->
      P z ->
  (∀ m < x.size + y.size + z.size,
  ∀ (x y z : YjsPtr A),
    P x →
      P y →
        P z →
          ∀ (h0 : ℕ), YjsLt h0 x y → ∀ (h1 : ℕ), YjsLt h1 y z → x.size + y.size + z.size = m → ∃ h, YjsLt h x z) ->
  ConflictLt h1 x y -> ConflictLt h2 y z -> YjsLt' x z := by
  intros hclosed x y z hpx hpy hpz ih hxy hyz
  have ⟨ ⟨ xo, xr, xid, xc, xd ⟩, heqx ⟩ : ∃ x' : YjsItem A, x = YjsPtr.itemPtr x' := by
    cases hxy <;> (constructor; eq_refl)
  have ⟨ ⟨ zo, zr, zid, zc, zd ⟩, heqz ⟩ : ∃ z' : YjsItem A, z = YjsPtr.itemPtr z' := by
    cases hyz <;> (constructor; eq_refl)
  subst heqx heqz
  have hltxrz :
    YjsLeq' xr (YjsItem.item zo zr zid zc zd) ∨ YjsLt' (YjsItem.item zo zr zid zc zd) xr := by
    apply yjs_lt_total <;> try assumption
    apply hclosed.closedRight; assumption
  have hltxzo :
    YjsLeq' (YjsItem.item xo xr xid xc xd) zo ∨ YjsLt' zo (YjsItem.item xo xr xid xc xd) := by
    apply yjs_lt_total <;> try assumption
    apply hclosed.closedLeft; assumption

  have hyzr : YjsLt' y zr := by
    cases hyz <;> try (constructor; assumption)

  have hxoy : YjsLt' xo y := by
    cases hxy <;> try (constructor; assumption)
    constructor
    apply YjsLt.ltOrigin <;> try assumption
    left

  have hltxzr : YjsLt' (YjsPtr.itemPtr (YjsItem.item xo xr xid xc xd)) zr := by
    obtain ⟨ _, hyzr ⟩ := hyzr
    apply ih (y := y) ((YjsPtr.itemPtr (YjsItem.item xo xr xid xc xd)).size + y.size + zr.size) (by simp [YjsItem.size, YjsPtr.size] at *; omega) _ _ hpx hpy (by apply hclosed.closedRight; assumption) <;> try simp
    . apply YjsLt.ltConflict
      assumption
    . assumption

  have hltxoz : YjsLt' xo (YjsPtr.itemPtr (YjsItem.item zo zr zid zc zd)) := by
    obtain ⟨ _, hxoy ⟩ := hxoy
    apply ih (y := y) (xo.size + y.size + (YjsPtr.itemPtr (YjsItem.item zo zr zid zc zd)).size) (by simp [YjsItem.size, YjsPtr.size] at *; omega) _ _ (by apply hclosed.closedLeft; assumption) hpy hpz <;> try simp
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
      | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 d1 d2 hlt1 hlt2 hlt3 hlt4 =>
        cases hyz with
        | ltOriginDiff h5 h6 h7 h8 l3 l4 r3 r4 id3 id4 c3 c4 d3 d4 hlt5 hlt6 hlt7 hlt8 =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz
          have hlt : zo.size + l2.size + xo.size <
            (YjsPtr.itemPtr (YjsItem.item xo xr xid xc xd)).size +
            (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2 d2)).size +
            (YjsPtr.itemPtr (YjsItem.item zo zr zid zc zd)).size := by
            simp [YjsItem.size, YjsPtr.size] at *
            omega
          obtain ⟨ _, hlt ⟩ := ih (y := l2) (zo.size + l2.size + xo.size) hlt zo xo (by apply hclosed.closedLeft; assumption) (by apply hclosed.closedLeft; assumption) (by apply hclosed.closedLeft; assumption) _ hlt5 _ hlt1 (refl _)
          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
        | ltOriginSame h5 h6 l3 r3 id3 id4 c3 c4 d3 d4 hlt5 hlt6 _ =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
      | ltOriginSame h1 h2 l1 r1 id1 id2 c1 c2 d1 d2 hlt1 hlt2 _ =>
        cases hyz with
        | ltOriginDiff h5 h6 h7 h8 l3 l4 r3 r4 id3 id4 c3 c4 d3 d4 hlt5 hlt6 hlt7 hlt8 =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginDiff <;> try assumption
        | ltOriginSame h5 h6 l3 r3 id3 id4 c3 c4 d3 d4 hlt5 hlt6 _ =>
          obtain ⟨ _, _ ⟩ := hltzxr
          obtain ⟨ _, _ ⟩ := hltzox
          obtain ⟨ _, _ ⟩ := hltxzr
          obtain ⟨ _, _ ⟩ := hltxoz

          constructor
          apply YjsLt.ltConflict
          apply ConflictLt.ltOriginSame <;> try assumption
          unfold ClientId at *
          apply YjsId_lt_trans (y := c1) <;> try assumption

theorem yjs_lt_trans {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' x y -> YjsLt' y z -> YjsLt' x z := by
  intros hP x y z hx hy hz hxy hyz
  unfold YjsLt' at *
  obtain ⟨ h0, hxy ⟩ := hxy
  obtain ⟨ h1, hyz ⟩ := hyz
  generalize hsize : x.size + y.size + z.size = total_size
  revert x y z h0 h1
  apply @Nat.strongRecOn' (P := fun ts => ∀ x y z,
    P x → P y → P z →
    ∀ h0, YjsLt h0 x y → ∀ h1, YjsLt h1 y z → x.size + y.size + z.size = ts → ∃ h, YjsLt h x z) total_size
  intros total_size ih x y z hx hy hz h0 hxy h1 hyz hsize
  -- first, we prove the corner cases x = first or y = first/last, or z = last
  rcases yjs_lt_cases _ _ _ _ hxy with
  ⟨ hxeq, hylast | ⟨ y', hy' ⟩ ⟩
  | ⟨ hyeq, _ ⟩
  | hxycases
  -- | ⟨ x', hx'eq, hx'y ⟩
  -- | ⟨ y', hy'eq, hyy' ⟩
  -- | hconflict
  . -- x = first and y = last
    subst hylast
    by_contra
    apply not_last_lt_ptr hP inv _ _ hz at hyz; assumption
  . -- x = first and y = itemPtr y'
    subst hxeq hy'
    cases z with
    | first =>
      apply not_ptr_lt_first hP inv _ _ hy at hyz
      cases hyz
    | last =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first_last
    | itemPtr y' =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first
  . -- y = last
    subst hyeq; apply not_last_lt_ptr hP inv _ _ hz at hyz
    cases hyz
  rcases yjs_lt_cases _ _ _ _ hyz with
  ⟨ hyeq, _ ⟩
  | ⟨ hzeq, hyfirst | ⟨ y', hy' ⟩ ⟩
  | hyzcases
  . -- y = first
    subst hyeq
    apply not_ptr_lt_first hP inv _ _ hx at hxy
    cases hxy
  . -- y = first and z = last
    subst hyfirst
    apply not_ptr_lt_first hP inv _ _ hx at hxy
    cases hxy
  . -- y = itemPtr y' and z = last
    subst hzeq hy'
    cases x with
    | first =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first_last
    | last =>
      apply not_last_lt_ptr hP inv _ _ hy at hxy
      cases hxy
    | itemPtr x' =>
      exists 0
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_last
  -- then, we prove the main parts
  rcases hxycases with
  ⟨ x', hxeq, hleq ⟩
  | ⟨ y', hyeq, h, hleq  ⟩
  | hxyconflict
  . subst hxeq
    obtain ⟨ o, r, id, c, d ⟩ := x'
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
    . obtain ⟨ o, r, id, c, d ⟩ := y'
      simp [YjsItem.origin] at hleq
      cases hyeq
      simp [YjsItem.rightOrigin] at hleq'
      have ⟨ hor, horlt ⟩ : YjsLt' o r := by
        apply inv.origin_not_leq (o := o) (r := r) (c := c) (id := id) (d := d) <;> assumption
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
          have ⟨ h', hoz ⟩ : YjsLt' o z := by
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
      obtain ⟨ o, r, id, c, d ⟩ := z'
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
        . obtain ⟨ o, r, id, c, d ⟩ := y'
          simp [ YjsItem.origin, YjsItem.size, YjsPtr.size] at *
          omega
        . obtain ⟨ o, r, id, c, d ⟩ := y'
          apply hP.closedLeft; assumption
  . rcases hyzcases with
    ⟨ y', hyeq, hyz, hleq' ⟩
    | ⟨ z', hzeq, hyz, hleq' ⟩
    | hyzconflict
    . subst hyeq
      obtain ⟨ o, r, id, c, d ⟩ := y'
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
      suffices YjsLt' x z'.origin by
        obtain ⟨ h', this ⟩ := this
        obtain ⟨ o, r, id, c, d ⟩ := z'
        constructor
        apply YjsLt.ltOrigin (h' + 1) <;> try assumption
        right; assumption
      cases hleq' with
      | leqSame =>
        constructor; assumption
      | leqLt h _ _ hlt' =>
        obtain ⟨ o, r, id, c, d ⟩ := z'
        apply ih (x.size + y.size + o.size) _ x y o _ _ _ _ hxy _ hlt' (refl _) <;> try assumption
        . simp [YjsItem.origin, YjsItem.size, YjsPtr.size] at *
          omega
        . apply hP.closedLeft; assumption
    . obtain ⟨ _, hxyconflict ⟩ := hxyconflict
      obtain ⟨ _, hyzconflict ⟩ := hyzconflict
      subst hsize
      apply conflict_lt_trans hP _ _ _ hx hy hz ih hxyconflict hyzconflict; assumption

theorem yjs_leq_p_trans1 {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  P x -> P y -> P z ->
  IsClosedItemSet P -> @YjsLeq A h1 x y -> @YjsLt A h2 y z -> ∃ h, @YjsLt A h x z := by
  intros hpx hpy hpz hclosed hleq hlt
  cases hleq with
  | leqSame =>
    exists h2
  | leqLt h _ _ hlt =>
    apply yjs_lt_trans (y := y) <;> try assumption
    constructor; assumption
    constructor; assumption

theorem yjs_leq'_p_trans1 {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A):
  P x -> P y -> P z ->
  IsClosedItemSet P -> YjsLeq' x y -> YjsLt' y z -> YjsLt' x z := by
  intros hpx hpy hpz hclosed hleq hlt
  obtain ⟨ _, hleq ⟩ := hleq
  obtain ⟨ _, hlt ⟩ := hlt
  apply yjs_leq_p_trans1 (x := x) (y := y) (z := z) <;> assumption

theorem yjs_leq_p_trans2 {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  P x -> P y -> P z ->
  IsClosedItemSet P -> @YjsLt A h1 x y -> @YjsLeq A h2 y z -> ∃ h, @YjsLt A h x z := by
  intros hpx hpy hpz hclosed hlt hleq
  cases hleq with
  | leqSame =>
    exists h1
  | leqLt h _ _ hlt =>
    apply yjs_lt_trans hclosed (y := y) <;> try assumption
    constructor; assumption
    constructor; assumption

theorem yjs_leq'_p_trans2 {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A):
  P x -> P y -> P z ->
  IsClosedItemSet P -> YjsLt' x y -> YjsLeq' y z -> YjsLt' x z := by
  intros hpx hpy hpz hclosed hlt hleq
  obtain ⟨ _, hlt ⟩ := hlt
  obtain ⟨ _, hleq ⟩ := hleq
  apply yjs_leq_p_trans2 (x := x) (y := y) (z := z) <;> assumption

theorem yjs_leq_p_trans {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2:
  P x -> P y -> P z ->
  IsClosedItemSet P -> @YjsLeq A h1 x y -> @YjsLeq A h2 y z -> ∃ h, @YjsLeq A h x z := by
  intros hpx hpy hpz hclosed hleq1 hleq2
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
      have ⟨ _, hlt ⟩ : YjsLt' x z := by
        apply yjs_lt_trans (y := y) <;> try assumption
        constructor; assumption
        constructor; assumption
      constructor
      right
      assumption

theorem yjs_leq'_p_trans {A} [DecidableEq A] {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A):
  P x -> P y -> P z ->
  IsClosedItemSet P -> YjsLeq' x y -> YjsLeq' y z -> YjsLeq' x z := by
  intros hpx hpy hpz hclosed hleq1 hleq2
  obtain ⟨ _, hleq1 ⟩ := hleq1
  obtain ⟨ _, hleq2 ⟩ := hleq2
  apply yjs_leq_p_trans inv x y z _ _ hpx hpy hpz hclosed hleq1 hleq2
