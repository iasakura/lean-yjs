import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ActorId
import LeanYjs.ItemOrder

variable {A : Type} [BEq A]

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : ItemSet A)

structure ItemSetInvariant where
  origin_not_leq : ∀ (o r c id), P (YjsItem.item o r id c) ->
    YjsLt' P o r
  origin_nearest_reachable : ∀ (o r c id x),
    P (YjsItem.item o r id c) ->
    OriginReachable (YjsItem.item o r id c) x ->
    (∃ h, YjsLeq P h x o) ∨ (∃ h, YjsLeq P h r x)
  same_id_ordered : ∀ (x y : YjsItem A),
    P x -> P y ->
    x ≠ y ->
    x.id = y.id ->
    YjsLt' P x y.origin ∨
    YjsLt' P y x.origin ∨
    YjsLt' P x.rightOrigin y ∨
    YjsLt' P y.rightOrigin x

@[simp] lemma origin_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> forall (x : YjsItem A), P x -> P x.origin := by
  intros hclosed x px
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.origin] at *
  apply hclosed.closedLeft <;> assumption

@[simp] lemma right_origin_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> forall (x : YjsItem A), P x -> P x.rightOrigin := by
  intros hclosed x px
  obtain ⟨ o, r, id, c ⟩ := x
  simp [YjsItem.rightOrigin] at *
  apply hclosed.closedRight <;> assumption

lemma not_ptr_lt_first {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h o YjsPtr.first := by
  intros hinv h o
  generalize hsize : o.size = size
  revert o h
  apply @Nat.strongRecOn' (P := fun s => ∀ h (o : YjsPtr A), o.size = s -> ¬ @YjsLt A P h o YjsPtr.first) size
  intros n ih h o hsize hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder o _ po pf hlt =>
    cases hlt
  | ltRightOrigin h o r id c po hp hlt =>
    cases hlt with
    | leqLt h _ _ hlt =>
      have hsize' : r.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih _ hsize' h r <;> try assumption
      simp
    | leqSame =>
      have ⟨ _, hlt ⟩ : YjsLt' P o YjsPtr.first := by
        apply hinv.origin_not_leq; assumption
      apply ih (o.size) (by simp [YjsPtr.size, YjsItem.size] at hsize; omega) _ o (refl _) hlt

lemma not_last_lt_ptr {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h (o : YjsPtr A), ¬ @YjsLt A P h YjsPtr.last o := by
  intros hinv h o
  generalize hsize : o.size = size
  revert o h
  apply @Nat.strongRecOn' (P := fun size => ∀ (h : ℕ) (o : YjsPtr A), o.size = size → ¬YjsLt P h YjsPtr.last o) size
  intros n ih h o hsize hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ _ hpo hlt =>
    cases hlt
  | ltOrigin h x o r id c hpo hlt =>
    cases hlt with
    | leqLt h _ _ hlt =>
      have hsize' : o.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih _ hsize' h o <;> try assumption
      simp
    | leqSame _ =>
      have ⟨ h', hlt ⟩ : YjsLt' P YjsPtr.last r := by
        apply hinv.origin_not_leq; assumption
      have hsize' : r.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih r.size hsize' h' r <;> try assumption
      simp

lemma not_last_lt_first {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.first := by
  intros hinv h
  apply @Nat.strongRecOn' (P := fun h => ¬ @YjsLt A P h YjsPtr.last YjsPtr.first)
  intros n ih hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ _ _ hlt =>
    cases hlt

lemma not_first_lt_first {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.first YjsPtr.first := by
  intros hinv h hlt
  have h: @OriginLt A YjsPtr.first YjsPtr.first := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

lemma not_last_lt_last {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A P h YjsPtr.last YjsPtr.last := by
  intros hinv h hlt
  have h: @OriginLt A YjsPtr.last YjsPtr.last := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

-- lemma origin_lt_p1 {A} {P : @ItemSet A} {x y : YjsPtr A} (h : OriginLt _ x y) : P x := by
--   sorry

-- lemma origin_lt_p2 {A} {P : @ItemSet A} {x y : YjsPtr A} (h : OriginLt _ x y) : P y := by
--   cases h with
--   | ltOrigin  y hpx hpy hlt
--     assumption
--   -- | ltReachableOrigin o r id c t ho hr ht hreach hlt =>
--   --   assumption
--   -- | ltReachableRight o r id c t ho hr ht hreach hlt =>
--   --   assumption
--   | ltTrans x y z hx hy hz hlt1 hlt2 =>
--     assumption
