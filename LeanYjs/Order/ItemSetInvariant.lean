import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder

variable {A : Type}

-- Defines a subset of YjsItem which are possible DAG of a history of insertions.

variable (P : ItemSet A)

structure ItemSetInvariant where
  origin_not_leq : ∀ (o r : YjsPtr A) c id, P (YjsItem.mk o r id c) ->
    YjsLt' o r
  origin_nearest_reachable : ∀ (o r : YjsPtr A) c id x,
    P (YjsItem.mk o r id c) ->
    OriginReachable (A := A) (YjsItem.mk o r id c) x ->
    (YjsLeq' x o) ∨ (YjsLeq' r x)
  id_unique : ∀ (x y : YjsItem A), x.id = y.id -> P x -> P y -> x = y

@[simp] theorem origin_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> forall (x : YjsItem A), P x -> P x.origin := by
  intros hclosed x px
  obtain ⟨ o, r, id, c ⟩ := x
  simp at *
  apply hclosed.closedLeft <;> assumption

@[simp] theorem right_origin_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> forall (x : YjsItem A), P x -> P x.rightOrigin := by
  intros hclosed x px
  obtain ⟨ o, r, id, c ⟩ := x
  simp at *
  apply hclosed.closedRight <;> assumption

theorem not_ptr_lt_first {A} {P : ItemSet A} : IsClosedItemSet P -> ItemSetInvariant P -> ∀ h (o : YjsPtr A), P o -> ¬ YjsLt h o YjsPtr.first := by
  intros hclosed hinv h o hpo
  generalize hsize : o.size = size
  revert o h
  apply @Nat.strongRecOn' (P := fun s => ∀ h (o : YjsPtr A), P o -> o.size = s -> ¬ YjsLt h o YjsPtr.first) size
  intros n ih h o hpo hsize hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder o _ hlt =>
    cases hlt
  | ltRightOrigin h o r id c hp hlt =>
    cases hlt with
    | leqLt h _ _ hlt =>
      have hsize' : r.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih _ hsize' h r <;> try assumption
      . apply hclosed.closedRight at hpo; assumption
      . simp
    | leqSame =>
      have ⟨ _, hlt ⟩ : YjsLt' o YjsPtr.first := by
        apply hinv.origin_not_leq <;> try assumption
      apply ih (o.size) (by simp [YjsPtr.size, YjsItem.size] at hsize; omega) _ o _ (refl _) hlt
      apply hclosed.closedLeft at hpo; assumption

theorem not_ptr_lt'_first {A} {P : ItemSet A} : IsClosedItemSet P -> ItemSetInvariant P -> ∀ (o : YjsPtr A), P o -> ¬ YjsLt' o YjsPtr.first := by
  intros hclosed hinv o hpo hlt
  obtain ⟨ _, hlt ⟩ := hlt
  apply not_ptr_lt_first hclosed hinv _ o hpo at hlt
  assumption

theorem not_last_lt_ptr {A} {P : ItemSet A} : IsClosedItemSet P -> ItemSetInvariant P -> ∀ h (o : YjsPtr A), P o -> ¬ @YjsLt A h YjsPtr.last o := by
  intros hclosed hinv h o hpo
  generalize hsize : o.size = size
  revert o h
  apply @Nat.strongRecOn' (P := fun size => ∀ (h : ℕ) (o : YjsPtr A), P o -> o.size = size → ¬YjsLt h YjsPtr.last o) size
  intros n ih h o hpo hsize hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _  hpo hlt =>
    cases hlt
  | ltOrigin h x o r id c hlt =>
    cases hlt with
    | leqLt h _ _ hlt =>
      have hsize' : o.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih _ hsize' h o <;> try assumption
      . apply hclosed.closedLeft at hpo; assumption
      . simp
    | leqSame _ =>
      have ⟨ h', hlt ⟩ : YjsLt' YjsPtr.last r := by
        apply hinv.origin_not_leq; assumption
      have hsize' : r.size < n := by
        simp [YjsPtr.size, YjsItem.size] at *
        omega
      apply ih r.size hsize' h' r <;> try assumption
      . apply hclosed.closedRight at hpo; assumption
      . simp

theorem not_last_lt_first {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A h YjsPtr.last YjsPtr.first := by
  intros hinv h
  apply @Nat.strongRecOn' (P := fun h => ¬ @YjsLt A h YjsPtr.last YjsPtr.first)
  intros n ih hlt
  cases hlt with
  | ltConflict h _ _ hlt =>
    cases hlt
  | ltOriginOrder _ _ hlt =>
    cases hlt

theorem not_first_lt_first {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A h YjsPtr.first YjsPtr.first := by
  intros hinv h hlt
  have h: @OriginLt A YjsPtr.first YjsPtr.first := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

theorem not_last_lt_last {A} {P : ItemSet A} : ItemSetInvariant P -> ∀ h, ¬ @YjsLt A h YjsPtr.last YjsPtr.last := by
  intros hinv h hlt
  have h: @OriginLt A YjsPtr.last YjsPtr.last := by
    cases hlt with
    | ltConflict h _ _ hlt =>
      cases hlt
    | ltOriginOrder _ _ hlt =>
      assumption
  cases h with

theorem ItemSetInvariant.eq_set {A} (P Q : ItemSet A) :
  IsClosedItemSet P →
  ItemSetInvariant P →
  (∀x, P x ↔ Q x) →
  ItemSetInvariant Q := by
  intros hPclosed hP hiff
  constructor
  . intros o r c id hq
    rw [<-hiff] at *
    apply hP.origin_not_leq <;> assumption
  . intros o r c id x hq hreachable
    rw [<-hiff] at *
    apply hP.origin_nearest_reachable <;> assumption
  . intros x y h_id_eq h_qx h_qy
    rw [<-hiff] at *
    apply hP.id_unique x y h_id_eq <;> assumption
