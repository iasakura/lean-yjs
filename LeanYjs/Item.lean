import LeanYjs.ClientId

variable (A : Type) [DecidableEq A]

structure YjsId where
  clientId : ClientId
  clock : Nat
deriving Repr, DecidableEq

instance : LT YjsId where
  lt id1 id2 :=
    if id1.clientId == id2.clientId then
      id1.clock > id2.clock
    else
      id1.clientId < id2.clientId

instance : DecidableRel (· < · : YjsId → YjsId → Prop) := by
  intros x y
  obtain ⟨ x_clientId, x_clock ⟩ := x
  obtain ⟨ y_clientId, y_clock ⟩ := y
  simp only [LT.lt]
  simp
  split
  . by_cases h : x_clock > y_clock
    . exact isTrue h
    . apply isFalse; omega
  . by_cases h : x_clientId < y_clientId
    . exact isTrue h
    . apply isFalse; omega

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr
  deriving Repr, DecidableEq

structure YjsItem : Type where
  origin : YjsPtr
  rightOrigin : YjsPtr
  id : YjsId
  content : A
deriving Repr, DecidableEq
end

mutual
def YjsPtr.size {A : Type} : YjsPtr A -> Nat
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} : YjsItem A -> Nat
  | YjsItem.mk origin rightOrigin _ _ =>
    origin.size + rightOrigin.size + 2
end

instance : BEq ClientId where
  beq x y := by
    unfold ClientId at x y
    apply Nat.beq x y

instance : BEq (YjsItem A) where
  beq := fun x y => decide (x = y)

instance : BEq (@YjsPtr A) where
  beq := fun x y => decide (x = y)

instance : LawfulBEq (YjsItem A) := by
  constructor
  . intros x y
    simp

instance : Coe (YjsItem A) (YjsPtr A) where
  coe item := YjsPtr.itemPtr item

/-! ### Order on identifiers

`YjsId` is ordered first by client id and, within one client, by *decreasing* clock
(a later operation of the same client sorts before an earlier one).  The lemmas
below expose this definition without going through the `BEq ClientId` instance. -/

theorem ClientId.lt_iff {x y : ClientId} : x < y ↔ Nat.lt x y := Iff.rfl

theorem ClientId.beq_eq_true_iff {x y : ClientId} : (x == y) = true ↔ x = y := by
  show Nat.beq x y = true ↔ x = y
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩

theorem YjsId.lt_iff {a b : YjsId} :
    a < b ↔ (a.clientId = b.clientId ∧ b.clock < a.clock) ∨
      (a.clientId ≠ b.clientId ∧ a.clientId < b.clientId) := by
  simp only [LT.lt]
  by_cases h : a.clientId = b.clientId
  · simp [h]
  · simp [h]

theorem YjsId.lt_of_clientId_lt {a b : YjsId} (h : a.clientId < b.clientId) : a < b :=
  YjsId.lt_iff.2 (Or.inr ⟨by unfold ClientId at *; omega, h⟩)

theorem YjsId.lt_of_clientId_eq {a b : YjsId} (h : a.clientId = b.clientId)
    (hc : b.clock < a.clock) : a < b :=
  YjsId.lt_iff.2 (Or.inl ⟨h, hc⟩)

theorem YjsId.clientId_lt_of_lt_of_ne {a b : YjsId} (hlt : a < b)
    (hne : a.clientId ≠ b.clientId) : a.clientId < b.clientId := by
  rcases YjsId.lt_iff.1 hlt with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd h hne
  · exact h

theorem YjsId.clock_gt_of_lt_of_eq {a b : YjsId} (hlt : a < b)
    (heq : a.clientId = b.clientId) : b.clock < a.clock := by
  rcases YjsId.lt_iff.1 hlt with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd heq h

theorem ClientId.lt_of_not_lt_of_ne {x y : ClientId} (h : ¬ y < x) (hne : x ≠ y) : x < y :=
  Nat.lt_of_le_of_ne (Nat.not_lt.1 h) hne
