def ActorId := Nat
deriving Repr, DecidableEq

instance : LT ActorId where
  lt x y := Nat.lt x y

instance : DecidableRel (· < · : ActorId → ActorId → Prop) := by
  intros x y
  unfold ActorId at x y
  apply (inferInstance : Decidable (x < y))

instance ActorIdOfNat n : OfNat ActorId n where
  ofNat := n
