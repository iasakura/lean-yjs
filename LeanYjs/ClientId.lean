def ClientId := Nat
deriving Repr, DecidableEq

instance : LT ClientId where
  lt x y := Nat.lt x y

instance : DecidableRel (· < · : ClientId → ClientId → Prop) := by
  intros x y
  unfold ClientId at x y
  apply (inferInstance : Decidable (x < y))

instance ClientIdOfNat n : OfNat ClientId n where
  ofNat := n
