import Mathlib.Order.Defs.Unbundled

variable (A : Type) [BEq A]

def ActorId := Nat

instance : LT ActorId where
  lt x y := Nat.lt x y

instance : DecidableRel (· < · : ActorId → ActorId → Prop) := by
  intros x y
  unfold ActorId at x y
  apply (inferInstance : Decidable (x < y))

instance ActorIdOfNat n : OfNat ActorId n where
  ofNat := n

mutual
inductive YjsPtr : Type where
| itemPtr : YjsItem -> YjsPtr
| first : YjsPtr
| last : YjsPtr

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : ActorId -> A -> YjsItem
end

mutual
def YjsPtr.size {A : Type} (x : YjsPtr A) :=
  match x with
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} (item : YjsItem A) :=
  match item with
  | YjsItem.item origin rightOrigin _ _ =>
    origin.size + rightOrigin.size + 2
end

instance : BEq ActorId where
  beq x y := by
    unfold ActorId at x y
    apply Nat.beq x y

mutual
def yjsItemEq (x y : YjsItem A) : Bool :=
  match x, y with
  | YjsItem.item origin1 rightOrigin1 id1 c1, YjsItem.item origin2 rightOrigin2 id2 c2 =>
    yjsPtrEq origin1 origin2 && yjsPtrEq rightOrigin1 rightOrigin2 && id1 == id2 && c1 == c2

def yjsPtrEq (x y : YjsPtr A) : Bool :=
  match x, y with
  | YjsPtr.itemPtr item1, YjsPtr.itemPtr item2 => yjsItemEq item1 item2
  | YjsPtr.first, YjsPtr.first => true
  | YjsPtr.last, YjsPtr.last => true
  | _, _ => false
end

instance BEqYjsItem : BEq (YjsItem A) where
  beq := yjsItemEq _

instance BEqYjsPtr : BEq (@YjsPtr A) where
  beq := yjsPtrEq _

instance : Coe (YjsItem A) (YjsPtr A) where
  coe item := YjsPtr.itemPtr item

def YjsItem.origin {A : Type} : YjsItem A -> YjsPtr A
| YjsItem.item origin _  _ _ => origin

def YjsItem.rightOrigin {A : Type} : YjsItem A -> YjsPtr A
| YjsItem.item _ rightOrigin _ _ => rightOrigin

def YjsItem.id {A : Type} : YjsItem A -> ActorId
| YjsItem.item _ _ id _ => id

mutual
inductive YjsLt {A : Type} : YjsPtr A -> YjsPtr A -> Prop where
| ltFirst : forall item, YjsLt (YjsPtr.first) (YjsPtr.itemPtr item)
| ltLast : forall item, YjsLt (YjsPtr.itemPtr item) (YjsPtr.last)
| ltFirstLast: YjsLt (YjsPtr.first) (YjsPtr.last)
| ltL1 : forall l r id c, YjsLt l (YjsItem.item l r id c)
| ltR1 : forall l r id c, YjsLt (YjsItem.item l r id c) r
| ltL2 : forall l1 r1 id1 l2 r2 id2 (c1 c2 : A),
  YjsLeq (YjsItem.item l1 r1 id1 c1) l2
  -> YjsLt (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltR2 : forall l1 r1 id1 l2 r2 id2 (c1 c2 : A),
  YjsLeq r1 (YjsItem.item l2 r2 id2 c2)
  -> YjsLt (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltOriginDiff : forall l1 l2 r1 r2 id1 id2 c1 c2,
  YjsLt l2 l1
  -> YjsLt (YjsItem.item l1 r1 id1 c1) r2
  -> YjsLt l1 (YjsItem.item l2 r2 id2 c2)
  -> YjsLt (YjsItem.item l2 r2 id2 c2) r1
  -> YjsLt (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltOriginSame : forall l r1 r2 id1 id2 (c1 c2 : A),
  YjsLt (YjsItem.item l r1 id1 c1) r2
  -> YjsLt (YjsItem.item l r2 id2 c2) r1
  -> id1 < id2
  -> YjsLt (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)

inductive YjsLeq {A : Type} : YjsPtr A -> YjsPtr A -> Prop where
  | ltLeq x y : YjsLt x y -> YjsLeq x y
  | ltEq x y : x = y -> YjsLeq x y
end

namespace ex1
  open Nat
  def item1 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 2 2

  example : YjsLt item1 item2 :=
  by
    unfold item1 item2
    apply YjsLt.ltOriginSame <;> try rfl
    . apply YjsLt.ltLast
    . apply YjsLt.ltLast
    simp [ActorId]
end ex1

namespace ex2
  def item0 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 0 0
  def item1 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 : YjsPtr Nat := YjsItem.item YjsPtr.first item0 2 2

  example : YjsLt item2 item1 :=
  by
    apply YjsLt.ltR2
    . apply YjsLeq.ltLeq
      apply YjsLt.ltOriginSame
      apply YjsLt.ltLast
      apply YjsLt.ltLast
      simp [ActorId]
end ex2

mutual
lemma yjs_decidable1 (A : Type) : forall (x y : YjsPtr A), YjsLeq x y ∨ YjsLt y x :=
  fun (x : YjsPtr A) (y : YjsPtr A) =>
  match x with
  | YjsPtr.first =>
    match y with
    | YjsPtr.first => by
      left
      right
      eq_refl
    | YjsPtr.last => by
      left
      left
      apply YjsLt.ltFirstLast
    | YjsPtr.itemPtr item => by
      left
      left
      apply YjsLt.ltFirst
  | YjsPtr.last =>
    match y with
    | YjsPtr.first => by
      right
      apply YjsLt.ltFirstLast
    | YjsPtr.last => by
      left
      right
      eq_refl
    | YjsPtr.itemPtr item => by
      right
      apply YjsLt.ltLast
  | YjsPtr.itemPtr item =>
    match y with
    | YjsPtr.first => by
      right
      apply YjsLt.ltFirst
    | YjsPtr.last => by
      left
      apply YjsLeq.ltLeq
      apply YjsLt.ltLast
    | YjsPtr.itemPtr item' =>
      have h : item.size + item'.size < (YjsPtr.itemPtr item).size + (YjsPtr.itemPtr item').size := by
        simp!
        omega
      yjs_decidable2 (x := item) (y := item')
termination_by x y => x.size + y.size

lemma yjs_decidable2 A : forall (x y : YjsItem A), @YjsLeq A x y ∨ @YjsLt A y x :=
  fun (x y : YjsItem A) => by
  cases x with
  | item l1 r1 id1 c1 =>
    cases y with
    | item l2 r2 id2 c2 =>
      have h : (YjsPtr.itemPtr (YjsItem.item l1 r1 id1 c1)).size + l2.size <
        (YjsItem.item l1 r1 id1 c1).size + (YjsItem.item l2 r2 id2 c2).size := by
        simp!
        omega
      cases yjs_decidable1 _ (YjsItem.item l1 r1 id1 c1) l2 with
      | inl hlt =>
        left
        left
        apply YjsLt.ltL2
        assumption
      | inr hlt1 =>
        have h : r2.size + (YjsPtr.itemPtr (YjsItem.item l1 r1 id1 c1)).size <
          (YjsItem.item l1 r1 id1 c1).size + (YjsItem.item l2 r2 id2 c2).size := by
          simp!
          omega
        cases yjs_decidable1 _ r2 (YjsItem.item l1 r1 id1 c1) with
        | inl hlt2 =>
          right
          apply YjsLt.ltR2
          assumption
        | inr hlt2 =>
          have h : l1.size + (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2)).size <
            (YjsItem.item l1 r1 id1 c1).size + (YjsItem.item l2 r2 id2 c2).size := by
            simp!
            omega
          cases yjs_decidable1 _ (YjsItem.item l2 r2 id2 c2) l1 with
          | inl hlt3 =>
            right
            apply YjsLt.ltL2
            assumption
          | inr hlt3 =>
            have h : r1.size + (YjsPtr.itemPtr (YjsItem.item l2 r2 id2 c2)).size <
              (YjsItem.item l1 r1 id1 c1).size + (YjsItem.item l2 r2 id2 c2).size := by
              simp!
              omega
            cases yjs_decidable1 _ r1 (YjsItem.item l2 r2 id2 c2) with
            | inl hlt4 =>
              left
              apply YjsLeq.ltLeq
              apply YjsLt.ltR2
              assumption
            | inr hlt4 =>
              have h : l1.size + l2.size <
                (YjsItem.item l1 r1 id1 c1).size + (YjsItem.item l2 r2 id2 c2).size := by
                simp!
                omega
              cases yjs_decidable1 _ l1 l2 with
              | inl hlt5 =>
                cases hlt5 with
                | ltEq _ _ heq =>
                  rw [heq]
                  cases Nat.decLt id1 id2 with
                  | isTrue h =>
                    left
                    apply YjsLeq.ltLeq
                    apply YjsLt.ltOriginSame <;> try assumption
                    rw [<-heq] <;> assumption
                  | isFalse h =>
                    have h' : id1 = id2 ∨ id2 < id1 := by
                      unfold ActorId
                      omega
                    cases h' with
                    | inl heq =>
                      sorry -- id1 = id2なのでconcurrentにはなりえない
                    | inr hlt6 =>
                      right
                      apply YjsLt.ltOriginSame <;> try assumption
                      rw [<-heq]
                      assumption
                | ltLeq _ _ hlt6 =>
                  right
                  apply YjsLt.ltOriginDiff <;> assumption
              | inr hlt5 =>
                left
                apply YjsLeq.ltLeq
                apply YjsLt.ltOriginDiff <;> assumption
termination_by x y => x.size + y.size
end

lemma yjs_lt_invert (x y : YjsItem A) (x' y' : YjsPtr A) :
  x = x' -> y = y' -> @YjsLt A x' y' -> YjsLeq x (y.origin) ∨ YjsLeq (x.origin) (y.origin) := by
  intros hx hy hlt
  induction hlt
  . injection hx
  . injection hy
  . left
    right
    injection hy with hy
    rw [hx, hy]
    eq_refl
  . left
    left
    injection hx with hx
    rw [hx, <-hy]
    sorry -- item < item.rightOrigin.originが必要
  . left
    left
    injections hx hy
    rw [hx, hy]
    simp!
    assumption
  . injections hx hy
    rw [hx, hy]
    simp!



theorem order_is_strict_total: IsStrictTotalOrder _ (@YjsLt A) := by
  sorry
