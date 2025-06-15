import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder
import LeanYjs.ItemSet
import LeanYjs.ItemSetInvariant

def yjsLtConcurrent {A : Type} {P : ClosedPredicate A} (x y : YjsItem A) : Prop :=
  ∃ h1 h2 h3 h4,
    YjsLt P h1 x.origin y ∧
    YjsLt P h2 y x.rightOrigin ∧
    YjsLt P h3 y.origin x ∧
    YjsLt P h4 x y.rightOrigin
