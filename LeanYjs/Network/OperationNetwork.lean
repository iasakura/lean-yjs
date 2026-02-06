import LeanYjs.Network.CausalNetwork

open NetworkModels

variable {A I : Type}  [DecidableEq A] [Operation A] [DecidableEq I] [Message A I]

def interpOps (items : List A) (init : Operation.State A) : Except (Operation.Error A) (Operation.State A) :=
  effect_list items init

def interpHistory (history : List (Event A)) (init : Operation.State A) : Except (Operation.Error A) (Operation.State A) :=
  interpOps (history.filterMap (fun ev => match ev with | Event.Deliver it => some it | _ => none)) init

class ValidMessage A [Operation A] where
  isValidMessage : Operation.State A → A → Prop

structure OperationNetwork A {I} [DecidableEq A] [DecidableEq I] [Operation A] [Message A I] [ValidMessage A] extends CausalNetwork A where
  broadcast_only_valid_messages :
    ∀i, pre ++ [Event.Broadcast e] ++ post = histories i →
    ∃state,
      interpHistory pre Operation.init = Except.ok state ∧
      ValidMessage.isValidMessage state e
