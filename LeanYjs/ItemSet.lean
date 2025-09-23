import LeanYjs.Item
import LeanYjs.ClientId

import Mathlib.Data.Set.Basic

variable (A : Type) [BEq A]

def ItemSet := Set (YjsPtr A)

structure IsClosedItemSet {A} (P : YjsPtr A -> Prop) : Prop where
  baseFirst : P YjsPtr.first
  baseLast : P YjsPtr.last
  closedLeft : (∀ (o : YjsPtr A) r id c, P (YjsItem.item o r id c) -> P o)
  closedRight : (∀ o (r : YjsPtr A) id c, P (YjsItem.item o r id c) -> P r)

-- Proof sketch: for a closed item set, membership of an item implies membership of its
-- origin or right origin. Decompose the item into `YjsItem.item` and apply the existing
-- `closedLeft` or `closedRight` hypothesis, which gives the desired pointer membership.
-- Proof sketch: to rewrite hypotheses like `P (YjsItem.item o r id c)` into `P o` or `P r`,
-- expose the item constructor and reuse the closure fields directly, turning them into simp lemmas.
@[simp]
lemma IsClosedItemSet.closed_item_left {A} {P : YjsPtr A -> Prop}
    (hP : IsClosedItemSet P) {o r : YjsPtr A} {id : ClientId} {c : A} :
    P (YjsItem.item o r id c) -> P o := by
  simpa using hP.closedLeft o r id c

@[simp]
lemma IsClosedItemSet.closed_item_right {A} {P : YjsPtr A -> Prop}
    (hP : IsClosedItemSet P) {o r : YjsPtr A} {id : ClientId} {c : A} :
    P (YjsItem.item o r id c) -> P r := by
  simpa using hP.closedRight o r id c
@[simp]

lemma IsClosedItemSet.closed_origin {A} {P : YjsPtr A -> Prop}
    (hP : IsClosedItemSet P) {x : YjsItem A} :
    P x -> P x.origin := by
  cases x with
  | item origin rightOrigin id c =>
    simpa using hP.closedLeft origin rightOrigin id c

@[simp]
lemma IsClosedItemSet.closed_rightOrigin {A} {P : YjsPtr A -> Prop}
    (hP : IsClosedItemSet P) {x : YjsItem A} :
    P x -> P x.rightOrigin := by
  cases x with
  | item origin rightOrigin id c =>
    simpa using hP.closedRight origin rightOrigin id c

open Aesop

open Lean Elab Tactic Meta

attribute [aesop safe apply]
  IsClosedItemSet.closed_item_left
  IsClosedItemSet.closed_item_right
  IsClosedItemSet.closed_origin
  IsClosedItemSet.closed_rightOrigin

private def closeClosedLemmas : List Name :=
  [
    ``IsClosedItemSet.closed_item_left,
    ``IsClosedItemSet.closed_item_right,
    ``IsClosedItemSet.closed_origin,
    ``IsClosedItemSet.closed_rightOrigin
  ]

private def getClosedPred? (type : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars type
  let ty ← Meta.whnf ty
  if ty.isAppOf ``IsClosedItemSet then
    let args := ty.getAppArgs
    match args.back? with
    | some pred => return some pred
    | none => return none
  else
    return none

private def getPredTerm? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app f arg => some (f, arg)
  | _ => none

private def isDefEqExpr (a b : Expr) : MetaM Bool :=
  Meta.withNewMCtxDepth <| Meta.isExprDefEq a b

private partial def termSeen (seen : List Expr) (term : Expr) : MetaM Bool :=
  match seen with
  | [] => return false
  | t :: ts => do
      if ← isDefEqExpr t term then
        return true
      else
        termSeen ts term

private def applyCloser (rule : Name) (hP fact : Expr) : MetaM (Option (Expr × Expr)) :=
  try
    let proof ← instantiateMVars (← Meta.mkAppM rule #[hP, fact])
    let ty ← instantiateMVars (← Meta.inferType proof)
    match getPredTerm? ty with
    | some (_, term) => return some (proof, term)
    | none => return none
  catch _ =>
    return none

private partial def findClosedProof (hP pred targetTerm : Expr)
    (queue : List (Expr × Expr)) (seen : List Expr) : MetaM (Option Expr) :=
  match queue with
  | [] => return none
  | (proof, term) :: rest => do
      if ← isDefEqExpr term targetTerm then
        return some (← instantiateMVars proof)
      else
        let mut todo := rest
        let mut visited := seen
        for rule in closeClosedLemmas do
          match ← applyCloser rule hP proof with
          | some (newProof, newTerm) =>
              if ← termSeen visited newTerm then
                pure ()
              else
                visited := newTerm :: visited
                todo := todo ++ [(newProof, newTerm)]
          | none => pure ()
        findClosedProof hP pred targetTerm todo visited

private def collectClosedFacts (pred : Expr) : MetaM (List (Expr × Expr)) := do
  let mut facts := []
  let ctx ← getLCtx
  for decl in ctx do
    if !decl.isAuxDecl then
      let ty ← instantiateMVars decl.type
      match getPredTerm? ty with
      | some (p, term) =>
          if ← isDefEqExpr p pred then
            facts := (mkFVar decl.fvarId, term) :: facts
      | none => pure ()
  return facts

private def collectClosedWitnesses : MetaM (List (Expr × Expr)) := do
  let mut witnesses := []
  let ctx ← getLCtx
  for decl in ctx do
    if !decl.isAuxDecl then
      if let some pred ← getClosedPred? decl.type then
        let pred ← instantiateMVars pred
        witnesses := (mkFVar decl.fvarId, pred) :: witnesses
  return witnesses

-- Tactic sketch: `closeClosed` does not take arguments; it scans the context for
-- `IsClosedItemSet` witnesses, enumerates each compatible predicate, and searches within the
-- available `P _` facts by chaining the closure lemmas until the goal pointer is derived.

syntax (name := closeClosed) "closeClosed" : tactic

elab_rules : tactic
| `(tactic| closeClosed) => do
  Tactic.liftMetaTactic fun goalId => do
    goalId.withContext do
      let witnesses ← collectClosedWitnesses
      match witnesses with
      | [] => throwError "closeClosed: no IsClosedItemSet hypothesis in context"
      | _ =>
        let target ← instantiateMVars (← goalId.getType)
        match getPredTerm? target with
        | some (targetPred, targetTerm) =>
            let rec tryWitnesses : List (Expr × Expr) → MetaM (List MVarId)
            | [] => throwError "closeClosed: unable to derive required membership"
            | (hExpr, pred) :: rest => do
                if ← isDefEqExpr targetPred pred then
                  let facts ← collectClosedFacts pred
                  let proof? ← findClosedProof hExpr pred targetTerm facts (facts.map Prod.snd)
                  match proof? with
                  | some proof =>
                      goalId.assign (← instantiateMVars proof)
                      pure []
                  | none => tryWitnesses rest
                else
                  tryWitnesses rest
            tryWitnesses witnesses
        | none => throwError "closeClosed: goal is not a predicate application"

theorem IsClosedItemSet.eq_set {A} (P Q : YjsPtr A -> Prop) :
  IsClosedItemSet P ->
  (∀ x, P x ↔ Q x) ->
  IsClosedItemSet Q := by
  intro hP hPQ
  constructor
  . rw [<-hPQ]
    apply hP.baseFirst
  . rw [<-hPQ]
    apply hP.baseLast
  . intros o r id c hp
    rw [<-hPQ] at *
    apply hP.closedLeft <;> assumption
  . intros o r id c hp
    rw [<-hPQ] at *
    apply hP.closedRight <;> assumption
