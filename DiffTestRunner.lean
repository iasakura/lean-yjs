import Lean.Data.Json
import Std.Data.HashMap

import LeanYjs.Item
import LeanYjs.Algorithm.YString
import LeanYjs.Algorithm.Integrate
import LeanYjs.Logger

open Lean
open Lean.Json
open Std
open LeanYjs

inductive NdjsonCommand where
  | insert (clientId index : Nat) (char : Char)
  | sync (src dst : Nat)
  deriving Repr

instance : Inhabited NdjsonCommand := ⟨NdjsonCommand.sync 0 0⟩

def parseChar (s : String) : Except String Char :=
  match s.toList with
  | [c] => Except.ok c
  | _ => Except.error "expected single-character string"

def decodeCommand (json : Json) : Except String NdjsonCommand := do
  let ty ← json.getObjVal? "type" >>= Json.getStr?
  match ty with
  | "insert" =>
    let clientId ← json.getObjVal? "clientId" >>= Json.getNat?
    let index ← json.getObjVal? "index" >>= Json.getNat?
    let ch ← json.getObjVal? "char" >>= Json.getStr? >>= parseChar
    return NdjsonCommand.insert clientId index ch
  | "sync" =>
    let src ← json.getObjVal? "from" >>= Json.getNat?
    let dst ← json.getObjVal? "to" >>= Json.getNat?
    return NdjsonCommand.sync src dst
  | other =>
    Except.error s!"unknown command type: {other}"

def renderIntegrateError : IntegrateError → String
  | .notFound => "integrate error: notFound"

abbrev ClientState := Std.HashMap Nat (YString × Nat)

def applyInsert (state : ClientState) (clientId index : Nat) (char : Char) : Except String ClientState :=
  let ⟨ current, clock ⟩ := state.getD clientId (YString.new, 0)
  let id := YjsId.mk clientId (clock + 1)
  match (YString.insert current index char).run id with
  | Except.ok ⟨ updated, nextId ⟩ =>
    Except.ok <| state.insert clientId ⟨ updated, nextId.clock ⟩
  | Except.error err =>
    Except.error (renderIntegrateError err)

def applySync (state : ClientState) (src dst : Nat) : Except String ClientState := do
  let ⟨ fromDoc, fromClock ⟩ := state.getD src (YString.new, 0)
  let ⟨ target, targetClock ⟩ := state.getD dst (YString.new, 0)
  let initial := target.contents
  let todo := fromDoc.contents.toList.filter fun item =>
    not (initial.any (fun existing => existing = item))

  let rec integrateLoop (dest : Array Item) (queue : List Item) (fuel : Nat) : Except String (Array Item) :=
    match fuel with
    | 0 => Except.error (renderIntegrateError IntegrateError.notFound)
    | Nat.succ fuel' =>
      match queue with
      | [] => pure dest
      | _ => do
        let process := fun (state : Array Item × List Item × Bool) (item : Item) => do
          let (d, remaining, progressed) := state
          if d.any (fun existing => decide (existing = item)) then
            pure (d, remaining, progressed)
          else
            match integrate item d with
            | Except.ok newDest => pure (newDest, remaining, true)
            | Except.error IntegrateError.notFound => pure (d, item :: remaining, progressed)

        let (dest', remaining, progressed) ← queue.foldlM process (dest, [], false)
        if remaining.isEmpty then
          pure dest'
        else if progressed then
          integrateLoop dest' remaining.reverse fuel'
        else
          Except.error (renderIntegrateError IntegrateError.notFound)

  let maxFuel := todo.length + 1
  let contents ← integrateLoop initial todo maxFuel
  let stateWithFrom := state.insert src ⟨ fromDoc, fromClock ⟩
  let updatedTarget : YString := { contents := contents }
  return stateWithFrom.insert dst ⟨ updatedTarget, targetClock ⟩

def applyCommand (state : ClientState) (cmd : NdjsonCommand) : Except String ClientState :=
  match cmd with
  | NdjsonCommand.insert clientId index ch => applyInsert state clientId index ch
  | NdjsonCommand.sync src dst => applySync state src dst

def runCommands (commands : Array NdjsonCommand) : Except String ClientState := do
  let init : ClientState := {}
  commands.foldlM applyCommand init

def runCommandsIO (commands : Array NdjsonCommand) : IO ClientState := do
  let (_, state) ← commands.foldlM
    (fun (acc : Nat × ClientState) cmd => do
      let (idx, st) := acc
      logDebug s!"Executing command {idx}: {reprStr cmd}"
      match applyCommand st cmd with
      | Except.ok newState =>
        pure (idx + 1, newState)
      | Except.error msg =>
        throw <| IO.userError msg)
    (0, {})
  pure state

def parseLine (line : String) : Except String NdjsonCommand := do
  let json ← Json.parse line
  decodeCommand json

def readCommands : IO (Array NdjsonCommand) := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let mut commands : Array NdjsonCommand := #[]
  for line in input.splitToList (fun c => c = '\n') do
    let trimmed := line.trim
    if !trimmed.isEmpty then
      match parseLine trimmed with
      | Except.ok cmd => commands := commands.push cmd
      | Except.error msg => throw <| IO.userError msg
  pure commands

def stateToJson (state : ClientState) : Json :=
  let pairs := state.toList.map fun (entry : Nat × (YString × Nat)) =>
    (toString entry.fst, Json.str (YString.toString entry.snd.fst))
  Json.mkObj pairs

def main : IO Unit := do
  configureFromEnv
  let commands ← readCommands
  logInfo s!"Received {commands.size} command(s)."
  let state ← runCommandsIO commands
  let output := stateToJson state
  IO.println output.compress
