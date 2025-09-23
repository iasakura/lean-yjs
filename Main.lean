import Lean.Data.Json
import Std.Data.HashMap

import LeanYjs.Item
import LeanYjs.YString
import LeanYjs.Integrate

open Lean
open Lean.Json
open Std

inductive NdjsonCommand where
  | insert (clientId index : Nat) (char : Char)
  | sync (src dst : Nat)
  deriving Repr

instance : Inhabited NdjsonCommand := ⟨NdjsonCommand.sync 0 0⟩

def parseChar (s : String) : Except String Char :=
  match s.data with
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
  | .outOfBounds i size => s!"integrate error: outOfBounds {i} (size={size})"

abbrev ClientState := Std.HashMap Nat YString

def applyInsert (state : ClientState) (clientId index : Nat) (char : Char) : Except String ClientState :=
  let current := state.getD clientId YString.new
  match (YString.insert current index char).run clientId with
  | Except.ok updated =>
    Except.ok <| state.insert clientId updated
  | Except.error err =>
    Except.error (renderIntegrateError err)

def applySync (state : ClientState) (src dst : Nat) : Except String ClientState := do
  let _ : DecidableEq Item := @instDecidableEqYjsItem _ instDecidableEqChar
  let fromDoc := state.getD src YString.new
  let target := state.getD dst YString.new
  let contents ← fromDoc.contents.foldlM (m := Except String) (fun acc item =>
    if acc.any (fun existing => decide (existing = item)) then
      pure acc
    else
      match integrate item acc with
      | Except.ok newAcc => pure newAcc
      | Except.error err => Except.error (renderIntegrateError err)
  ) target.contents
  return state.insert dst { contents := contents }

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
      IO.eprintln s!"Executing command {idx}: {reprStr cmd}"
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
  for line in input.split (fun c => c = '\n') do
    let trimmed := line.trim
    if !trimmed.isEmpty then
      match parseLine trimmed with
      | Except.ok cmd => commands := commands.push cmd
      | Except.error msg => throw <| IO.userError msg
  pure commands

def stateToJson (state : ClientState) : Json :=
  let pairs := state.toList.map fun (entry : Nat × YString) =>
    (toString entry.fst, Json.str (YString.toString entry.snd))
  Json.mkObj pairs

def main : IO Unit := do
  let commands ← readCommands
  IO.eprintln s!"Received {commands.size} command(s)."
  let state ← runCommandsIO commands
  let output := stateToJson state
  IO.println output.compress
