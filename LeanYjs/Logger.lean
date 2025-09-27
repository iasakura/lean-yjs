namespace LeanYjs

inductive LogLevel
  | error
  | warn
  | info
  | debug
  deriving DecidableEq, Repr

namespace LogLevel

@[simp] def priority : LogLevel → Nat
  | error => 0
  | warn  => 1
  | info  => 2
  | debug => 3

@[simp] def toString : LogLevel → String
  | error => "error"
  | warn  => "warn"
  | info  => "info"
  | debug => "debug"

partial def parse? (value : String) : Option LogLevel :=
  match value.trim.toLower with
  | "error" => some LogLevel.error
  | "warn"  => some LogLevel.warn
  | "warning" => some LogLevel.warn
  | "info"  => some LogLevel.info
  | "debug" => some LogLevel.debug
  | _ => none

end LogLevel

@[inline] def defaultLevel : LogLevel := .info

abbrev LoggerState := IO.Ref LogLevel

instance : Inhabited LogLevel := ⟨defaultLevel⟩

initialize logLevelRef : LoggerState ← IO.mkRef defaultLevel

@[inline] def setLevel (level : LogLevel) : IO Unit :=
  logLevelRef.set level

@[inline] def getLevel : IO LogLevel :=
  logLevelRef.get

@[inline] def configureFromEnv (envVar : String := "LEAN_YJS_LOG") : IO Unit := do
  let some value ← IO.getEnv envVar | pure ()
  match LogLevel.parse? value with
  | some level => setLevel level
  | none => pure ()

@[inline] def shouldLog (level : LogLevel) : IO Bool := do
  let current ← getLevel
  pure $ level.priority ≤ current.priority

@[inline] def log (level : LogLevel) (message : String) : IO Unit := do
  let log? ← shouldLog level
  if log? then
    IO.eprintln s!"[{level.toString}] {message}"

@[inline] def logDebug (message : String) : IO Unit :=
  log .debug message

@[inline] def logInfo (message : String) : IO Unit :=
  log .info message

@[inline] def logWarn (message : String) : IO Unit :=
  log .warn message

@[inline] def logError (message : String) : IO Unit :=
  log .error message

end LeanYjs
