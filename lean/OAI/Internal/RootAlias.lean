module

public meta import Mathlib.Util.AliasIn

public meta section

open Lean Elab Command Meta

/-- Collect root parser aliases for declarations generated in the current file.
This includes declarations produced by attributes such as `reassoc` and `simps`. -/
private def collectOAIRootAliases (env : Environment) : BaseIO (Array (Name × Name)) := do
  let constants ← env.getLocalConstantInfos
  let mut aliases : Array (Name × Name) := #[]
  for constant in constants do
    match constant.name.components with
    | `OAI :: rest@(_ :: _) =>
      aliases := aliases.push (.fromComponents rest, constant.name)
    | _ => pure ()
  return aliases

private def addOAIRootAliases : CoreM Unit := do
  let aliases ← collectOAIRootAliases (← getEnv)
  modifyEnv fun env => aliases.foldl (fun env (target, source) =>
    addAlias env target source) env

/-- Add aliases for any declarations generated after the last named declaration. -/
elab "oai_root_alias_generated" : command => do
  liftCoreM addOAIRootAliases

initialize registerBuiltinAttribute {
    name := `oai_root_alias
    descr := "create a transparent root parser alias for an OAI declaration"
    applicationTime := .afterCompilation
    add := fun
    | src, _, kind => do
      unless kind == .global do
        throwError "The `oai_root_alias` attribute cannot be {kind}."
      if (← toModifiers src).visibility.isPrivate then
        return
      addOAIRootAliases
    }

end
