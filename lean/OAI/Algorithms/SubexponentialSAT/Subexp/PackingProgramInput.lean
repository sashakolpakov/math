import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingPlumbing
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalTypeProgram

namespace OAI.Algorithms

/-! Input preparation stages of the fixed physical packing controller. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

abbrev Op := PackingPlumbing.Op

structure Input where
  assignment : List Bool
  width : List Bool
  dimension : List Bool
  degree : List Bool
  scopes : List Bool
  alphabet : List Bool

def inputState (input : Input) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i =>
    if i = 40 then input.assignment else
    if i = 41 then input.width else
    if i = 42 then input.dimension else
    if i = 43 then input.degree else
    if i = 44 then input.scopes else
    if i = 45 then input.alphabet else []⟩

def frontendOutputState (input : Input) (labelBytes typeBytes : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 26 then labelBytes else if i = 27 then typeBytes
    else (inputState input regs).stacks i⟩

def outputState (input : Input) (blocks leftovers metadata addresses storage inverse : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 30 then blocks else if i = 31 then leftovers else
    if i = 32 then metadata else if i = 33 then addresses else
    if i = 34 then storage else if i = 35 then inverse else (inputState input regs).stacks i⟩

def plansSetup : List Op := [.copy 44 16 39, .copy 42 17 39, .copy 43 18 39]
def plansSave : List Op := PackingPlumbing.move 24 25 39 ++
  [.clear 16, .clear 17, .clear 18, .clear 20]
def labelsSetup : List Op := [.copy 40 0 39, .copy 41 3 39] ++ PackingPlumbing.move 25 10 39
def labelsSave : List Op := PackingPlumbing.move 13 26 39 ++ [.clear 0, .clear 3, .clear 12]
def typesSetup : List Op := [.copy 45 1 39, .copy 43 8 39]
def typesSave : List Op := PackingPlumbing.move 0 27 39 ++ [.clear 1, .clear 5]
abbrev plansCall : Cmd 16 48 := lowCall SubexpPlanAlphabetBase.program (by decide) (by decide)
abbrev labelsCall : Cmd 16 48 := lowCall PackingVertexLabels.program (by decide) (by decide)
abbrev typesCall : Cmd 16 48 := lowCall UniversalTypeProgram.program (by decide) (by decide)

abbrev plans : Cmd 16 48 := .seq (PackingPlumbing.command plansSetup)
  (.seq plansCall (PackingPlumbing.command plansSave))
abbrev labels : Cmd 16 48 := .seq (PackingPlumbing.command labelsSetup)
  (.seq labelsCall (PackingPlumbing.command labelsSave))
abbrev types : Cmd 16 48 := .seq (PackingPlumbing.command typesSetup)
  (.seq typesCall (PackingPlumbing.command typesSave))

abbrev frontend : Cmd 16 48 := sequence [plans, labels, types]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
