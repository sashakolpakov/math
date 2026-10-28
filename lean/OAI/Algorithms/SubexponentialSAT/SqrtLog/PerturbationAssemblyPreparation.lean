import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramRun

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Source205 and full choice206 are preserved through beta and row traversal.
Target caches are paid, temporary, and restored before returning. -/
def prepareLow : Code := .seq PerturbationBetaProgram.betaCommand (.seq origin
  (.seq initializeTarget (.seq (scanRows coordinate) (.seq finishTarget (clear 220)))))

/-- Global selected-factor driver shares the leaf's fixed workspace. Inner
ports are relocated by340; the source generator may use through679. -/
abbrev OuterCode := Cmd 16 768

def innerPort (i : Fin 256) : Fin 768 := ⟨340 + i.val, by omega⟩

theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

def liftInner (code : Code) : OuterCode :=
  liftCommand code 0 0 id innerPort

/-- The lower source generator consumes the bare original ID on233. The
interpreter table key215 contains the same ID with its unary terminator. -/
def makeLiteralKey : Code := .seq (Subexp.TupleProgram.pushConst 215 0 false) (copy 233 215)

/-- High coordinates use the current branch constant; low coordinates invoke
actual source generation followed by the closed inner preparation command. -/
def literalPayload (source : OuterCode) : OuterCode :=
  .seq (liftInner (readFlag 234)) (.ite 15 (liftInner highConstant)
    (.seq source (liftInner prepareLow)))

def finishLiteral : Code := .seq entry (.seq (clear 215) (clear 205))

def literalIteration (source : OuterCode) : OuterCode :=
  .seq (liftInner makeLiteralKey) (.seq (literalPayload source) (liftInner finishLiteral))

def literalPorts : UnaryForPrograms.Ports 16 768 := ⟨573,0,1⟩

/-- The pop-before-body counter visits n-1,...,0. Since entry prepends, the
resulting raw lookup records are in original ascending variable order. -/
def prepareFactor (source : OuterCode) : OuterCode :=
  .seq (liftInner (copy 212 233))
    (.seq (UnaryForPrograms.forCmd literalPorts (literalIteration source))
      (liftInner (move 229 221)))

def prepareFactorProgram (source : OuterCode) := compiled (prepareFactor source) 556 561

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
