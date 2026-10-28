import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingFront
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmeticState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryGuard
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryProtected

namespace OAI.Algorithms

/-! A concrete preparation certificate is produced from the original query
masters. Each execution field is proved by invoking its fixed native program;
there is no setup-oracle or supplied prepared-cache hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes Subexp

structure Preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ) where
  lengths : Fin 8 → ℕ
  bankWords : Bank.Words
  front : Data
  frontSteps : ℕ
  frontExecution : Eval (LeafQueryFrontend.frontend k) frontSteps a front
  frontTime : frontSteps ≤ q.inputBudget k
  frontOutput : FrontState q k a front lengths bankWords
  firstWord : Word (packingProblem q k hg).r (packingProblem q k hg).Q
  remainingWords : List (Word (packingProblem q k hg).r (packingProblem q k hg).Q)
  alphabetOrder : (firstWord::remainingWords).map ReadPlan.encodeWord=
    AssignmentAlphabetSemantics.wordBytes (packingProblem q k hg).r (packingProblem q k hg).Q
  alphabetNodup : (firstWord::remainingWords).Nodup
  alphabetComplete : ∀z,z∈firstWord::remainingWords
  packed : Data
  packingSteps : ℕ
  packingExecution : Eval PackingCallerProgram.command packingSteps front packed
  packingTime : packingSteps+1 ≤ PackingCallerProgram.budget front (packingProblem q k hg) firstWord remainingWords
  packingBytes : packed.stacks=(PackingCallerProgram.result front (packingProblem q k hg) firstWord remainingWords).stacks
  packingFrame : ∀i : Fin 768,(i.val < 417 ∨ 481 ≤ i.val) →
    (i.val < 128 ∨ 142 ≤ i.val) → (i.val < 730 ∨ 744 ≤ i.val) → packed.stacks i=front.stacks i
  packingRegisters : ∀i : Fin 40,16 ≤ i.val → packed.regs i=front.regs i
  cutoff : packed.stacks 740=List.replicate (produce (q.input k)).R true
  arithmeticData : ArithmeticPreparation packed (Execute.guardedModel (q.input k) lengths)
    (ring_precision_pos (q.input k) lengths hg) (ring_degree_pos (q.input k) lengths hg)
    (W+q.inputBudget k+PackingCallerProgram.budget front (packingProblem q k hg) firstWord remainingWords)
    V L

namespace Preparation
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
  {hg : Guard (q.input k)} {W V L : ℕ}

abbrev out (p : Preparation q k a hg W V L) := p.arithmeticData.out

abbrev ringState (p : Preparation q k a hg W V L) := p.arithmeticData.ringState

abbrev modulus (p : Preparation q k a hg W V L) := p.arithmeticData.modulus

abbrev scalarCache (p : Preparation q k a hg W V L) := p.arithmeticData.scalarCache

abbrev half (p : Preparation q k a hg W V L) := p.arithmeticData.half

abbrev arithmeticSteps (p : Preparation q k a hg W V L) := p.arithmeticData.steps

abbrev arithmeticExecution (p : Preparation q k a hg W V L) := p.arithmeticData.execution

abbrev arithmeticTime (p : Preparation q k a hg W V L) := p.arithmeticData.time

abbrev arithmeticOutput (p : Preparation q k a hg W V L) := p.arithmeticData.output

abbrev denominatorInverse (p : Preparation q k a hg W V L) := p.arithmeticData.denominatorInverse

end Preparation
end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
