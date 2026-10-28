import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarFromCountsPrimitives
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarNumerator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgramCell

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev binomial : Cmd 9 40 := .call (ProgramLinking.liftProgram LayoutBinomialProgram.finalProgram regs8 binomialPorts)
abbrev numerator : Cmd 9 40 := .call (ProgramLinking.liftProgram numeratorProgram id numeratorPorts)
abbrev command : Cmd 9 40 := .seq copies (.seq count (.seq binomial (.seq numerator cleanup)))
def program := compiled command 7 37

def binomialCost (h R W : ℕ) : ℕ :=
  12*R+400*(h+1)*(R+1)*(h+5)+110*(R+1)*(W+(h+1)+4)+32


def totalCost (A R d h W P : ℕ) : ℕ :=
  14*R+7*A+15+(3*d+4)+binomialCost h R W+
  (numeratorPrepareCost (R-d) A W P+numeratorFoldCost (R-d) W P+1)+4*(R*W)+6+1

def unsignedSaved (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (R : ℕ) (a : List Bool) : Saved :=
  ⟨Hwords.flatten,List.replicate (R*width.length) false,width,power,List.replicate R true,a⟩


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
