import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorMachine
import OAI.Algorithms.SubexponentialSAT.SubexpCRTWeightedMachine
import OAI.Algorithms.SubexponentialSAT.SubexpHornerMachine
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterControl
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterFinish
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCofactor
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterHorner
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterNeg
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterAccumulate

namespace OAI.Algorithms

/-! Concrete finite control for scalar Hermite reconstruction at zero.

This module fixes the actual service calls and storage layout. The complete
execution theorem is still an integration obligation: in particular, the
local-correction producer must supply its full preserved-state theorem.
No execution bound or correctness theorem for this outer program is assumed.

Inputs: full node array 256; matching constant-first jet arrays 265; unary D
243; modulus 5/194, base width 10/202, reduction 201; constants 206/207/211.
Output: one flat quartet at 261. All scalar services are concrete programs.
Persistent outer state occupies 256 and above, outside the local producer.
-/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def localCorrection : Code :=
  .call (ProgramLinking.liftProgram SubexpLocalCRTProgram.program id localPorts)

/-- The two copies into 227 produce remaining ++ processed. The current
node has already been removed from remaining and has not yet been processed. -/
def cofactor : Code :=
  SubexpCRTOuterCofactor.command

def negativePoint : Code :=
  SubexpCRTOuterNeg.command

def evaluateCorrection : Code :=
  SubexpCRTOuterHorner.command

def accumulate : Code :=
  SubexpCRTOuterAccumulate.command

def evaluateNode : Code :=
  localCorrection ;; cofactor ;; negativePoint ;; evaluateCorrection ;; accumulate

def iteration : Code := loadCurrent ;; evaluateNode ;; advance

/-- No input parameter occurs in the control table; all loops inspect stacks. -/
def command : Code :=
  controller evaluateNode

abbrev program : Program 16 320 (size command + 1) := compiled command 256 261

/-- The physical remaining/processed concatenation has the product of exactly
the other positions. This argument does not cancel or invert a node value. -/
theorem excluded_product {C R : Type*} [CommMonoid R] (f : C → R)
    (processed remaining : List C) (current : C) :
    (((processed.reverse ++ current :: remaining).eraseIdx processed.length).map f).prod =
      ((remaining ++ processed).map f).prod := by
  rw [List.eraseIdx_append_of_length_le (by simp)]
  simp [List.map_reverse, List.prod_reverse, mul_comm]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
