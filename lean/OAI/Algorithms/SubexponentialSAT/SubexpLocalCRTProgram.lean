import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialPowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalConstantProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAddCall
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerProgram
import OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorCall
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialConstructor
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl
import OAI.Algorithms.SubexponentialSAT.SubexpLocalLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialHornerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalSeedProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalGeometricProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalInitializedScan
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTFrames

namespace OAI.Algorithms

/-! The fixed instruction controller for one local CRT correction.

This file defines concrete control. The companion `SubexpLocalCRTExecution`
module contains the full execution/correctness statement and explicit runtime
bound; the component modules provide its arithmetic, array, and loop traces.

Persistent inputs: current node 213, all nodes 214, unary node index 216,
jet 225, unary dimension 243. Constants: Fermat exponent 206, quartic one
207, scalar minus-one 211. Native arithmetic metadata occupy 5/194
(modulus), 10/202 (base width), 104 (zero coefficient / coefficient width),
and 201 (quartic reduction). This is the counting specialization μ=D+1:
the actual geometric counter has 2D+1 tokens. Output 244 is the sole changed stack at the
intended endpoint; temporary arrays are explicitly cleared.
-/

namespace SubexponentialSAT.SubexpLocalCRTProgram

open BitProgram StructuredCalls SubexpConvolutionControl

def registers : Fin 8 ↪ Fin 16 := SubexpLocalLinearFactorProgram.registers
def addPorts : Fin 20 ↪ Fin 256 := SubexpLocalLinearFactorProgram.addPorts
def lowerPorts : Fin 128 ↪ Fin 256 := ⟨Fin.castAdd 128, Fin.castAdd_injective 128 128⟩
def powerPorts : Fin 83 ↪ Fin 256 :=
  ⟨fun i => ⟨128 + i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩

def negatePorts : Fin 24 ↪ Fin 256 :=
  SubexpLocalLinearFactorProgram.negatePorts

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def move (src dst : Fin 256) : Code :=
  SubexpPolynomialConstructor.move src dst

def clearMany : List (Fin 256) → Code := SubexpLocalCRTSetup.clearMany

def token (dst : Fin 256) : Code :=
  SubexpLocalCRTSetup.token dst

def constructAtInputs (dst : Fin 256) : Code :=
  SubexpPolynomialConstructor.constructAtInputs dst

def construct (low high dst : Fin 256) : Code :=
  SubexpPolynomialConstructor.construct low high dst

def scalarNegate : Code := SubexpLocalLinearFactorProgram.scalarNegate
def scalarAdd : Code := SubexpLocalLinearFactorProgram.scalarAdd
def scalarPower : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticPowerProgram.program registers powerPorts)

def addArrays : Code :=
  SubexpPolynomialAddService.command

def multiplyIntoAccumulator : Code :=
  SubexpPolynomialHornerProgram.multiply

def addOneIntoAccumulator : Code :=
  SubexpPolynomialHornerProgram.addOne

/-- Build one shifted linear factor and multiply it into Pt exactly D times. -/
def includeNode : Code :=
  SubexpLocalProductProgram.command

/-- The copied index loses one token before each earlier node. The pending
marker skips exactly the indexed node and is then permanently cleared. -/
def chooseNode : Code :=
  SubexpNodeScanControl.choose includeNode

def nodeStep : Code :=
  SubexpNodeScanControl.step includeNode

def nodeLoop : Code :=
  SubexpNodeScanControl.command includeNode

def initializeCaches : Code :=
  SubexpLocalCRTSetup.initializeCaches

/-- Power in the lifted ring using the residue field's Fermat exponent.
This seed feeds the longer polynomial geometric loop. -/
def prepareSeed : Code :=
  SubexpLocalSeedProgram.command

def prepareDefect : Code :=
  SubexpLocalGeometricProgram.prepareDefect

def hornerStep : Code :=
  SubexpPolynomialHornerProgram.iteration

def geometricInverse : Code :=
  SubexpLocalGeometricProgram.inverse

def cleanup : Code :=
  SubexpLocalCRTFrames.command

def positiveDimension : Code :=
  SubexpLocalInitializedScan.command ;; prepareSeed ;; SubexpLocalGeometricProgram.command ;; cleanup

/-- The finite table is independent of p, Q, D, μ, and every coefficient.
The zero-dimensional branch returns the initially empty output. -/
def command : Code := test 243 15 ;; .ite 15 positiveDimension (.base .skip)
def program := compiled command 225 244

end SubexponentialSAT.SubexpLocalCRTProgram

end OAI.Algorithms
