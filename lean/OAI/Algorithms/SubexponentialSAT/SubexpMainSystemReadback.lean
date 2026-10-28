import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTSelected

namespace OAI.Algorithms

/-! Physical selected-CRT inputs for a factor system in its actual emitted
order. The factor index type is retained rather than implicitly changed. -/

namespace SubexponentialSAT.SubexpMainSystemReadback

open SubexpMainProgram SubexpLayoutSpec SubexpLiftRing SubexpQuarticRing

variable {er es D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F : Type*} [Fintype F] [DecidableEq F]

local notation "N" => Fintype.card (Fin D)

structure Readback (S : Factor.System (Fin D) F (ZMod p))
    {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p) S.toPattern c)
    (alloc : SubexpMainCRT.Allocation es) (a : MainState er es) where
  modulus : SubexpPreparedQuartic.Modulus p (N + 1)
  reduction : SubexpCRTSelectedInput.Coefficient p N
  one : SubexpCRTSelectedInput.Coefficient p N
  minusOne : Word (baseWidth p (N + 1))
  width : List Bool
  exponent : List Bool
  nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p N
  jets : Fin c.Q → SubexpCRTSelectedInput.Jet p N
  width_length : width.length = baseWidth p (N + 1)
  reduction_value : reduction.map (wordValue p (N + 1)) =
    reductionData (QuarticSearch.liftedCoefficients p (N + 1))
  one_value : SubexpCRTSelectedInput.decode p N one = 1
  minusOne_value : wordValue p (N + 1) minusOne = -1
  exponent_value : BinaryArithmetic.toNat exponent = p ^ 4 - 2
  node_values : ∀ i, SubexpCRTSelectedInput.decode p N (nodes i) =
    SubexpCRTAtZero.selectedNode S layout i
  jet_values : ∀ i, SubexpCRTSelectedInput.denote p N (jets i) =
    SubexpCRTSelectedInput.selectedJet S layout i
  modulus_word : a.stacks (persistent es 12) = modulus.bits
  width_word : a.stacks (persistent es 13) = width
  reduction_word : a.stacks (persistent es 14) = SubexpFlatAdd.encode reduction
  exponent_word : a.stacks (persistent es 29) = exponent
  one_word : a.stacks (persistent es 30) = SubexpFlatAdd.encode one
  minusOne_word : a.stacks (persistent es 31) = minusOne.val
  dimension_word : CounterPrograms.value (a.stacks (persistent es 19)) = N
  node_words : a.stacks (SubexpMainCRT.ordinary alloc 256) =
    (List.finRange c.Q).flatMap (fun i => SubexpFlatAdd.encode (nodes i))
  jet_words : a.stacks (SubexpMainCRT.ordinary alloc 265) =
    (List.finRange c.Q).flatMap
      (fun i => SubexpPolynomialPowerProgram.encode p (N + 1) (jets i))

def Readback.bound {S : Factor.System (Fin D) F (ZMod p)}
    {c : Parameters p k Δ r tau}
    {layout : Layout (E := SubexpActualRing.E p) S.toPattern c}
    {alloc : SubexpMainCRT.Allocation es} {a : MainState er es}
    (input : Readback S layout alloc a) : ℕ :=
  SubexpMainCRTSelected.runtimeBound (p := p) (V := Fin D) alloc a c.Q input.exponent

end SubexponentialSAT.SubexpMainSystemReadback

end OAI.Algorithms
