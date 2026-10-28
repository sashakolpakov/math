import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSubmoduleEquivalence
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FlowHilbertSymmetry
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.SplitConjugation

/-! # Action On Ambient Positive -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Every element of the intrinsic split subspace conjugates the
ambient positive operators into themselves. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.ActionOnAmbientPositive.Construction.ambientSplitEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.ActionOnAmbientPositive.Construction.ambientSplitEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.ActionOnAmbientPositive.Construction.ambientSplitEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance Split.ActionOnAmbientPositive.Construction.ambientSplit_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

theorem KillingSplit.Construction.KillingSplitWeightData.split_conjugation_preserves_ambient_positive
    (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) (X : L →L[ℝ] L)
    (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)) :
    exp A.val * X * exp (-A.val) ∈
      Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement) := by
  have h : exp ((-(-1 : ℝ)) • A.val) * X * exp ((-1 : ℝ) • A.val) ∈
      Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement) := by
    intro i j hij
    rw [Weight.ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate d.basis A.val (d.le_symmetric A.property).1
      (fun r => d.weight r A) (fun r => d.eigenvector r A), hX i j hij, mul_zero]
  simpa only [neg_neg, one_smul, neg_one_smul] using h

def KillingSplit.Construction.KillingSplitWeightData.ambientPositiveConjugation (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement) ≃L[ℝ]
      Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement) :=
  InvariantSubmoduleEquivalence.Construction.invariantSubmoduleEquiv (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv A.val).conjContinuousAlgEquiv.toContinuousLinearEquiv
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement))
    (fun X hX => d.split_conjugation_preserves_ambient_positive A X hX)
    (fun X hX => by
      change exp (-A.val) * X * exp A.val ∈ _
      simpa only [Submodule.coe_neg, neg_neg] using
        d.split_conjugation_preserves_ambient_positive (-A) X hX)

theorem KillingSplit.Construction.KillingSplitWeightData.ambientPositiveConjugation_val (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)) :
    (d.ambientPositiveConjugation A X).val = exp A.val * X.val * exp (-A.val) := rfl

theorem KillingSplit.Construction.KillingSplitWeightData.ambientPositiveConjugation_inner (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X Y : Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)) :
    inner ℝ (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates d.basis.toBasis (d.ambientPositiveConjugation A X).val)
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates d.basis.toBasis Y.val) =
    inner ℝ (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates d.basis.toBasis X.val)
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates d.basis.toBasis (d.ambientPositiveConjugation A Y).val) := by
  rw [d.ambientPositiveConjugation_val, d.ambientPositiveConjugation_val]
  simpa only [neg_neg, one_smul, neg_one_smul] using
    Split.FlowHilbertSymmetry.Construction.split_conjugation_euclidean_inner d.basis A.val (d.le_symmetric A.property).1
      (fun i => d.weight i A) (fun i => d.eigenvector i A) (-1) X.val Y.val

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
