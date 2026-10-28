import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.InnerDerivationBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisTrace
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant

/-! # Derivation Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The split action on positive derivations has trace equal to the
positive-weight sum and exponential determinant equal to its exponential. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.DerivationTrace.Construction.positiveTraceEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.DerivationTrace.Construction.positiveTraceEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.DerivationTrace.Construction.positiveTraceEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

local instance Positive.DerivationTrace.Construction.positiveTraceSubspace_normed (d : KillingSplit.Construction.KillingSplitWeightData B) :
    NormedAddCommGroup (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
local instance Positive.DerivationTrace.Construction.positiveTraceSubspace_space (d : KillingSplit.Construction.KillingSplitWeightData B) :
    NormedSpace ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
local instance Positive.DerivationTrace.Construction.positiveTraceSubspace_finite (d : KillingSplit.Construction.KillingSplitWeightData B) :
    FiniteDimensional ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.positiveAction (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →ₗ[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation A.val).toLinearMap.restrict (fun X hX =>
    DerivationSpectralDecomposition.Construction.centralizing_derivation_commutator_positive B d.regularElement.val A.val X
      (d.le_symmetric A.property).2
      (d.commute d.regularElement.val d.regularElement.property A.val A.property) hX)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveAction_eigenbasis
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (A : d.subspace) (i : d.PositiveIndex) :
    d.positiveAction A (d.positiveDerivationBasis hB hK i) =
      d.weight i.val A • d.positiveDerivationBasis hB hK i := by
  apply Subtype.ext
  change A.val * (d.positiveDerivationBasis hB hK i).val -
    (d.positiveDerivationBasis hB hK i).val * A.val =
      d.weight i.val A • (d.positiveDerivationBasis hB hK i).val
  rw [d.positiveDerivationBasis_val hB hK i,
    FaithfulDerivationCommutator.Construction.derivation_commutator_inner_operator B A.val (d.le_symmetric A.property).2,
    d.eigenvector i.val A, map_smul]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveAction_trace
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (A : d.subspace) :
    LinearMap.trace ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) (d.positiveAction A) =
      d.positiveTrace A := by
  rw [EigenbasisTrace.Construction.linear_trace_eq_sum_eigenvalues (d.positiveDerivationBasis hB hK) (d.positiveAction A)
    (fun i => d.weight i.val A) (d.positiveAction_eigenbasis hB hK A)]
  exact (LinearMap.sum_apply _ _ _).symm

theorem KillingSplit.Construction.KillingSplitWeightData.positiveAction_exp_det
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (A : d.subspace) :
    LinearMap.det (NormedSpace.exp (d.positiveAction A).toContinuousLinearMap).toLinearMap =
      Real.exp (d.positiveTrace A) := by
  rw [ContinuousOperatorExponentialDeterminant.Construction.continuousOperator_exp_det, Real.exp_eq_exp_ℝ]
  congr 1
  exact d.positiveAction_trace hB hK A

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
