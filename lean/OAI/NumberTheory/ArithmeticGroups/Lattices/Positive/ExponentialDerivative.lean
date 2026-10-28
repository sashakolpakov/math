import OAI.NumberTheory.ArithmeticGroups.Lattices.LeftExponentialDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.UnipotentExponentialEquiv

/-! # Exponential Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! A global strict derivative formula for the exponential on the
positive derivation subspace. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.ExponentialDerivative.Construction.positiveDerivativeEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.ExponentialDerivative.Construction.positiveDerivativeEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.ExponentialDerivative.Construction.positiveDerivativeEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.positiveExpDifferential (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →L[ℝ] (L →L[ℝ] L) :=
  (Finite.ExponentialDerivative.Construction.finiteExponentialDerivative (Module.finrank ℝ L + 2) X.val).comp
    (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL

def KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferentialAmbient (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →L[ℝ] (L →L[ℝ] L) :=
  (LeftExponentialDerivative.Construction.leftExponentialDerivative (Module.finrank ℝ L + 2) X.val).comp
    (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL

theorem KillingSplit.Construction.KillingSplitWeightData.positive_exp_hasStrictFDerivAt (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    HasStrictFDerivAt (fun Y : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val => exp Y.val)
      (d.positiveExpDifferential X) X := by
  have he : (fun Y : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val => exp Y.val) =
      fun Y => Finite.ExponentialDerivative.Construction.finiteExponentialPolynomial (Module.finrank ℝ L + 2) Y.val := by
    funext Y
    exact NilpotentExponentialPolynomial.Construction.exp_eq_finite_sum_of_pow_eq_zero Y.val _ (pow_eq_zero_of_le (by omega)
      (NilpotentExponentialPolynomial.Construction.nilpotent_continuous_operator_pow_finrank Y.val (Positive.DerivationNilpotence.Construction.positiveBracketDerivations_isNilpotent B
        d.regularElement.val (d.le_symmetric d.regularElement.property).1 Y.val Y.property)))
  rw [he]
  exact (Finite.ExponentialDerivative.Construction.hasStrictFDerivAt_finiteExponentialPolynomial _ X.val).comp X
    (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL.hasStrictFDerivAt

theorem KillingSplit.Construction.KillingSplitWeightData.positive_left_exp_hasStrictFDerivAt (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    HasStrictFDerivAt
      (fun Y : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val => exp (-X.val) * exp Y.val)
      (d.positiveLeftDifferentialAmbient X) X := by
  exact (ContinuousLinearMap.mul ℝ (L →L[ℝ] L) (exp (-X.val))).hasStrictFDerivAt.comp X
    (d.positive_exp_hasStrictFDerivAt X)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
