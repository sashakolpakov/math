import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TranslatedTangent
import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialPolynomial

/-! # Derivative Factorization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! The translated exponential differential is a linear isomorphism
with determinant one on the positive derivation subspace. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.DerivativeFactorization.Construction.jacobianEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.DerivativeFactorization.Construction.jacobianEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.DerivativeFactorization.Construction.jacobianEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferential (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →L[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  (d.positiveLeftDifferentialAmbient X).codRestrict _ (d.positiveLeftDifferentialAmbient_mem X)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferential_unipotent (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    IsNilpotent ((d.positiveLeftDifferential X).toLinearMap - 1) := by
  have hp : ∀ Z ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val,
      LeftExponentialDerivative.Construction.leftExponentialDerivative (Module.finrank ℝ L + 2) X.val Z ∈
        DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val := by
    intro Z hZ
    exact d.positiveLeftDifferentialAmbient_mem X ⟨Z, hZ⟩
  exact NilpotentExponentialPolynomial.Construction.restrict_unipotent_linear_map
    (LeftExponentialDerivative.Construction.leftExponentialDerivative (Module.finrank ℝ L + 2) X.val).toLinearMap _ hp
    (LeftExponentialDerivative.Construction.leftExponentialDerivative_unipotent (Module.finrank ℝ L) X.val
      (Positive.DerivationNilpotence.Construction.positiveBracketDerivations_isNilpotent B d.regularElement.val
        (d.le_symmetric d.regularElement.property).1 X.val X.property))

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferential_det (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (d.positiveLeftDifferential X).toLinearMap.det = 1 :=
  NilpotentExponentialPolynomial.Construction.linear_det_eq_one_of_unipotent _ (d.positiveLeftDifferential_unipotent X)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferential_bijective (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    Function.Bijective (d.positiveLeftDifferential X) := by
  have hu : IsUnit (d.positiveLeftDifferential X).toLinearMap := by
    apply (LinearMap.isUnit_iff_isUnit_det _).mpr
    rw [d.positiveLeftDifferential_det]
    exact isUnit_one
  have hinj := LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

def KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferentialEquiv (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≃L[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  (LinearEquiv.ofBijective (d.positiveLeftDifferential X).toLinearMap
    (d.positiveLeftDifferential_bijective X)).toContinuousLinearEquiv

end

/-! The exponential differential factors into left translation,
subspace inclusion, and its determinant-one tangent isomorphism. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.DerivativeFactorization.Construction.derivativeFactor_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance Positive.DerivativeFactorization.Construction.derivativeFactor_rat : NormedAlgebra ℚ (L →L[ℝ] L) :=
  NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveExpDifferential_factor (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.positiveExpDifferential X =
      (ContinuousLinearMap.mul ℝ (L →L[ℝ] L) (exp X.val)).comp
        ((DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL.comp
          (d.positiveLeftDifferentialEquiv X).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro Y
  change Finite.ExponentialDerivative.Construction.finiteExponentialDerivative (Module.finrank ℝ L + 2) X.val Y.val =
    exp X.val * (exp (-X.val) * Finite.ExponentialDerivative.Construction.finiteExponentialDerivative (Module.finrank ℝ L + 2) X.val Y.val)
  rw [← mul_assoc, ← exp_add_of_commute (Commute.refl X.val).neg_right,
    add_neg_cancel, exp_zero, one_mul]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferentialEquiv_det (d : KillingSplit.Construction.KillingSplitWeightData B)
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (d.positiveLeftDifferentialEquiv X).toLinearEquiv.toLinearMap.det = 1 :=
  d.positiveLeftDifferential_det X

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
