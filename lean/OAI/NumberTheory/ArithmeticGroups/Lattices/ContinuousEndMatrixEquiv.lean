import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Group.Units

/-! # Continuous End Matrix Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv.Construction

noncomputable section

/-! Continuous algebra and unit-group equivalences between finite
endomorphisms and their matrices in a chosen basis. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuousEndMatrix_bijective {m : ℕ} (b : Module.Basis (Fin m) ℝ L) :
    Function.Bijective (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b) := by
  constructor
  · intro A C h
    have he := (LinearMap.toMatrix b b).injective h
    ext x
    exact DFunLike.congr_fun he x
  · intro M
    refine ⟨(Matrix.toLin b b M).toContinuousLinearMap, ?_⟩
    change LinearMap.toMatrix b b (Matrix.toLin b b M) = M
    exact (LinearMap.toMatrix b b).apply_symm_apply M

def continuousEndMatrixAlgEquiv {m : ℕ} (b : Module.Basis (Fin m) ℝ L) :
    (L →L[ℝ] L) ≃A[ℝ] Matrix (Fin m) (Fin m) ℝ where
  __ := AlgEquiv.ofBijective (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b) (continuousEndMatrix_bijective b)
  continuous_toFun := ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix_continuous b
  continuous_invFun :=
    (AlgEquiv.ofBijective (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b) (continuousEndMatrix_bijective b)).symm.toLinearMap.continuous_of_finiteDimensional

theorem continuousEndMatrixAlgEquiv_apply {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (X : L →L[ℝ] L) :
    continuousEndMatrixAlgEquiv b X = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b X := rfl

def continuousEndMatrixUnitsEquiv {m : ℕ} (b : Module.Basis (Fin m) ℝ L) :
    (L →L[ℝ] L)ˣ ≃ₜ* (Matrix (Fin m) (Fin m) ℝ)ˣ :=
  Units.mapContinuousMulEquiv {
    toMulEquiv := (continuousEndMatrixAlgEquiv b).toAlgEquiv.toMulEquiv
    continuous_toFun := (continuousEndMatrixAlgEquiv b).continuous
    continuous_invFun := (continuousEndMatrixAlgEquiv b).symm.continuous }

theorem continuousEndMatrixUnitsEquiv_val {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    ((continuousEndMatrixUnitsEquiv b g) : Matrix (Fin m) (Fin m) ℝ) = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b (g : L →L[ℝ] L) := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv.Construction
