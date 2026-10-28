import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryTransport
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Levi Oscillator -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator.CM.LinearCoordinates

/-! An invertible adelic matrix gives the actual continuous linear
coordinate change and a normalized unitary test-function operator. -/

open scoped Classical _root_.Matrix

variable {I : Type*} [Fintype I]

def coordinates (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun x := A.val.transpose *ᵥ x
  invFun x := (A⁻¹).val.transpose *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ _ _
  map_smul' c x := Matrix.mulVec_smul _ _ _
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact continuous_finsetSum Finset.univ (fun j _ => continuous_const.mul (continuous_apply j))
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact continuous_finsetSum Finset.univ (fun j _ => continuous_const.mul (continuous_apply j))

def operator (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  UnitaryTransport.CM.transport (coordinates A)

theorem operator_apply (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (operator A f).val x = (UnitaryTransport.CM.scalar (coordinates A) : ℂ) *
      f.val (A.val.transpose *ᵥ x) := rfl

theorem unitary (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (operator A f) (operator A h) =
      FiniteOscillator.CM.integralPairing f h := UnitaryTransport.CM.unitary (coordinates A) f h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator.CM.LinearCoordinates

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator.CM

/-! Exact Heisenberg covariance of the actual normalized finite linear
operator, giving the Levi factor inside the constructed oscillator group. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator.CM.LinearCoordinates
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {I : Type*} [Fintype I]

theorem coordinate_cancel (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    A.val.transpose *ᵥ ((A⁻¹).val.transpose *ᵥ q) = q :=
  (LinearCoordinates.coordinates A).apply_symm_apply q

theorem levi_phase (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A).val *ᵥ Sum.elim p q = Sum.elim (A.val *ᵥ p) ((A⁻¹).val.transpose *ᵥ q) := by
  change Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *ᵥ Sum.elim p q = _
  rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  rfl

theorem phase_identity (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    p ⬝ᵥ (A.val.transpose *ᵥ x - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q) =
      (A.val *ᵥ p) ⬝ᵥ (x - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • ((A⁻¹).val.transpose *ᵥ q)) := by
  have ht := Matrix.dotProduct_transpose_mulVec A.val p
    (x - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • ((A⁻¹).val.transpose *ᵥ q))
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, coordinate_cancel] at ht
  exact ht.trans (dotProduct_comm _ _)

theorem heisenberg_linear (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) (c : ℂ) :
    c * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f (A.val.transpose *ᵥ x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character (A.val *ᵥ p) ((A⁻¹).val.transpose *ᵥ q)
        (fun y => c * f (A.val.transpose *ᵥ y)) x := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg
  change c * (Constructed.AdelicCharacter.CM.Finite.character
    (p ⬝ᵥ (A.val.transpose *ᵥ x - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q)) *
      f (A.val.transpose *ᵥ x - q)) =
    Constructed.AdelicCharacter.CM.Finite.character
      ((A.val *ᵥ p) ⬝ᵥ (x - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • ((A⁻¹).val.transpose *ᵥ q))) *
        (c * f (A.val.transpose *ᵥ (x - (A⁻¹).val.transpose *ᵥ q)))
  rw [phase_identity, Matrix.mulVec_sub, coordinate_cancel]
  ring

theorem intertwines (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
      (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A) (LinearCoordinates.operator A) := by
  intro p q f h hh x
  rw [LinearCoordinates.operator_apply, hh, levi_phase, heisenberg_linear]
  rw [show (LinearCoordinates.operator A f).val =
    (fun y => (UnitaryTransport.CM.scalar (LinearCoordinates.coordinates A) : ℂ) * f.val (A.val.transpose *ᵥ y))
    from funext (LinearCoordinates.operator_apply A f)]
  rfl

def leviOscillator (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : FiniteOscillator.CM.Oscillator (I := I) :=
  ⟨(RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A, LinearCoordinates.operator A), LinearCoordinates.unitary A,
    FiniteOscillator.CM.graph_of_intertwines _ _ (intertwines A)⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator.CM

end

end OAI
