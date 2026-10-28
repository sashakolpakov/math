import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints

/-! # Coefficient Point Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientPointDerivations

noncomputable section

/-! The derivations at a complex coefficient point agree linearly
with the established native affine point-derivation space, retaining
the same second coefficients of the actual dual-number lift. -/

open scoped _root_.Manifold ContDiff

variable (B : Type) [CommRing B] [Algebra ℂ B] [Algebra B ℂ] [IsScalarTower ℂ B ℂ]

def coefficientPointDerivationsEquiv : Derivation ℂ B ℂ ≃ₗ[ℂ]
    PointDerivations.pointDerivations (IsScalarTower.toAlgHom ℂ B ℂ) where
  toFun d := ⟨d.toLinearMap, d.map_one_eq_zero, fun a b => by
    change d (a * b) = (IsScalarTower.toAlgHom ℂ B ℂ) a * d b + (IsScalarTower.toAlgHom ℂ B ℂ) b * d a
    rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply]
    simpa only [Algebra.smul_def] using d.leibniz a b⟩
  invFun d := {
    toLinearMap := d.val
    map_one_eq_zero' := d.property.1
    leibniz' := fun a b => by simpa only [Algebra.smul_def, IsScalarTower.toAlgHom_apply] using d.property.2 a b }
  left_inv d := Derivation.ext (fun _ => rfl)
  right_inv d := Subtype.ext (LinearMap.ext (fun _ => rfl))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientPointDerivationsEquiv_apply (d : Derivation ℂ B ℂ) (b : B) :
    (coefficientPointDerivationsEquiv B d).val b = d b := rfl

theorem coefficientPointDerivationsEquiv_dualLift
    (f : {f : B →ₐ[ℂ] DualNumber ℂ //
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f = IsScalarTower.toAlgHom ℂ B ℂ}) :
    coefficientPointDerivationsEquiv B (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv ℂ B ℂ f) =
      PointDerivations.dualPointDerivationsEquiv (IsScalarTower.toAlgHom ℂ B ℂ) f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  exact Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply ℂ B ℂ f b

variable [IsDomain B] [Algebra.Smooth ℂ B]

def nativeAffineCoefficientDerivationEquiv :
    TangentSpace 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)
      (IsScalarTower.toAlgHom ℂ B ℂ) ≃ₗ[ℂ] Derivation ℂ B ℂ :=
  (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations (IsScalarTower.toAlgHom ℂ B ℂ)).trans (coefficientPointDerivationsEquiv B).symm

theorem nativeAffineCoefficientDerivationEquiv_apply
    (v : TangentSpace 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) (IsScalarTower.toAlgHom ℂ B ℂ))
    (b : B) : nativeAffineCoefficientDerivationEquiv B v b =
      ((Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv (IsScalarTower.toAlgHom ℂ B ℂ) v).val b).snd := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientPointDerivations
