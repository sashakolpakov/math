import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction

/-! # Period Action Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodActionLieRanks.IntrinsicIntegralAction

noncomputable section

/-! The genuine period action has exactly the Lie eigenspace dimensions
specified using the original abelian scheme's dual-number points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential.IntrinsicLinearMaps

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction R A)

local instance : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

theorem nativeMap_eq_original (a : R) : Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a = ρ.map a := by
  apply Over.OverMorphism.ext
  change (𝟙 A.scheme.left ≫ (ρ.map a).left) ≫ 𝟙 A.scheme.left = (ρ.map a).left
  rw [Category.id_comp, Category.comp_id]

theorem linearAction_eq_nativeLieDifferential (a : R) :
    Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a = Intrinsic.Lie.nativeLieDifferential A ρ a := by
  have h := Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_eq_nativeDifferential (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a)
  have he := congrArg (fun f : A.scheme ⟶ A.scheme =>
    (show Module.End ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ) from
    (mfderiv 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1).toLinearMap)) (nativeMap_eq_original A P ρ a)
  exact h.trans he

def periodActionEigenspace (τ : R →+* ℂ) : Submodule ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) where
  carrier := {v | ∀ a : R, Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a v = τ a • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hu hv a := by rw [map_add, hu a, hv a, smul_add]
  smul_mem' z v hv a := by rw [map_smul, hv a, smul_comm]

theorem periodActionEigenspace_eq (τ : R →+* ℂ) :
    periodActionEigenspace A P ρ τ = Intrinsic.Lie.nativeLieEigenspace A ρ τ := by
  ext v
  change (∀ a, Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a v = τ a • v) ↔
    ∀ a, Intrinsic.Lie.nativeLieDifferential A ρ a v = τ a • v
  constructor
  · intro hv a
    exact (LinearMap.congr_fun (linearAction_eq_nativeLieDifferential A P ρ a) v).symm.trans (hv a)
  · intro hv a
    exact (LinearMap.congr_fun (linearAction_eq_nativeLieDifferential A P ρ a) v).trans (hv a)

theorem periodActionEigenspace_finrank (τ : R →+* ℂ) {r : ℕ} (hr : LieRanks.HasLieRank A ρ τ r) :
    Module.finrank ℂ (periodActionEigenspace A P ρ τ) = r := by
  rw [periodActionEigenspace_eq]
  exact hr.native_finrank A ρ τ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodActionLieRanks.IntrinsicIntegralAction
