import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.SchemeStructureBound
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPoincareParameter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Represented Picard Tangent Bijection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentBijection

noncomputable section

/-! The actual representing dual's tangent space is the original
structure-sheaf H1: injectivity comes from the Poincare family, and
surjectivity follows from the proved native H1 dimension bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)

local instance representedPicardTargetIntegral : IsIntegral A.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
local instance representedPicardSourceIntegral : IsIntegral D.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral D.abelian
local instance representedPicardTargetDiagonal :
    IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal A.scheme
local instance representedPicardH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.scheme

def representedPicardTangentLinear :
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension D.abelian.scheme.hom) → ℂ) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1 :=
  Intrinsic.ParameterTangentLinear.nativeParameterTangentLinear A D.poincare D.normalizedAtDualZero.some
    D.normalizedAtAbelianZero.some (RepresentedPoincareParameter.representedPoincareParameter_mul D)

theorem representedPicardTangentLinear_injective :
    Function.Injective (representedPicardTangentLinear A D) :=
  Intrinsic.ParameterTangentLinear.nativeParameterTangentLinear_injective A D.poincare D.normalizedAtDualZero.some
    D.normalizedAtAbelianZero.some (RepresentedPoincareParameter.representedPoincareParameter_mul D)
    (RepresentedPoincareParameter.representedPoincareParameter_injective D (LieRanks.dualNumberTest ℂ))

include D P

theorem representedPicardTangentLinear_bijective :
    Function.Bijective (representedPicardTangentLinear A D) := by
  let : FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) :=
    Abelian.SchemeStructureBound.abelianSchemeStructureH1_finiteDimensional A P
  have hi := representedPicardTangentLinear_injective A D
  have hle : Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) ≤
      Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension D.abelian.scheme.hom) → ℂ) := by
    rw [Module.finrank_fin_fun, Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq D.abelian]
    exact Abelian.SchemeStructureBound.abelianSchemeStructureH1_finrank_le A P
  have hd := le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) hle
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

def representedPicardTangentEquiv :
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension D.abelian.scheme.hom) → ℂ) ≃ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1 :=
  LinearEquiv.ofBijective (representedPicardTangentLinear A D)
    (representedPicardTangentLinear_bijective A D P)

theorem representedStructureH1_finrank :
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) = g := by
  have h := (representedPicardTangentEquiv A D P).finrank_eq.symm
  rw [Module.finrank_fin_fun, Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq D.abelian] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentBijection
