import OAI.RepresentationTheory.Theta.Geometric.InvariantFormsTranslation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps

/-! # Invariant Forms Smooth -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantFormsSmooth

noncomputable section

/-! The actual smooth realization of the algebraic cotangent forms is
translation invariant on the native analytic group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology

variable {G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]

theorem groupLeftTranslation_analytic (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GroupJetCoordinates.groupLeftTranslation c) = fun p => c * p := by
  funext p
  change p ≫ GroupJetCoordinates.groupLeftTranslation c = c * p
  rw [GroupJetCoordinates.groupLeftTranslation_point]
  have h : toUnit (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) = 𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) :=
    Subsingleton.elim _ _
  rw [h, Category.id_comp]

variable [IsIntegral G.left] [Smooth G.hom] [G.left.IsSeparated]
    {U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

theorem nativeGroupRealLie (G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsIntegral G.left] [Smooth G.hom] :
    LieGroup 𝓘(ℝ, AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) where
  contMDiff_mul :=
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.real_contMDiff_product_map (MonObj.mul (X := G))).of_le le_top
  contMDiff_inv := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (GrpObj.inv (X := G)) ∞

theorem nativeGroupComplexLie (G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsIntegral G.left] [Smooth G.hom] :
    LieGroup 𝓘(ℂ, AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) where
  contMDiff_mul :=
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (MonObj.mul (X := G))).of_le le_top
  contMDiff_inv := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (GrpObj.inv (X := G)) ∞

attribute [local instance] nativeGroupRealLie nativeGroupComplexLie

theorem identityCotangentOneForm_smooth_invariant (a : InvariantAlgebraicForms.identityChartCotangent U) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a) ∈
      AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (G := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) 1 := by
  rw [AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff]
  intro c
  have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality.globalSmoothForm_pullback (GroupJetCoordinates.groupLeftTranslation c)
    (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a)
  rw [InvariantFormsTranslation.identityCotangentOneForm_leftTranslation] at h
  apply Subtype.ext
  have hv := congrArg Subtype.val h.symm
  change (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a)).val.pullback
    (fun p => c * p) = _
  change (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a)).val.pullback
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GroupJetCoordinates.groupLeftTranslation c)) = _ at hv
  rw [groupLeftTranslation_analytic] at hv
  exact hv

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantFormsSmooth
