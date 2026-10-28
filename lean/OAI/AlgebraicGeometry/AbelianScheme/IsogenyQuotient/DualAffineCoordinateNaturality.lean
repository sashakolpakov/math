import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePresentationChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart

/-! # Dual Affine Coordinate Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualAffineCoordinateNaturality.Construction

noncomputable section

/-! The original change of affine coordinates extends coefficientwise
to dual numbers and commutes with the actual translation chart.
The induced regular-section comparison is therefore proved on the
original open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart

theorem dualCoefficientProductMap_natural (B D : CommAlgCat ℂ) (q : B →ₐ[ℂ] D) :
    AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber D) (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q) ≫
        AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart.dualCoefficientProductMap B =
      AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart.dualCoefficientProductMap D ≫ (𝟙 (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B D q) := by
  have hleft : (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q).comp (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ B)) =
      AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ D) := by
    apply AlgHom.ext
    intro x
    apply TrivSqZeroExt.ext
    · exact q.commutes x.fst
    · exact q.commutes x.snd
  have hright : (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q).comp (TrivSqZeroExt.inlAlgHom ℂ B B) =
      (TrivSqZeroExt.inlAlgHom ℂ D D).comp q := by
    apply AlgHom.ext
    intro x
    apply TrivSqZeroExt.ext
    · rfl
    · exact q.map_zero
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart.dualCoefficientProductMap, lift_fst,
      tensorHom_fst, Category.comp_id]
    rw [AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverAlgHom_comp, hleft]
  · simp only [Category.assoc, AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart.dualCoefficientProductMap, lift_snd, lift_snd_assoc,
      tensorHom_snd, AbelianModuli.ReferenceFamily.Dual.CoefficientSchemeTests.dualCoefficientProjection]
    rw [AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverAlgHom_comp, AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverAlgHom_comp, hright]

theorem dualAffineTranslationChart_coordinateMap
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B D : CommAlgCat ℂ) (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) (q : B →ₐ[ℂ] D) :
    AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber D) (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q) ≫
        AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i =
      AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D (AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B D q ≫ i) := by
  rw [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_factor, ← Category.assoc, dualCoefficientProductMap_natural]
  simp only [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_factor, Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp]

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B D : CommAlgCat ℂ)
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) (j : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (h : j.left.opensRange = i.left.opensRange)

theorem sameOpenDualCoordinateMap_square :
    AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber D)
        (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h)) ≫
        AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i = AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j := by
  rw [dualAffineTranslationChart_coordinateMap, AffinePresentationChange.Construction.sameOpenAffineCoordinateMap_square]

include h in
theorem sameOpenDualChart_range :
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j).left.opensRange =
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange := by
  rw [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range, AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range, h]

theorem sameOpenDualCoordinateMap_sections (a : DualNumber B) :
    AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)
        (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h) a) =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.presheaf.map
        (homOfLE (sameOpenDualChart_range G B D i j h).le).op
        (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
          (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i) a) :=
  AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv_natural ℂ (CommAlgCat.of ℂ (DualNumber B))
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)
    (CommAlgCat.of ℂ (DualNumber D)) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)
    (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h))
    (sameOpenDualCoordinateMap_square G B D i j h) (sameOpenDualChart_range G B D i j h).le a

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualAffineCoordinateNaturality.Construction
