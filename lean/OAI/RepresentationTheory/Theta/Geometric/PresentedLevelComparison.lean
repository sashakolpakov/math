import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Presented Level Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.PresentedLevelComparison

noncomputable section

/-! An equality on all original presented level labels implies the
full-level equations on every test scheme of the original fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem original_level_comparison_of_presented_points {g N : ℕ}
    {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation B)
    (α : A.FullLevel N) (β : B.FullLevel N) (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (hf : ∀ a : Multiplicative (Fin (2 * g) → ZMod N),
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ f ≫ Q.comparison.hom)
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
          ((α.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Q.comparison.hom
        ((β.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val)
    (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (a : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients g N)) :
    (α.hom.app (.op T) a).val ≫ f = (β.hom.app (.op T) a).val := by
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.level_comparison_of_base_constants α β f ?_ T a
  intro c
  have h := hf c
  change ((_ ≫ P.comparison.hom) ≫ (P.comparison.inv ≫ f ≫ Q.comparison.hom)) =
    _ ≫ Q.comparison.hom at h
  have he := congrArg (fun u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Q.variety.toOver => u ≫ Q.comparison.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using he

end

end OAI.RepresentationTheory.Theta.Geometric.PresentedLevelComparison
