import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.InfinitesimalTheta
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.InfinitesimalPicardLift

/-! # Infinitesimal Picard Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual descended Picard family has no nontrivial native
dual-number point in its infinitesimal kernel at the origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {N : DualModel.ReferenceDualModel F hP}

theorem IsogenyKernel.ReferenceLatticeIsogeny.parameterPicardClass_infinitesimal_kernel_trivial (p : IsogenyKernel.ReferenceLatticeIsogeny M N)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension
      (U.projectiveMap z))
    (hg' : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension
      (V.projectiveMap z))
    (Q : HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)
    (eA : (Q.pullback (lift (𝟙 N.abelianScheme.scheme)
      (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left)
    (eB : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (v : DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1)
    (hv : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q v.val = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q
      (1 : LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme)) : v.val = 1 := by
  obtain ⟨r, hr, ⟨u⟩⟩ := p.exists_infinitesimal_translation_comparison
    (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) Q recover eA eB v hv
  have hr0 := M.nativeInfinitesimalTheta_eq_one U V hdeg f g hf hg' r u
  rw [hr0, MonObj.one_comp] at hr
  exact hr.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
