import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality

/-! # Complex Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ComplexConstants

noncomputable section

/-! The canonical affine complex algebra constants agree with
the actual global section map of the specified complex structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineComplexConstant_structure (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (c : ℂ) :
    algebraMap ℂ Γ(X.left, ⊤) c = X.hom.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_top_ext X
  intro p
  have hl : RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.left ⊤ (by trivial) (algebraMap ℂ Γ(X.left, ⊤) c) = c := by
    rw [Complex.TopSectionValues.complexSectionValue_top_formula, ← Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval]
    exact (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p).commutes c
  have hr := Complex.TopSectionValues.complexSectionValue_top_pullback p.left X.hom ((Scheme.ΓSpecIso (.of ℂ)).inv c)
  have hp : p.left ≫ X.hom = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := Over.w p
  have hc : RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue (p.left ≫ X.hom) ⊤ (by trivial)
      ((Scheme.ΓSpecIso (.of ℂ)).inv c) = c := by
    rw [hp, Complex.TopSectionValues.complexSectionValue_top_formula]
    change (Scheme.ΓSpecIso (.of ℂ)).hom ((Scheme.ΓSpecIso (.of ℂ)).inv c) = c
    exact Iso.inv_hom_id_apply _ _
  exact hl.trans (hr.symm.trans hc).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ComplexConstants
