import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Scalars

/-! # Scalar Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarSectionValues

noncomputable section

/-! Values of actual regular sections under scalar pullback use
the original scalar endomorphism of the dual-number coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualGlobalSectionValue_scalar {X : Scheme.{0}} (c : ℂ)
    (p : Spec (.of (DualNumber ℂ)) ⟶ X) (s : Γ(X, ⊤)) :
    RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue ((LieRanks.dualNumberScalar ℂ c).left ≫ p) s =
      LieRanks.dualNumberScale ℂ c (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue p s) :=
  (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue_pullback (LieRanks.dualNumberScalar ℂ c).left p s).trans
    (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue_spec (LieRanks.dualNumberScale ℂ c).toRingHom (p.appTop s))

theorem dualConstantPoint_scalar_section (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left ((Scalars.dualFamilyScalar X c).left.appTop s) =
      LieRanks.dualNumberScale ℂ c (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s) :=
  (SectionValueTransport.dualSectionValue_transport (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left (Scalars.dualFamilyScalar X c).left
    ((LieRanks.dualNumberScalar ℂ c).left ≫ (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left)
    (congrArg (fun f : LieRanks.dualNumberTest ℂ ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) (Scalars.dualConstantPoint_scalar X c p)) s).trans
      (dualGlobalSectionValue_scalar c (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarSectionValues
