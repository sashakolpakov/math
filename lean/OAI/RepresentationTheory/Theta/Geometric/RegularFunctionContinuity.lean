import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

/-! # Regular Function Continuity -/

namespace OAI.RepresentationTheory.Theta.Geometric.RegularFunctionContinuity

noncomputable section

/-! Evaluation of an actual global regular function is continuous on
native complex scheme points, checked through all affine tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def regularFunctionValue (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ℂ :=
  Complex.SectionEvaluation.complexSectionValue p.left ⊤ (by trivial) s

theorem regularFunctionValue_affineTest (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤))
    (A : CommAlgCat ℂ) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    regularFunctionValue X s (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) =
      x ((Scheme.ΓSpecIso (.of A)).hom (i.left.appTop s)) := by
  have H := Complex.SectionEvaluation.complexSectionValue_pullback (Spec.map (CommRingCat.ofHom x.toRingHom)) i.left
    ⊤ ⊤ le_top (by trivial) s
  change Complex.SectionEvaluation.complexSectionValue _ ⊤ (by trivial) (i.left.appTop s) = _ at H
  have H' := Complex.SectionEvaluation.complexSectionValue_spec x.toRingHom ((Scheme.ΓSpecIso (.of A)).hom (i.left.appTop s))
  have hs := (Scheme.ΓSpecIso (.of A)).hom_inv_id_apply (i.left.appTop s)
  exact H.symm.trans ((congrArg
    (Complex.SectionEvaluation.complexSectionValue (Spec.map (CommRingCat.ofHom x.toRingHom)) ⊤ (by trivial)) hs).symm.trans H')

theorem regularFunctionValue_continuous (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    Continuous (regularFunctionValue X s) := by
  apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A i
  exact (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval ((Scheme.ΓSpecIso (.of A)).hom (i.left.appTop s))).congr
    (fun x => (regularFunctionValue_affineTest X s A i x).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.RegularFunctionContinuity
