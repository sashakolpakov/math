import OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologyEquality
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import OAI.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! # Regular Section Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RegularSectionBridge

noncomputable section

/-! # Actual regular-function evaluations in both point conventions

These formulas compare the original stalk evaluation to the actual algebra
characters on an affine open. They will be used to compare the analytic atlases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint

/-- The two affine-point correspondences are the same actual scheme morphism. -/
theorem nativeAffinePoint_eq_original (A : Type) [CommRing A] [Algebra ℂ A]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x = (ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A).symm x := by
  apply Over.OverMorphism.ext
  change (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x).left = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  rfl

/-- Original stalk evaluation on the actual affine scheme point is evaluation by its character. -/
theorem evaluate_nativeAffinePoint (A : Type) [CommRing A] [Algebra ℂ A]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (a : A) :
    ComplexPoint.Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x) = x a := by
  rw [nativeAffinePoint_eq_original]
  change ComplexPoint.Basic.Point.evaluate (X := Over.mk (ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap A)) ⊤
    ((Scheme.ΓSpecIso (.of A)).inv a) ((ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A).symm x) = x a
  rw [ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top]
  simp only [Iso.inv_hom_id_apply]

/-- Pullback by the genuine spectrum-of-sections map evaluates the corresponding section. -/
theorem evaluate_fromSpecSection (X : Over (Spec (.of ℂ)))
    (U : X.left.Opens) (hU : IsAffineOpen U) [Algebra ℂ Γ(X.left, U)]
    (f : Over.mk (ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap Γ(X.left, U)) ⟶ X)
    (hf : f.left = hU.fromSpec)
    (z : ComplexPoint.Basic.ComplexSchemePoint (Over.mk (ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap Γ(X.left, U))))
    (s : Γ(X.left, U)) :
    ComplexPoint.Basic.Point.evaluate U s (ComplexPoint.Basic.Point.map f z) =
      ComplexPoint.Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso (.of Γ(X.left, U))).inv s) z := by
  rw [ComplexPoint.Basic.Point.evaluate_map, hf, hU.fromSpec_app_self]
  exact (ComplexPoint.Basic.ComplexSchemePoint.evaluate_eq (Y := Over.mk (ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap Γ(X.left, U)))
    hU.fromSpec_preimage_self.symm
    ((Scheme.ΓSpecIso (.of Γ(X.left, U))).inv s) z).symm

/-- The actual affine-open character evaluates exactly the original ambient regular section. -/
theorem evaluate_nativeAffineOpenPoint (X : Over (Spec (.of ℂ)))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (s : Γ(X.left, U)) :
    ComplexPoint.Basic.Point.evaluate U s (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x) =
      x s := by
  let : Algebra ℂ Γ(X.left, U) := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  have h := evaluate_fromSpecSection X U hU
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) rfl
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, U) x) s
  exact h.trans (evaluate_nativeAffinePoint
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) x s)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RegularSectionBridge
