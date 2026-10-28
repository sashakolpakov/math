import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! # Point Topologies -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologies

noncomputable section

/-! # Comparing the actual complex-point topologies

The point carriers and the affine character maps are the actual scheme maps in
both libraries. This file proves their compatibility, rather than identifying
an unrelated topological model with the original analytification.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- Both affine character correspondences give exactly the same scheme point. -/
theorem affineCharacterPoint_eq (a : A →ₐ[ℂ] ℂ) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A a = (ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A).symm a := by
  apply Over.OverMorphism.ext
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  rfl

/-- On affine schemes the identity on actual points is a homeomorphism between the topologies. -/
def affinePointTopologiesHomeomorph :
    @Homeomorph (ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))
      (ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _) ComplexPoint.Basic.Point.analyticTopology :=
  @Homeomorph.mk _ _
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _) ComplexPoint.Basic.Point.analyticTopology
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A).symm)
    (@Continuous.comp _ _ _
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _)
      (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A) ComplexPoint.Basic.Point.analyticTopology _ _
      (ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm A)
      (@Homeomorph.continuous_invFun _ _
        (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A)))
    (@Continuous.comp _ _ _ ComplexPoint.Basic.Point.analyticTopology
      (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _) _ _
      (@Homeomorph.continuous_toFun _ _
        (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A))
      (ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv A))

/-- This compatibility uses the identity map, not a change of scheme points. -/
@[simp]
theorem affinePointTopologiesHomeomorph_apply
    (z : ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) :
    (@Homeomorph.toEquiv _ _
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology _) ComplexPoint.Basic.Point.analyticTopology
      (affinePointTopologiesHomeomorph A)) z = z := by
  change (ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A).symm
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A).symm z) = z
  rw [← affineCharacterPoint_eq]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A).apply_symm_apply z

/-- The unchanged affine character-to-scheme-point map is continuous in the original topology. -/
theorem affineCharacterPoint_continuous :
    @Continuous (A →ₐ[ℂ] ℂ) (ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))
      (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A) ComplexPoint.Basic.Point.analyticTopology
      (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A) := by
  let : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) := ComplexPoint.Basic.Point.analyticTopology
  exact @Continuous.congr _ _ (ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology A)
    ComplexPoint.Basic.Point.analyticTopology _ _ (ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm A)
    (fun a => (affineCharacterPoint_eq A a).symm)

/-- The identity from the older affine-test topology to the original analytic topology
is continuous for every actual scheme over ℂ. -/
theorem affineTestToAnalytic_continuous (X : Over (Spec (.of ℂ))) :
    @Continuous (ComplexPoint.Basic.ComplexSchemePoint X) (ComplexPoint.Basic.ComplexSchemePoint X)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X) ComplexPoint.Basic.Point.analyticTopology id := by
  let : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint X) := ComplexPoint.Basic.Point.analyticTopology
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests (X := X) id).mpr
  intro A f
  let : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) := ComplexPoint.Basic.Point.analyticTopology
  have hc := (ComplexPoint.Basic.Point.continuous_map f).comp (affineCharacterPoint_continuous A)
  simpa only [Function.comp_def,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap, ComplexPoint.Basic.Point.map, id_eq] using hc

end

end OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologies
