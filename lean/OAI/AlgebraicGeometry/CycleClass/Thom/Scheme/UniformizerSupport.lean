import OAI.AlgebraicGeometry.DivisorClass.Chern.SchemeUniformizerSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionCoordinates

/-! # Uniformizer Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.UniformizerSupport

noncomputable section

/-!
# ThomClass: the actual analytic parameter vanishes on the original divisor support

The canonical affine character chart preserves both section evaluation and
the original underlying scheme point. A section evaluates to zero exactly
when its germ is a nonunit. Thus the proved scheme support identity is the
literal zero-locus identity for the analytic equation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.DivisorClass.Chern.SchemeUniformizerSupport OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (hU : IsAffineOpen U)

/-- The canonical analytic affine chart has the original spectrum point as
its actual underlying scheme point. -/
theorem affineSectionPointHomeomorph_underlying
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).val =
      hU.fromSpec (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum
        (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) y) := by
  rw [SectionCoordinates.Constructions.affineSectionPointHomeomorph_val, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
  rfl

theorem affineSectionPointHomeomorph_prime
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    hU.primeIdealOf ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).val,
      (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).property⟩ = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  exact affineSectionPointHomeomorph_underlying X U hU y

include hU in
/-- Actual section evaluation detects exactly nonunit germs. -/
theorem sectionEvaluationOn_zero_iff_nonunit (p : Γ(X.left, U)) (y : SectionEvaluation.Constructions.analyticOpen X U) :
    SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔
      ¬ IsUnit (X.left.presheaf.germ U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val) y.property p) := by
  obtain ⟨z, rfl⟩ := (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).surjective y
  rw [SectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation,
    ← DivisorClass.Chern.SchemeUniformizerSupport.mem_affinePointPrime_iff hU
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU z).val,
        (SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU z).property⟩ p,
    affineSectionPointHomeomorph_prime]
  rfl

include hU in
/-- A genuine DVR parameter has the original divisor point closure as its
literal analytic zero locus on an actual algebraic neighborhood. -/
theorem smooth_uniformizer_analytic_support_neighborhood [IsIntegral X.left]
    [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    (x : X.left) (hxU : x ∈ U) (hx : Order.coheight x = 1)
    (p : Γ(X.left, U)) (hp : Irreducible (X.left.presheaf.germ U x hxU p)) :
    ∃ b : Γ(X.left, U), IsUnit (X.left.presheaf.germ U x hxU b) ∧
      ∀ y : SectionEvaluation.Constructions.analyticOpen X U, SectionEvaluation.Constructions.sectionEvaluationOn X U b y ≠ 0 →
        (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ closure ({x} : Set X.left)) := by
  obtain ⟨b, hb, hsupport⟩ := DivisorClass.Chern.SchemeUniformizerSupport.smooth_uniformizer_section_support_neighborhood
    X.hom U hU x hxU hx p hp
  refine ⟨b, hb, ?_⟩
  intro y hy
  have hbunit : IsUnit (X.left.presheaf.germ U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val) y.property b) := by
    by_contra hn
    exact hy ((sectionEvaluationOn_zero_iff_nonunit X U hU b y).mpr hn)
  exact (sectionEvaluationOn_zero_iff_nonunit X U hU p y).trans
    (hsupport ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val, y.property⟩ hbunit)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.UniformizerSupport
