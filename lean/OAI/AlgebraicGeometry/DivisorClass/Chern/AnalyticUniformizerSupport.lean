import OAI.AlgebraicGeometry.DivisorClass.Chern.SchemeUniformizerSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates

/-! # Analytic Uniformizer Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticUniformizerSupport

noncomputable section

/-!
# ChernClass: the actual analytic parameter vanishes on the original divisor support

The canonical affine character chart preserves both section evaluation and
the original underlying scheme point. A section evaluates to zero exactly
when its germ is a nonunit. Thus the proved scheme support identity is the
literal zero-locus identity for the analytic equation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (U : X.carrier.Opens) (hU : IsAffineOpen U)

/-- The canonical analytic affine chart has the original spectrum point as
its actual underlying scheme point. -/
theorem affineSectionPointHomeomorph_underlying
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).val =
      hU.fromSpec (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum
        (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) y) := by
  rw [HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_val, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
  rfl

theorem affineSectionPointHomeomorph_prime
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)) :
    hU.primeIdealOf ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).val,
      (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU y).property⟩ = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  exact affineSectionPointHomeomorph_underlying X U hU y

include hU in
/-- Actual section evaluation detects exactly nonunit germs. -/
theorem sectionEvaluationOn_zero_iff_nonunit (p : Γ(X.carrier, U)) (y : Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0 ↔
      ¬ IsUnit (X.carrier.presheaf.germ U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val) y.property p) := by
  obtain ⟨z, rfl⟩ := (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).surjective y
  rw [HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation,
    ← SchemeUniformizerSupport.mem_affinePointPrime_iff hU
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU z).val,
        (HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU z).property⟩ p,
    affineSectionPointHomeomorph_prime]
  rfl

include hU in
/-- A genuine DVR parameter has the original divisor point closure as its
literal analytic zero locus on an actual algebraic neighborhood. -/
theorem smooth_uniformizer_analytic_support_neighborhood [IsIntegral X.carrier]
    (x : X.carrier) (hxU : x ∈ U) (hx : Order.coheight x = 1)
    (p : Γ(X.carrier, U)) (hp : Irreducible (X.carrier.presheaf.germ U x hxU p)) :
    ∃ b : Γ(X.carrier, U), IsUnit (X.carrier.presheaf.germ U x hxU b) ∧
      ∀ y : Line.Bundles.AlgebraicLineBundle.analyticOpen X U, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b y ≠ 0 →
        (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0 ↔
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ closure ({x} : Set X.carrier)) := by
  let : Smooth X.structureMap := X.smooth
  obtain ⟨b, hb, hsupport⟩ := SchemeUniformizerSupport.smooth_uniformizer_section_support_neighborhood
    X.structureMap U hU x hxU hx p hp
  refine ⟨b, hb, ?_⟩
  intro y hy
  have hbunit : IsUnit (X.carrier.presheaf.germ U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val) y.property b) := by
    by_contra hn
    exact hy ((sectionEvaluationOn_zero_iff_nonunit X U hU b y).mpr hn)
  exact (sectionEvaluationOn_zero_iff_nonunit X U hU p y).trans
    (hsupport ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val, y.property⟩ hbunit)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticUniformizerSupport
