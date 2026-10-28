import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticUniformizerSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConcreteResidue

/-! # Support Model -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SupportModel

noncomputable section

/-!
# ChernClass: local Chern models on the actual divisor support

The genuine normal equation cuts out the original point closure on a
principal neighborhood through that point. On the same neighborhood the
actual relative Chern class has its original algebraic multiplicity in
the constructed normal model. No equation, multiplicity, or support
identification is assumed as extra input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- The actual local Chern formula and the original algebraic support
hold on one genuine neighborhood of every nonzero divisor coefficient. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_actual_divisor_model
    (z : X.carrier) (hz : Order.coheight z = 1) (hm : L.rationalSectionOrder z ≠ 0)
    (i : X.carrier) (hzi : z ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : IsAffineOpen U) (hzU : z ∈ U)
      (_ : U ≤ L.trivializingOpen i) (p b : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U z hzU p) ∧
      IsUnit (X.carrier.presheaf.germ U z hzU b) ∧
      (∀ x : Line.Bundles.AlgebraicLineBundle.analyticOpen X U, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0 →
        (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0 ↔
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ closure ({z} : Set X.carrier))) ∧
      ∀ (x : Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0),
        Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0 →
        ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
          (Subtype.val : {y : Line.Bundles.AlgebraicLineBundle.analyticOpen X U // Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} → Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
          ⟨x, hxp⟩),
          ∃ hA : HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue.referenceComplement L U p x hxp P ⊆ P.relativeComplement,
          AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue.neighborhoodInclusion U p x hxp P)
            (HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue.referenceComplement_mapsTo L U p x hxp P) 2
            (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
              (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2 L.rationalSectionChernRelativeClass) =
          (L.rationalSectionOrder z) • (NormalWinding.normalWindingCoefficient •
            AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
              (𝟙 (TopCat.of P.neighborhood)) hA 2 (HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalChartClass P)) := by
  obtain ⟨U, hU, hzU, hUi, p, b, hp, hb, hmodel⟩ :=
    L.rationalSectionChernRelativeClass_actual_localThom_model z hz hm i hzi
  obtain ⟨c, hc, hsupport⟩ := AnalyticUniformizerSupport.smooth_uniformizer_analytic_support_neighborhood X U hU z hzU hz p hp
  refine ⟨U, hU, hzU, hUi, p, b * c, hp, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact hb.mul hc
  · intro x hx
    rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul] at hx
    exact hsupport x (mul_ne_zero_iff.mp hx).2
  · intro x hxp hx
    rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul] at hx
    exact hmodel x hxp (mul_ne_zero_iff.mp hx).1

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SupportModel
