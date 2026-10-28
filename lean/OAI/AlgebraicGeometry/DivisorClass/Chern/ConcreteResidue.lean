import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneWindingComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomModel

/-! # Concrete Residue -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConcreteResidue

noncomputable section

/-!
# ChernClass: actual algebraic divisor orders in the relative Chern class

The global lift of the original first Chern cocycle has, near each actual
codimension-one divisor point, a genuine analytic Thom model with the
already-defined algebraic multiplicity. Smoothness supplies the DVR,
equation, and normal coordinates through the checked DegreeTwo constructions.
The primitive orientation coefficient is retained explicitly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomModel.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- The actual relative first Chern class has the actual divisor
multiplicity in genuine normal coordinates, with no local equation or
normal-form assumption supplied by the caller. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_actual_localThom_model
    (z : X.carrier) (hz : Order.coheight z = 1) (hm : L.rationalSectionOrder z ≠ 0)
    (i : X.carrier) (hzi : z ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : IsAffineOpen U) (hzU : z ∈ U)
      (_ : U ≤ L.trivializingOpen i) (p b : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U z hzU p) ∧
      IsUnit (X.carrier.presheaf.germ U z hzU b) ∧
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
    HodgeConjecture.DegreeTwo.DivisorThomModel.Constructions.rationalSection_actual_localThom_model L z hz hm i hzi
  refine ⟨U, hU, hzU, hUi, p, b, hp, hb, ?_⟩
  intro x hxp hxb
  obtain ⟨d, P, hA, hc⟩ := hmodel x hxp hxb
  refine ⟨d, P, hA, ?_⟩
  rw [L.rationalSectionChernRelativeClass_algebraic i U hUi]
  rw [PlaneWindingComparison.neg_windingNormalCoefficient_eq_normalWindingCoefficient] at hc
  exact hc

/-- At a zero actual divisor coefficient, the genuine relative Chern
class vanishes on an affine neighborhood of that codimension-one point. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_local_zero_of_order_zero
    (z : X.carrier) (hz : Order.coheight z = 1) (hm : L.rationalSectionOrder z = 0)
    (i : X.carrier) (hzi : z ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (_ : z ∈ U),
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2 L.rationalSectionChernRelativeClass = 0 := by
  obtain ⟨U, hU, hzU, hUi, hc⟩ :=
    HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.rationalSection_local_zero_of_order_zero L z hz hm i hzi
  exact ⟨U, hU, hzU, (L.rationalSectionChernRelativeClass_algebraic i U hUi).trans hc⟩

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConcreteResidue
