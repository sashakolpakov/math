import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo

/-! # Divisor Thom Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomModel.Constructions

noncomputable section

/-!
# DegreeTwo: actual divisor orders have genuine local Thom models

Starting at an actual codimension-one scheme point, smoothness proves the
DVR property, supplies the equation with its algebraic order, and constructs
the analytic normal pair. No normal-coordinate assumption is supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue

/-- The genuine local Thom model at every smooth complex point of a
neighborhood of an actual nonzero rational-section divisor coefficient. -/
theorem rationalSection_actual_localThom_model {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]
    (z : X.carrier) (hz : Order.coheight z = 1) (hm : L.rationalSectionOrder z ≠ 0)
    (i : X.carrier) (hzi : z ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : IsAffineOpen U) (hzU : z ∈ U)
      (hUi : U ≤ L.trivializingOpen i) (p b : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U z hzU p) ∧
      IsUnit (X.carrier.presheaf.germ U z hzU b) ∧
      ∀ (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0),
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0 →
        ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
          (Subtype.val : {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U // DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} → DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
          ⟨x, hxp⟩),
          ∃ hA : DivisorThomTo.Constructions.DivisorThomResidue.referenceComplement L U p x hxp P ⊆ P.relativeComplement,
          AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (DivisorThomTo.Constructions.DivisorThomResidue.neighborhoodInclusion U p x hxp P)
            (DivisorThomTo.Constructions.DivisorThomResidue.referenceComplement_mapsTo L U p x hxp P) 2
            (L.rationalSectionLocalSupportedClass i U hUi) =
          (L.rationalSectionOrder z) • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
            AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
              (𝟙 (TopCat.of P.neighborhood)) hA 2 (NormalMultiplicity.Constructions.normalChartClass P)) := by
  obtain ⟨U, hU, hzU, hUi, p, v, b, hp, hb, hsm, he⟩ :=
    DivisorSmooth.Constructions.rationalSection_smooth_local_equation L z hz i hzi
  let : Nonempty U := ⟨⟨z, hzU⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  refine ⟨U, hU, hzU, hUi, p, b, hp, hb, ?_⟩
  intro x hxp hxb
  obtain ⟨d, P, _, hP⟩ := SectionNormalPair.Constructions.exists_section_normalPair X U hU p b hp0 hsm x hxp hxb
  obtain ⟨hA, hclass⟩ := DivisorThomTo.Constructions.DivisorThomResidue.rationalSectionLocalClass_eq_localThom L U p x hxp P
    i hUi hp0 v (L.rationalSectionOrder z) hm he hP
  exact ⟨d, P, hA, hclass⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomModel.Constructions
