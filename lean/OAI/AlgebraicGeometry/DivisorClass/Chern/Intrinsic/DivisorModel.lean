import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.Residue
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicSectionNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Divisor Model -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DivisorModel

noncomputable section

/-!
# ChernClass: actual Chern multiplicities in native smooth divisor charts

Smoothness constructs the DVR equation and a genuine normal pair on the
whole native scheme manifold. Both chart directions are smooth, the normal
coordinate is the original regular parameter, and the actual relative
Chern class has the original divisor order in this same normal pair.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff _root_.Topology _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local instance : IsIntegral X.toOver.left := inferInstanceAs (IsIntegral X.carrier)
local instance : Smooth X.toOver.hom := X.smooth

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ

/-- Native complex differentiable coordinates realize the actual
algebraic multiplicity in the original global relative Chern class. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_native_divisor_model
    (z : X.carrier) (hz : Order.coheight z = 1) (hm : L.rationalSectionOrder z ≠ 0)
    (i : X.carrier) (hzi : z ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : IsAffineOpen U) (hzU : z ∈ U)
      (_ : U ≤ L.trivializingOpen i) (p b : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U z hzU p) ∧
      IsUnit (X.carrier.presheaf.germ U z hzU b) ∧
      ∀ (x : Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0),
        Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0 →
        ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
          (fun w : {y : Line.Bundles.AlgebraicLineBundle.analyticOpen X U // Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} => w.val.val)
          ⟨x, hxp⟩),
          ∃ hPU : P.neighborhood ⊆ (Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T),
          d + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom ∧
          P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, (Fin d → ℂ) × ℂ) ∧
          ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, (Fin d → ℂ) × ℂ) ∞ P.ambientChart P.ambientChart.source ∧
          ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × ℂ) 𝓘(ℂ, E) ∞ P.ambientChart.symm P.ambientChart.target ∧
          (∀ y : P.neighborhood, P.normalCoordinate y =
            Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p ⟨y.val, hPU y.property⟩) ∧
          ∃ hA : L.analyticReferenceLocus P.openNeighborhood ⊆ P.relativeComplement,
            CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P.openNeighborhood 2
              L.rationalSectionChernRelativeClass =
            (L.rationalSectionOrder z) • (NormalWinding.normalWindingCoefficient •
              AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
                (𝟙 (TopCat.of P.neighborhood)) hA 2 (HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalChartClass P)) := by
  obtain ⟨U, hU, hzU, hUi, p, v, b, hp, hb, hsm, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions.rationalSection_smooth_local_equation L z hz i hzi
  let : Nonempty U := ⟨⟨z, hzU⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  refine ⟨U, hU, hzU, hUi, p, b, hp, hb, ?_⟩
  intro x hxp hxb
  obtain ⟨d, P, hPU, hd, hmd, hforward, hinverse, hcoord⟩ :=
    HodgeConjecture.DegreeTwo.IntrinsicSectionNormalPair.Constructions.exists_native_section_normalPair_smooth X U hU p b hp0 hsm x hxp hxb
  refine ⟨d, P, hPU, hd, hmd, hforward, hinverse, hcoord, ?_⟩
  exact L.rationalSectionChernRelativeClass_native_parameter U p x hxp P hPU
    i hUi hp0 v (L.rationalSectionOrder z) hm he hcoord

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DivisorModel
