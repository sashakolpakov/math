import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionSmoothNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormalReindex
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom

/-! # Section Smooth Fixed Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionSmoothFixedPair.Constructions

noncomputable section

/-!
# DegreeTwo: actual divisor equations in the canonical normal model

The proved codimension fixes the tangential model, and the complex-linear
one-coordinate equivalence fixes the normal model. The resulting pair is
eligible for the global regular Thom class's actual restriction theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

/-- Actual section normal coordinates in precisely the models of the
canonical global regular-support Thom class. -/
theorem exists_regular_section_fixedNormalPair_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (U : V.carrier.Opens) (hU : IsAffineOpen U)
    (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra V.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔
          y.val ∈ Set.range Z.analyticInclusion))
    (x : Z.regularAnalyticSpace)
    (hxU : Z.regularAnalyticToAmbient x ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0)
    (hxc : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
        Z.regularComplementInclusion x,
      ∃ hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
        𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∧
      ContMDiffOn 𝓘(ℂ, V.analyticModel)
        𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
        𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target ∧
      (∀ y : P.neighborhood, P.normalCoordinate y 0 =
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p ⟨y.val.val, hPU y.val y.property⟩) ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
        P.openNeighborhood 2 Z.regularThomClass = P.rationalClassFin := by
  obtain ⟨d, P, hPU, hd, hmd, hq, hqi, hcoord⟩ :=
    SectionSmoothNormalPair.Constructions.exists_regular_section_normalPair_smooth V Z U hU p b c hp hsm hsupp x hxU hxb hxc
  have hdZ := Z.regularComplexDimension_add_codimension
  have hd' : d = Z.regularComplexDimension := by omega
  subst d
  let T := NormalPairReindex.Constructions.normalPairReindex P NormalPairReindex.Constructions.planeCoordinates NormalPairReindex.Constructions.planeCoordinates_norm
  have hTP : T.neighborhood ⊆ P.neighborhood :=
    (NormalPairReindex.Constructions.normalPairReindex_neighborhood P NormalPairReindex.Constructions.planeCoordinates NormalPairReindex.Constructions.planeCoordinates_norm).subset
  have hTU : ∀ y ∈ T.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U :=
    fun y hy => hPU y (hTP hy)
  have hTd : T.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) :=
    NormalPairReindex.Constructions.normalPairReindex_mdifferentiable P NormalPairReindex.Constructions.planeCoordinates NormalPairReindex.Constructions.planeCoordinates_norm hmd
  have hqs := SmoothNormalReindex.Constructions.normalPairReindex_smooth P NormalPairReindex.Constructions.planeCoordinates NormalPairReindex.Constructions.planeCoordinates_norm hq hqi
  refine ⟨T, hTU, hTd, hqs.1, hqs.2, ?_, ?_⟩
  · intro y
    change NormalPairReindex.Constructions.planeCoordinates (P.ambientChart y.val).2 0 = _
    exact hcoord ⟨y.val, hTP y.property⟩
  · rw [T.rationalClassFin_eq_normalPullback]
    exact Z.regularThomClass_restrict_normalPair x T hTd

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionSmoothFixedPair.Constructions
