import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalOpenStage
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.FixedNormalComparison

/-! # Global Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalTrace

noncomputable section

/-! The native global compact Thom pushforward preserves the original fundamental trace, with coefficient exactly one. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Construction

theorem compactSupportOpenExtension_degreeCast (X : TopCat.{0}) [T2Space X] (U : Opens X)
    {p q : ℕ} (h : p = q)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) p) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := X) U p b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := X) U q
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)) h) b) := by
  subst q
  rfl

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = D.regularThomClass)

theorem regularSourceCompactThomPushforward_fixed_normal (x : D.regularAnalyticSpace) (q : ℕ)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)) q) :
    SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha q
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace) (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x) q b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAmbientSpace) (D.regularFixedNormalPair x).openNeighborhood ((2 * p)+q)
      (HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin (D.regularFixedNormalPair x)
        D.isClosedEmbedding_regularComplementInclusion.isEmbedding q b) := by
  obtain ⟨K, c, rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)) q b
  have h := ConcreteCategory.congr_hom (NormalOpenStage.Constructions.Construction.regularSourceCompactThomPushforward_normal_stage D x
    (D.regularFixedNormalPair x) a ha K q) c
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAmbientSpace)
    (D.regularFixedNormalPair x).openNeighborhood ((2 * p)+q)) (FixedNormalComparison.Constructions.Construction.regularFixedNormalThomStage_compact D a ha x K q c))

theorem regularSourceCompactThomPushforward_trace_hom [SecondCountableTopology D.regularAnalyticSpace] :
    SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha (2 * D.regularComplexDimension) ≫
      eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace))
        (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D)) ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := D.regularAmbientSpace) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := D.regularAnalyticSpace) := by
  apply FixedNormalCover.Constructions.Construction.regularTopCompact_fixedNormal_hom_ext D
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := D.regularAmbientSpace)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace))
      (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D))
      (SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha (2 * D.regularComplexDimension)
        (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace) (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)
          (2 * D.regularComplexDimension) b))) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := D.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace) (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)
        (2 * D.regularComplexDimension) b)
  rw [regularSourceCompactThomPushforward_fixed_normal,
    compactSupportOpenExtension_degreeCast (TopCat.of D.regularAmbientSpace)
      (D.regularFixedNormalPair x).openNeighborhood (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D),
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply, AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply]
  have ht := NormalSourceTrace.Constructions.Construction.regularNormalPairSourceCompactGysin_topTrace V D x (D.regularFixedNormalPair x)
    (FixedNormalCover.Constructions.Construction.regularFixedNormalPair_contMDiffOn D x) (FixedNormalCover.Constructions.Construction.regularFixedNormalPair_symm_contMDiffOn D x) b
  exact ht

theorem regularSourceCompactThomPushforward_trace [SecondCountableTopology D.regularAnalyticSpace]
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := D.regularAmbientSpace)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace))
        (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D))
        (SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha (2 * D.regularComplexDimension) b)) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := D.regularAnalyticSpace) b :=
  ConcreteCategory.congr_hom (regularSourceCompactThomPushforward_trace_hom D a ha) b

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalTrace
