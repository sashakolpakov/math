import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Compact Pairing -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.CompactPairing

noncomputable section

/-! The actual compact integration pairing under restriction to an open manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Open extension of a compact test is adjoint to actual ordinary restriction. -/
theorem evaluation_openExtension (U : Opens M) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq a (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U q b) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := U) p q hpq
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a) b := by
  simp only [AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation_apply]
  rw [AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality.complexManifoldCompactSupportCap_open_apply]
  exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (X := TopCat.of U) (Y := TopCat.of M) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) q p (by omega) b)).symm

/-- At an actual compact support, restricting a test to an open neighborhood
of its support preserves its pairing with the restricted ordinary class. -/
theorem evaluation_openStage (U : Opens M) (K : Compacts U)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M)ᶜ q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq a
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of M) U K) q b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := U) p q hpq
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K q
        ((AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K q).hom b)) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportCohomologyι_openExtension (X := TopCat.of M) U K q)
    ((AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K q).hom b)
  change AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K q
        ((AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K q).hom b)) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of M) U K) q
      ((AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K q).inv ((AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K q).hom b)) at h
  rw [Iso.hom_inv_id_apply] at h
  rw [← h]
  exact evaluation_openExtension d U p q hpq a _

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.CompactPairing
