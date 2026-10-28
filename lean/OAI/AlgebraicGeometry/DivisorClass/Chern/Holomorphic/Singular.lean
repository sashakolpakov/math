import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Bundle
import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms

/-! # Singular -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Singular

noncomputable section

/-! The existing logarithmic singular Chern construction applied to the constructed holomorphic bundle. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicTransitionPair (u : Connecting.holomorphicUnitCohomology E M) (i j : M) :
    C((CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u j : Opens M), ℂ) :=
  ⟨(CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val.val,
    (CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val.property.continuous⟩

variable [CompactSpace M] [NormalSpace M]

def holomorphicLogRefinement (u : Connecting.holomorphicUnitCohomology E M) :
    LogRefinementOpen.Construction.CompactLogarithmicRefinement (CohomologyTransitions.holomorphicCohomologyDomain E M u)
      (holomorphicTransitionPair E M u) :=
  Classical.choice (LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement (CohomologyTransitions.holomorphicCohomologyDomain E M u)
    (fun x => ⟨x, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩)
    (holomorphicTransitionPair E M u)
    (fun i j x => SlitLog.holomorphicUnit_value_ne_zero (CohomologyTransitions.holomorphicCohomologyTransition E M u i j) x))

abbrev HolomorphicLogIndex (u : Connecting.holomorphicUnitCohomology E M) :=
  M × (holomorphicLogRefinement E M u).charts

abbrev holomorphicLogCover (u : Connecting.holomorphicUnitCohomology E M) :
    HolomorphicLogIndex E M u → Opens M :=
  (holomorphicLogRefinement E M u).refinement.cover

theorem holomorphicLogCover_subset (u : Connecting.holomorphicUnitCohomology E M)
    (i : HolomorphicLogIndex E M u) :
    holomorphicLogCover E M u i ≤ CohomologyTransitions.holomorphicCohomologyDomain E M u i.2.val :=
  (holomorphicLogRefinement E M u).refinement.subset i

theorem holomorphicLogCover_covers (u : Connecting.holomorphicUnitCohomology E M) (x : M) :
    ∃ i, x ∈ holomorphicLogCover E M u i :=
  (holomorphicLogRefinement E M u).refinement.covers x

def holomorphicLogCech (u : Connecting.holomorphicUnitCohomology E M) :
    LogCech.RationalCech.LogCechCochain (TopCat.of M) (holomorphicLogCover E M u) :=
  fun a => ((holomorphicLogRefinement E M u).refinement.logarithm (a 0) (a 1)).comp
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair (holomorphicLogCover E M u) a))

theorem exp_holomorphicLogCech (u : Connecting.holomorphicUnitCohomology E M)
    (a : Fin 2 → HolomorphicLogIndex E M u) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (holomorphicLogCover E M u) a) :
    Complex.exp (holomorphicLogCech E M u a x) =
      (CohomologyTransitions.holomorphicCohomologyTransition E M u (a 0).2.val (a 1).2.val).val
        ⟨x.val, holomorphicLogCover_subset E M u (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property),
          holomorphicLogCover_subset E M u (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property)⟩ :=
  (holomorphicLogRefinement E M u).refinement.exp_logarithm (a 0) (a 1)
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair (holomorphicLogCover E M u) a) x)

theorem holomorphicLogCech_cocycle (u : Connecting.holomorphicUnitCohomology E M) :
    LogCech.RationalCech.ExponentialCocycle (TopCat.of M) (holomorphicLogCover E M u)
      (holomorphicLogCech E M u) := by
  intro a x
  change Complex.exp (holomorphicLogCech E M u (a ∘ (2 : Fin 3).succAbove) _) *
    Complex.exp (holomorphicLogCech E M u (a ∘ (0 : Fin 3).succAbove) _) =
    Complex.exp (holomorphicLogCech E M u (a ∘ (1 : Fin 3).succAbove) _)
  rw [exp_holomorphicLogCech, exp_holomorphicLogCech, exp_holomorphicLogCech]
  exact CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M u (a 0).2.val (a 1).2.val (a 2).2.val x.val
    (holomorphicLogCover_subset E M u (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property))
    (holomorphicLogCover_subset E M u (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property))
    (holomorphicLogCover_subset E M u (a 2) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 2 x.property))

/-- The original rational logarithmic-defect-to-singular-cohomology construction. -/
def holomorphicFirstChernClassQ (u : Connecting.holomorphicUnitCohomology E M) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2 :=
  LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) (holomorphicLogCover E M u)
    (holomorphicLogCover_covers E M u) (holomorphicLogCech E M u) (holomorphicLogCech_cocycle E M u)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Singular
