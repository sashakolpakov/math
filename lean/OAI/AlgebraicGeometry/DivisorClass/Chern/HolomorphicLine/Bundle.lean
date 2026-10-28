import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension

/-! # Bundle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Bundle

noncomputable section

/-! The actual complex line bundle constructed from a class in H¹(Oˣ). -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicCohomologyCoordChange (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (i j : M)
    (x : M) : ℂ →L[ℂ] ℂ :=
  Holomorphic.OpenExtension.holomorphicOpenExtend (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val x •
    ContinuousLinearMap.id ℂ ℂ

theorem holomorphicCohomologyCoordChange_apply (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (i j x : M) (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) (v : ℂ) :
    holomorphicCohomologyCoordChange E M u i j x v =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ * v := by
  change Holomorphic.OpenExtension.holomorphicOpenExtend (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val x * v = _
  rw [Holomorphic.OpenExtension.holomorphicOpenExtend_apply (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val x ⟨hi, hj⟩]

theorem holomorphicCohomologyCoordChange_contMDiffOn (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (i j : M) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ (holomorphicCohomologyCoordChange E M u i j)
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j : Opens M) :=
  (Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val).smul
    contMDiffOn_const

/-- Native vector-bundle gluing, with one-dimensional complex model fiber. -/
def holomorphicLineBundleCore (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) : VectorBundleCore ℂ M ℂ M where
  baseSet i := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i
  isOpen_baseSet i := (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i).isOpen
  indexAt := id
  mem_baseSet_at x := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x
  coordChange := holomorphicCohomologyCoordChange E M u
  coordChange_self i x hx v := by
    rw [holomorphicCohomologyCoordChange_apply E M u i i x hx hx,
      Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self E M u i x hx, one_mul]
  continuousOn_coordChange i j := (holomorphicCohomologyCoordChange_contMDiffOn E M u i j).continuousOn
  coordChange_comp i j k x hx v := by
    rw [holomorphicCohomologyCoordChange_apply E M u j k x hx.1.2 hx.2,
      holomorphicCohomologyCoordChange_apply E M u i j x hx.1.1 hx.1.2,
      holomorphicCohomologyCoordChange_apply E M u i k x hx.1.1 hx.2]
    rw [← mul_assoc, mul_comm ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u j k).val _),
      Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M u i j k x hx.1.1 hx.1.2 hx.2]

instance holomorphicLineBundleCore_isContMDiff (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    (holomorphicLineBundleCore E M u).IsContMDiff 𝓘(ℂ, E) ∞ where
  contMDiffOn_coordChange := holomorphicCohomologyCoordChange_contMDiffOn E M u

/-- The fibers of the glued holomorphic line bundle. -/
abbrev holomorphicLineBundleFiber (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) : M → Type :=
  (holomorphicLineBundleCore E M u).Fiber

/-- The constructed bundle carries its actual holomorphic atlas. -/
theorem holomorphicLineBundle_contMDiff (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    ContMDiffVectorBundle ∞ ℂ (holomorphicLineBundleFiber E M u) 𝓘(ℂ, E) :=
  inferInstance

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Bundle
