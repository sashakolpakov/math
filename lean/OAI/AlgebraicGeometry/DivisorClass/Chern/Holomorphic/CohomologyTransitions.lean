import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

/-! # Cohomology Transitions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions

noncomputable section

/-! Actual holomorphic transition units extracted from degree-one unit-sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicCohomologyRepresentative (u : Connecting.holomorphicUnitCohomology E M) :
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₃.obj.obj (op (⊤ : Opens M)) :=
  Classical.choose (Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary_surjective (Sheaves.holomorphicUnitsSheaf E M) u)

theorem holomorphicCohomologyRepresentative_spec (u : Connecting.holomorphicUnitCohomology E M) :
    Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary (Sheaves.holomorphicUnitsSheaf E M)
      (holomorphicCohomologyRepresentative E M u) = u :=
  Classical.choose_spec (Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary_surjective (Sheaves.holomorphicUnitsSheaf E M) u)

def holomorphicCohomologyLocalLifts (u : Connecting.holomorphicUnitCohomology E M) :
    Sheaf.CohomologyLifts.SheafLocalLiftCover (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).g
      (holomorphicCohomologyRepresentative E M u) := by
  have := (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)).epi_g
  exact Sheaf.CohomologyLifts.sheafLocalLiftCover _ _

abbrev holomorphicCohomologyDomain (u : Connecting.holomorphicUnitCohomology E M) (i : M) : Opens M :=
  (holomorphicCohomologyLocalLifts E M u).domain i

def holomorphicCohomologyTransition (u : Connecting.holomorphicUnitCohomology E M) (i j : M) :
    (Exponential.HolomorphicFunction (E := E)
      (M := ↥(holomorphicCohomologyDomain E M u i ⊓ holomorphicCohomologyDomain E M u j)))ˣ :=
  Additive.toMul ((holomorphicCohomologyLocalLifts E M u).transition
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)) i j)

theorem holomorphicCohomologyTransition_cocycle (u : Connecting.holomorphicUnitCohomology E M)
    (i j k x : M) (hi : x ∈ holomorphicCohomologyDomain E M u i)
    (hj : x ∈ holomorphicCohomologyDomain E M u j)
    (hk : x ∈ holomorphicCohomologyDomain E M u k) :
    (holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ *
      (holomorphicCohomologyTransition E M u j k).val ⟨x, hj, hk⟩ =
      (holomorphicCohomologyTransition E M u i k).val ⟨x, hi, hk⟩ := by
  let l := holomorphicCohomologyLocalLifts E M u
  have h := l.transition_cocycle
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)) i j k
  exact congrArg (fun s : (Sheaves.holomorphicUnitsSheaf E M).obj.obj
      (op (l.domain i ⊓ l.domain j ⊓ l.domain k)) =>
    ((Additive.toMul s :
      (Exponential.HolomorphicFunction (E := E) (M := ↥(l.domain i ⊓ l.domain j ⊓ l.domain k)))ˣ).val)
        ⟨x, ⟨hi, hj⟩, hk⟩) h

theorem holomorphicCohomologyTransition_self (u : Connecting.holomorphicUnitCohomology E M)
    (i x : M) (hi : x ∈ holomorphicCohomologyDomain E M u i) :
    (holomorphicCohomologyTransition E M u i i).val ⟨x, hi, hi⟩ = 1 := by
  have h := holomorphicCohomologyTransition_cocycle E M u i i i x hi hi hi
  apply mul_left_cancel₀ (SlitLog.holomorphicUnit_value_ne_zero
    (holomorphicCohomologyTransition E M u i i) ⟨x, hi, hi⟩)
  exact h.trans (mul_one _).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions
