import OAI.Geometry.Nikodym.OpenTangent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restriction to an open set changes no local coordinate expression. -/
theorem opens_writtenInExtChartAt_eventuallyEq (U : TopologicalSpace.Opens E)
    (x : U) (f : E → F) :
    writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x (fun y : U => f y) =ᶠ[𝓝 (x:E)] f := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  change f (((extChartAt 𝓘(ℝ,E) x).symm y : U) : E) = f y
  apply congrArg f
  exact (extChartAt 𝓘(ℝ,E) x).right_inv (by
    rw [opens_extChartAt_target]
    exact hy)

/-- The ordinary derivative is the actual manifold derivative of the
restriction, in the canonical tangent coordinates of an open set. -/
theorem opens_hasMFDerivAt (U : TopologicalSpace.Opens E) (x : U)
    {f : E → F} {f' : E →L[ℝ] F} (hf : HasFDerivAt f f' (x:E)) :
    HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,F) (fun y : U => f y) x f' := by
  refine ⟨hf.continuousAt.comp continuous_subtype_val.continuousAt,?_⟩
  have h := hf.congr_of_eventuallyEq (opens_writtenInExtChartAt_eventuallyEq U x f)
  change HasFDerivWithinAt _ f' (Set.range (id : E → E)) (x:E)
  simpa only [Set.range_id,hasFDerivWithinAt_univ] using h

theorem opens_mfderiv_eq_fderiv (U : TopologicalSpace.Opens E) (x : U)
    {f : E → F} (hf : DifferentiableAt ℝ f (x:E)) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun y : U => f y) x = fderiv ℝ f (x:E) :=
  (opens_hasMFDerivAt U x hf.hasFDerivAt).mfderiv

@[simp] theorem opens_hasMFDerivAt_subtype_val (U : TopologicalSpace.Opens E) (x : U) :
    HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : U → E) x (ContinuousLinearMap.id ℝ E) :=
  opens_hasMFDerivAt U x (hasFDerivAt_id (x:E))

@[simp] theorem opens_mfderiv_subtype_val (U : TopologicalSpace.Opens E) (x : U) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : U → E) x = ContinuousLinearMap.id ℝ E :=
  (opens_hasMFDerivAt_subtype_val U x).mfderiv

theorem opens_mdifferentiable_subtype_val (U : TopologicalSpace.Opens E) :
    MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : U → E) :=
  fun x => (opens_hasMFDerivAt_subtype_val U x).mdifferentiableAt

end OAI.Geometry.Nikodym
