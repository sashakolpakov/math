import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem opens_extChartAt_apply (U : TopologicalSpace.Opens E) (x y : U) :
    extChartAt 𝓘(ℝ,E) x y = (y : E) := rfl

@[simp] theorem opens_extChartAt_source (U : TopologicalSpace.Opens E) (x : U) :
    (extChartAt 𝓘(ℝ,E) x).source = univ := by
  ext y
  simp [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]

@[simp] theorem opens_extChartAt_target (U : TopologicalSpace.Opens E) (x : U) :
    (extChartAt 𝓘(ℝ,E) x).target = (U : Set E) := by
  ext y
  simp [extChartAt,OpenPartialHomeomorph.extend,TopologicalSpace.Opens.chartAt_eq,
    chartAt_self_eq,OpenPartialHomeomorph.subtypeRestr_def, mfld_simps]

/-- Tangent coordinates on an open subset of the model space are the
ordinary linear coordinates, even though chart inverses are totalized. -/
theorem opens_tangentCoordChange (U : TopologicalSpace.Opens E) (x y z : U) :
    tangentCoordChange 𝓘(ℝ,E) x y z = (1 : E →L[ℝ] E) := by
  have heq : (extChartAt 𝓘(ℝ,E) y ∘ (extChartAt 𝓘(ℝ,E) x).symm) =ᶠ[𝓝 (z : E)] id := by
    filter_upwards [U.isOpen.mem_nhds z.property] with w hw
    change ((extChartAt 𝓘(ℝ,E) x).symm w : E) = w
    have hr := (extChartAt 𝓘(ℝ,E) x).right_inv (by
      rw [opens_extChartAt_target]
      exact hw)
    exact hr
  rw [tangentCoordChange_def]
  have hrange : Set.range (𝓘(ℝ,E) : E → E) = univ := Set.range_id
  rw [hrange,fderivWithin_univ,opens_extChartAt_apply]
  rw [heq.fderiv_eq]
  simp only [fderiv_id]
  rfl

@[simp] theorem opens_chartAt_source (U : TopologicalSpace.Opens E) (x : U) :
    (chartAt E x).source = univ := by
  rw [← extChartAt_source (I := 𝓘(ℝ,E)),opens_extChartAt_source]

@[simp] theorem opens_tangentCore_coordChange
    (U : TopologicalSpace.Opens E) (x y z : U) :
    (tangentBundleCore 𝓘(ℝ,E) U).coordChange (achart E x) (achart E y) z =
      (1 : E →L[ℝ] E) := by
  change tangentCoordChange 𝓘(ℝ,E) x y z = _
  exact opens_tangentCoordChange U x y z

@[simp] theorem opens_tangent_symmL (U : TopologicalSpace.Opens E) (x y : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).symmL ℝ y =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core,opens_tangentCore_coordChange]
  simp

@[simp] theorem opens_tangent_continuousLinearMapAt
    (U : TopologicalSpace.Opens E) (x y : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).continuousLinearMapAt ℝ y =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core,
    opens_tangentCore_coordChange]
  simp

end OAI.Geometry.Nikodym
