import OAI.Geometry.Nikodym.SmoothMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

def riemannianPullbackForm (f : E → M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem riemannianPullbackForm_apply (f : E → M) (y u v : E) :
    riemannianPullbackForm f y u v =
      ⟪mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y u,mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y v⟫ := rfl

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] in
theorem contMDiffOn_mfderiv_const_vector {s : Set E} (hs : IsOpen s)
    {f : E → M} (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f s) (u : E) :
    ContMDiffOn 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun y => (⟨f y,mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y u⟩ : TangentBundle 𝓘(ℝ,E) M)) s := by
  have hsec : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun y => (⟨y,u⟩ : TangentBundle 𝓘(ℝ,E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have htan := hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have h := htan.comp hsec.contMDiffOn (show MapsTo
      (fun y => (⟨y,u⟩ : TangentBundle 𝓘(ℝ,E) E)) s
      (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy => hy)
  apply h.congr
  intro y hy
  simp only [Function.comp_def,tangentMapWithin,mfderivWithin_of_mem_nhds (hs.mem_nhds hy)]

theorem contDiffOn_riemannianPullbackForm {s : Set E} (hs : IsOpen s)
    {f : E → M} (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f s) :
    ContDiffOn ℝ ∞ (riemannianPullbackForm f) s := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have h := ContMDiffOn.inner_bundle
    (E := fun x : M => TangentSpace 𝓘(ℝ,E) x) (F := E)
    (b := f)
    (v := fun y => mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y u)
    (w := fun y => mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y v)
    (contMDiffOn_mfderiv_const_vector hs hf u)
    (contMDiffOn_mfderiv_const_vector hs hf v)
  exact h.contDiffOn

def riemannianPullbackOperator (f : E → M) (y : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (riemannianPullbackForm f y)

omit [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem inner_riemannianPullbackOperator (f : E → M) (y u v : E) :
    ⟪riemannianPullbackOperator f y u,v⟫ = riemannianPullbackForm f y u v := by
  exact InnerProductSpace.toDual_symm_apply

theorem contDiffOn_riemannianPullbackOperator {s : Set E} (hs : IsOpen s)
    {f : E → M} (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f s) :
    ContDiffOn ℝ ∞ (riemannianPullbackOperator f) s := by
  apply contDiffOn_clm_apply.mpr
  intro u
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    ((contDiffOn_riemannianPullbackForm hs hf).clm_apply contDiffOn_const)

end OAI.Geometry.Nikodym
