import OAI.Geometry.Nikodym.OpenMFDeriv

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- Taking values in an open subset does not change the manifold
derivative. This also applies to source manifolds with boundary. -/
theorem opens_hasMFDerivAt_target_iff (I : ModelWithCorners ℝ E H)
    (U : TopologicalSpace.Opens F) {f : M → U} {x : M}
    {f' : TangentSpace I x →L[ℝ] F} :
    HasMFDerivAt I 𝓘(ℝ,F) f x f' ↔
      HasMFDerivAt I 𝓘(ℝ,F) (fun y => (f y : F)) x f' := by
  constructor
  · intro hf
    refine ⟨continuous_subtype_val.continuousAt.comp hf.continuousAt,?_⟩
    exact hf.2
  · intro hf
    refine ⟨?_,?_⟩
    · exact tendsto_subtype_rng.mpr hf.continuousAt
    · exact hf.2

theorem opens_hasMFDerivAt_target (I : ModelWithCorners ℝ E H)
    (U : TopologicalSpace.Opens F) {f : M → U} {x : M}
    {f' : TangentSpace I x →L[ℝ] F}
    (hf : HasMFDerivAt I 𝓘(ℝ,F) (fun y => (f y : F)) x f') :
    HasMFDerivAt I 𝓘(ℝ,F) f x f' :=
  (opens_hasMFDerivAt_target_iff I U).mpr hf

theorem opens_mdifferentiableAt_target_iff (I : ModelWithCorners ℝ E H)
    (U : TopologicalSpace.Opens F) {f : M → U} {x : M} :
    MDifferentiableAt I 𝓘(ℝ,F) f x ↔
      MDifferentiableAt I 𝓘(ℝ,F) (fun y => (f y : F)) x := by
  constructor
  · intro hf
    exact ((opens_hasMFDerivAt_target_iff I U).mp hf.hasMFDerivAt).mdifferentiableAt
  · intro hf
    exact (opens_hasMFDerivAt_target I U hf.hasMFDerivAt).mdifferentiableAt

theorem opens_mfderiv_target (I : ModelWithCorners ℝ E H)
    (U : TopologicalSpace.Opens F) (f : M → U) (x : M) :
    mfderiv I 𝓘(ℝ,F) f x = mfderiv I 𝓘(ℝ,F) (fun y => (f y : F)) x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ,F) (fun y => (f y : F)) x
  · exact (opens_hasMFDerivAt_target I U hf.hasMFDerivAt).mfderiv
  · have hnf : ¬ MDifferentiableAt I 𝓘(ℝ,F) f x :=
      fun h => hf ((opens_mdifferentiableAt_target_iff I U).mp h)
    rw [mfderiv_zero_of_not_mdifferentiableAt hnf,mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

/-- Ordinary Fréchet derivatives compute derivatives of paths or maps
whose range is a coordinate open set. -/
theorem opens_mfderiv_target_eq_fderiv (U : TopologicalSpace.Opens F)
    (f : E → U) (x : E) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x = fderiv ℝ (fun y => (f y : F)) x := by
  rw [opens_mfderiv_target,mfderiv_eq_fderiv]

end OAI.Geometry.Nikodym
