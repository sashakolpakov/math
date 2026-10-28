import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected

/-! # Discrete Complex Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DiscreteComplexKernel

noncomputable section

/-! A complex-linear kernel contained in a discrete subgroup is zero:
each complex scalar line is connected and hence constant in that subgroup. -/

theorem complexLinear_injective_of_discrete_kernel
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] (f : V →ₗ[ℂ] W)
    (h : ∀ v, f v = 0 → v ∈ Λ) : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro v hv
  let g : ℂ → Λ := fun c => ⟨c • v, h (c • v) (by rw [map_smul, hv, smul_zero])⟩
  have hg : Continuous g := continuous_induced_rng.mpr (continuous_id.smul continuous_const)
  let : PathConnectedSpace ℂ := IsTopologicalAddGroup.pathConnectedSpace
  have hc := ((IsLocallyConstant.iff_continuous g).mpr hg).apply_eq_of_preconnectedSpace (1 : ℂ) 0
  have he := congrArg (fun x : Λ => x.val) hc
  change (1 : ℂ) • v = (0 : ℂ) • v at he
  simpa only [one_smul, zero_smul] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DiscreteComplexKernel
