import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! # Local Model Inverse Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LocalModelInverseContinuity.Construction

noncomputable section

/-! A bijection whose local representatives agree with an ambient
local homeomorphism has a continuous inverse on a neighborhood. -/

open scoped _root_.Topology
open Filter Set

theorem continuous_inverse_eventually_of_local_model
    {E F A : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace A]
    (f : E ≃ F) (i : E → A) (hi : Topology.IsEmbedding i) (j : F → A) (hj : Continuous j)
    (p : OpenPartialHomeomorph A A) (x₀ : E)
    (hmodel : ∀ x, p (i x) = j (f x))
    (hlocal : ∀ᶠ y in 𝓝 (f x₀), ∃ x, i x ∈ p.source ∧ f x = y) :
    ∀ᶠ y in 𝓝 (f x₀), ContinuousAt f.symm y := by
  obtain ⟨S, hS, hSopen, hS₀⟩ := mem_nhds_iff.mp hlocal
  have he (y : F) (hy : y ∈ S) : i (f.symm y) = p.symm (j y) := by
    obtain ⟨x, hx, rfl⟩ := hS hy
    rw [f.symm_apply_apply, ← hmodel x, p.left_inv hx]
  refine Filter.mem_of_superset (hSopen.mem_nhds hS₀) (fun y hy => ?_)
  have hyT : j y ∈ p.target := by
    obtain ⟨x, hx, rfl⟩ := hS hy
    rw [← hmodel x]
    exact p.map_source hx
  apply hi.isInducing.continuousAt_iff.mpr
  have hc := (p.continuousAt_symm hyT).comp hj.continuousAt
  have hevent : (fun z => i (f.symm z)) =ᶠ[𝓝 y] (fun z => p.symm (j z)) :=
    Filter.mem_of_superset (hSopen.mem_nhds hy) (fun z hz => he z hz)
  exact hc.congr_of_eventuallyEq hevent

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LocalModelInverseContinuity.Construction
