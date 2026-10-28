import Mathlib.Topology.ContinuousOn

/-! # Contracting Inverse Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseContinuity.Construction

noncomputable section

/-! An equivariant bijection has a continuous inverse everywhere if
its target contracts into a region where that inverse is continuous. -/

open scoped _root_.Topology
open Filter

theorem continuous_inverse_of_contracting_equivariance
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (f : E ≃ F) (a c : ι → E → E) (b : ι → F → F)
    (hc : ∀ t, Continuous (c t)) (hb : ∀ t, Continuous (b t))
    (hca : ∀ t x, c t (a t x) = x) (heq : ∀ t x, f (a t x) = b t (f x))
    (l : Filter ι) [NeBot l] (y₀ : F)
    (hcontract : ∀ y, Tendsto (fun t => b t y) l (𝓝 y₀))
    (hlocal : ∀ᶠ y in 𝓝 y₀, ContinuousAt f.symm y) : Continuous f.symm := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨t, ht⟩ := ((hcontract y).eventually hlocal).exists
  have hid : f.symm = fun z => c t (f.symm (b t z)) := by
    funext z
    rw [← f.apply_symm_apply z, ← heq]
    simp only [f.symm_apply_apply, hca]
  rw [hid]
  exact (hc t).continuousAt.comp (ht.comp (hb t).continuousAt)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseContinuity.Construction
