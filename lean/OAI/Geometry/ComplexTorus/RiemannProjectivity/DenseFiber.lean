import OAI.Geometry.ComplexTorus.RiemannProjectivity.MaximalRankOf
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Dense Fiber -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.DenseFiber.Constructions.DenseFiberPreimage

noncomputable section

/-!
# RiemannProjectivity: dense base sets lift densely under finite holomorphic maps

Equal source and target dimensions turn the dense injective-derivative
locus into local inverse charts. These charts lift any base set whose
closure contains the image, and density then includes critical points.
-/

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

theorem dense_preimage {F : V → W} {U : Set V} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U)
    (hdim : Module.finrank ℂ V = Module.finrank ℂ W)
    (hfinite : ∀ y, {z : V | z ∈ U ∧ F z = y}.Finite)
    {D : Set W} (hD : ∀ x ∈ U, F x ∈ closure D) :
    U ⊆ closure (U ∩ F ⁻¹' D) := by
  have hreg : {x | x ∈ U ∧ Function.Injective (fderiv ℂ F x)} ⊆
      closure (U ∩ F ⁻¹' D) := by
    intro x hx
    have hbij : Function.Bijective (fderiv ℂ F x) :=
      ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hx.2⟩
    obtain ⟨e, hxe, he, _⟩ := FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse hU hF hx.1 hbij
    have hx' : x ∈ e.source ∩ e ⁻¹' closure D := by
      refine ⟨hxe, ?_⟩
      change e x ∈ closure D
      rw [he]
      exact hD x hx.1
    rw [e.preimage_closure, he] at hx'
    exact hU.inter_closure ⟨hx.1, hx'.2⟩
  exact (MaximalRankOf.Constructions.MaximalRank.dense_injective_points hU hF hfinite).trans
    (closure_minimal hreg isClosed_closure)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.DenseFiber.Constructions.DenseFiberPreimage
