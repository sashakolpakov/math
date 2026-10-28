import OAI.RepresentationTheory.Theta.Geometric.Kernel
import OAI.RepresentationTheory.Theta.Geometric.DoubleCosets

/-! # Kernel Coefficients -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelCoefficients.Spherical

noncomputable section

variable {G : Type*} [Group G] (K : Subgroup G)

theorem translate_apply (g : G) (w : SphericalGU.Spherical.CosetModule K) (c : G ⧸ K) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g w c = w (g⁻¹ • c) := by
  change Finsupp.mapDomain (fun x : G ⧸ K => g • x) w c = w (g⁻¹ • c)
  simpa only [smul_inv_smul] using
    Finsupp.mapDomain_apply_of_injective (MulAction.injective g) w (g⁻¹ • c)

theorem invariantKernel_left (w : Kernel.Spherical.invariantKernels K) (k : G) (hk : k ∈ K)
    (c : G ⧸ K) : w.val (k • c) = w.val c := by
  have h := congrArg (fun v : SphericalGU.Spherical.CosetModule K => v (k • c)) (w.property k hk)
  simpa only [translate_apply, inv_smul_smul] using h.symm

theorem doubleCoset_of_coset_smul (g h k : G) (hk : k ∈ K)
    (he : (QuotientGroup.mk h : G ⧸ K) = k • QuotientGroup.mk g) :
    DoubleCosets.Spherical.InDoubleCoset K g h := by
  have hr : h⁻¹ * (k * g) ∈ K := QuotientGroup.eq.mp he
  refine ⟨⟨k, hk⟩, ⟨(h⁻¹ * (k * g))⁻¹, K.inv_mem hr⟩, ?_⟩
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

theorem invariantKernel_doubleCoset (w : Kernel.Spherical.invariantKernels K) (g h : G)
    (hh : DoubleCosets.Spherical.InDoubleCoset K g h) :
    w.val (QuotientGroup.mk h) = w.val (QuotientGroup.mk g) := by
  obtain ⟨k, l, rfl⟩ := hh
  have he : (QuotientGroup.mk (k.val * g * l.val) : G ⧸ K) =
      k.val • QuotientGroup.mk g := by
    change (QuotientGroup.mk (k.val * g * l.val) : G ⧸ K) = QuotientGroup.mk (k.val * g)
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      K.inv_mem l.property
  rw [he]
  exact invariantKernel_left K w k.val k.property _

end

end OAI.RepresentationTheory.Theta.Geometric.KernelCoefficients.Spherical
