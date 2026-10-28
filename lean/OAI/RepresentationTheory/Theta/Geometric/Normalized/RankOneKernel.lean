import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Rank One Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.RankOneKernel

/-! Normalized sections in a rank-one source are cut out exactly by
the coordinates of the source generator's differential. -/

variable {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem rankOne_apply (e : R ≃ₗ[R] M) (a : R) : e a = a • e 1 := by
  rw [← map_smul]
  simp only [smul_eq_mul, mul_one]

theorem normalized_rankOne_kernel_iff (e : R ≃ₗ[R] M)
    (d : M →ₗ[R] N) (v : M →ₗ[R] R) (hv : IsUnit (v (e 1))) :
    (∃ m : M, d m = 0 ∧ v m = 1) ↔ d (e 1) = 0 := by
  constructor
  · rintro ⟨m, hm, hvm⟩
    have hc : v m = e.symm m * v (e 1) := by
      calc
        v m = v (e (e.symm m)) := congrArg v (e.apply_symm_apply m).symm
        _ = v (e.symm m • e 1) := congrArg v (rankOne_apply e (e.symm m))
        _ = _ := map_smul v (e.symm m) (e 1)
    have he : v (e 1) • m = e 1 := by
      apply e.symm.injective
      rw [map_smul, e.symm_apply_apply]
      change v (e 1) * e.symm m = 1
      rw [mul_comm, ← hc, hvm]
    rw [← he, map_smul, hm, smul_zero]
  · intro hd
    obtain ⟨u, hu⟩ := hv
    refine ⟨(↑u⁻¹ : R) • e 1, ?_, ?_⟩
    · rw [map_smul, hd, smul_zero]
    · rw [map_smul, ← hu]
      exact u.inv_val

theorem normalized_rankOne_kernel_unique (e : R ≃ₗ[R] M)
    (v : M →ₗ[R] R) (hv : IsUnit (v (e 1)))
    {a b : M} (ha : v a = 1) (hb : v b = 1) : a = b := by
  obtain ⟨u, hu⟩ := hv
  have he (m : M) : v m = e.symm m * (u : R) := by
    calc
      v m = v (e (e.symm m)) := congrArg v (e.apply_symm_apply m).symm
      _ = v (e.symm m • e 1) := congrArg v (rankOne_apply e (e.symm m))
      _ = _ := by rw [map_smul, ← hu]; rfl
  apply e.symm.injective
  have h := congrArg (fun z : R => z * (↑u⁻¹ : R))
    ((he a).symm.trans (ha.trans (hb.symm.trans (he b))))
  simpa only [mul_assoc, Units.mul_inv, mul_one] using h

end OAI.RepresentationTheory.Theta.Geometric.Normalized.RankOneKernel
