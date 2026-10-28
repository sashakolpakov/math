import OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameSectionRestriction

/-! # Frame Generator Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FrameGeneratorCoordinates.RingedModules

noncomputable section

/-! A semilinear restriction map preserves frame coordinates once it preserves
the actual frame generator. -/

theorem linearFrame_restrict {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (σ : R →+* S) (r : M →ₛₗ[σ] N) (e : M ≃ₗ[R] R) (f : N ≃ₗ[S] S)
    (h : r (e.symm 1) = f.symm 1) (m : M) : f (r m) = σ (e m) := by
  have hm : m = e m • e.symm 1 := by
    rw [← e.symm.map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  calc
    f (r m) = f (r (e m • e.symm 1)) := congrArg (fun x => f (r x)) hm
    _ = σ (e m) := by
      rw [r.map_smulₛₗ, h, f.map_smul, f.apply_symm_apply, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.Comparison.Betti.FrameGeneratorCoordinates.RingedModules
