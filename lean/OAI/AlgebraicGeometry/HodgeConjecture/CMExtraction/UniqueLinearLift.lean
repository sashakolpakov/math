import Mathlib

/-! # Unique Linear Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UniqueLinearLift

noncomputable section

/-! Uniqueness of a linear lift forces it to preserve the observed kernel. -/

theorem unique_linear_lift_kernel
    {k X V U : Type*} [Field k] [AddCommGroup X] [Module k X]
    [AddCommGroup V] [Module k V] [AddCommMonoid U] [Module k U]
    (p : V →ₗ[k] U) (θ : X →ₗ[k] V) (η : X →ₗ[k] U)
    (h : p.comp θ = η) (hu : ∀ ψ : X →ₗ[k] V, p.comp ψ = η → ψ = θ) :
    LinearMap.ker η ≤ LinearMap.ker θ := by
  intro x hx
  change θ x = 0
  by_cases hzero : x = 0
  · simp only [hzero, map_zero]
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hzero
  let correction : X →ₗ[k] V := (LinearMap.toSpanSingleton k V (θ x)).comp l
  have hc : p.comp correction = 0 := by
    apply LinearMap.ext
    intro y
    change p (l y • θ x) = 0
    rw [map_smul]
    have hpx : p (θ x) = 0 := (LinearMap.congr_fun h x).trans hx
    rw [hpx, smul_zero]
  have hnew : p.comp (θ + correction) = η := by rw [LinearMap.comp_add, h, hc, add_zero]
  have he := LinearMap.congr_fun (hu (θ + correction) hnew) x
  change θ x + l x • θ x = θ x at he
  rw [hl, one_smul] at he
  exact add_left_cancel (he.trans (add_zero (θ x)).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UniqueLinearLift
