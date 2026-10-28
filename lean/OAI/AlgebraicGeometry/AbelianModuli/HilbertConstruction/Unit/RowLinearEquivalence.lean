import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitEvaluationCokernel

/-! # Row Linear Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.RowLinearEquivalence

noncomputable section

/-! Unit rescaling of rows is a linear equivalence. It preserves the
projective-cokernel conclusion of a split-surjective factorization. -/
universe u v w z
variable {R : Type u} [CommRing R] {ι : Type v}

def unitRowLinearEquiv (a : ι → Rˣ) : (ι → R) ≃ₗ[R] (ι → R) where
  toFun x i := (a i : R) * x i
  invFun x i := (↑((a i)⁻¹) : R) * x i
  left_inv x := by
    funext i
    change (↑((a i)⁻¹) : R) * ((a i : R) * x i) = x i
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext i
    change (a i : R) * ((↑((a i)⁻¹) : R) * x i) = x i
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    funext i
    exact mul_add _ _ _
  map_smul' r x := by
    funext i
    change (a i : R) * (r * x i) = r * ((a i : R) * x i)
    ring

theorem projective_cokernel_of_rescaled_split_factorization
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Projective R N]
    {V : Type z} [AddCommGroup V] [Module R V]
    (e : N ≃ₗ[R] N) (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hgf : g.comp f = LinearMap.id)
    (q : V →ₗ[R] M) (hq : Function.Surjective q) :
    Module.Projective R (N ⧸ (e.toLinearMap.comp (f.comp q)).range) := by
  have h : (g.comp e.symm.toLinearMap).comp (e.toLinearMap.comp f) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change g (e.symm (e (f x))) = x
    rw [e.symm_apply_apply]
    exact LinearMap.congr_fun hgf x
  exact SplitEvaluationCokernel.projective_cokernel_of_split_surjective_factorization
    (e.toLinearMap.comp f) (g.comp e.symm.toLinearMap) h q hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.RowLinearEquivalence
