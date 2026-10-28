import Mathlib

/-! # Semilinear Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange

noncomputable section

/-!
# Scalar extension of semilinear operators

When the two scalar endomorphisms commute with the algebra map, their
tensor product acts semilinearly over the larger scalar ring.
-/

open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
variable (σ : R →+* R) (τ : S →+* S)
  (h : ∀ r, τ (algebraMap R S r) = algebraMap R S (σ r))

def coefficientMap : S →ₛₗ[σ] S where
  toFun := τ
  map_add' := map_add τ
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]

def baseChange (F : M →ₛₗ[σ] M) : S ⊗[R] M →ₛₗ[τ] S ⊗[R] M where
  toFun := TensorProduct.map (coefficientMap σ τ h) F
  map_add' := map_add (TensorProduct.map (coefficientMap σ τ h) F)
  map_smul' s z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change TensorProduct.map (coefficientMap σ τ h) F (s • (a ⊗ₜ[R] x)) =
        τ s • TensorProduct.map (coefficientMap σ τ h) F (a ⊗ₜ[R] x)
      simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul]
      change τ (s * a) ⊗ₜ[R] F x = (τ s * τ a) ⊗ₜ[R] F x
      rw [map_mul]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']

theorem baseChange_tmul (F : M →ₛₗ[σ] M) (s : S) (x : M) :
    baseChange σ τ h F (s ⊗ₜ[R] x) = τ s ⊗ₜ[R] F x := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange
