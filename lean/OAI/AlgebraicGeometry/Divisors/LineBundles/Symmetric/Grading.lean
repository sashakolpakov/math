import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading.BundleCycles

noncomputable section

/-! The actual symmetric algebra is internally graded by the powers of
its degree-one module. The decomposition is constructed by its universal property. -/

open scoped DirectSum

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

def symmetricGrading (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

instance symmetricGrading_gradedMonoid : SetLike.GradedMonoid (symmetricGrading R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

def symmetricGradedGenerator : M →ₗ[R] ⨁ n : ℕ, symmetricGrading R M n :=
  DirectSum.lof R ℕ (fun n => symmetricGrading R M n) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m => by
      change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
      simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

theorem symmetricGradedGenerator_apply (m : M) :
    symmetricGradedGenerator R M m = DirectSum.of (fun n => symmetricGrading R M n) 1
      ⟨SymmetricAlgebra.ι R M m, by
        change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
        simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m⟩ := rfl

def symmetricDecompose : SymmetricAlgebra R M →ₐ[R] ⨁ n : ℕ, symmetricGrading R M n :=
  SymmetricAlgebra.lift (symmetricGradedGenerator R M)

theorem symmetricDecompose_homogeneous (n : ℕ) (x : symmetricGrading R M n) :
    symmetricDecompose R M x = DirectSum.of (fun n => symmetricGrading R M n) n x := by
  obtain ⟨x, hx⟩ := x
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  dsimp only [Subtype.coe_mk]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, DirectSum.algebraMap_apply]
    rfl
  | add x y n hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]
    rfl
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, ih]
    change SymmetricAlgebra.lift (symmetricGradedGenerator R M) (SymmetricAlgebra.ι R M a) * _ = _
    rw [SymmetricAlgebra.lift_ι_apply, symmetricGradedGenerator_apply, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

instance symmetricGradedAlgebra : GradedAlgebra (symmetricGrading R M) :=
  GradedAlgebra.ofAlgHom _ (symmetricDecompose R M)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext m
      change DirectSum.coeAlgHom (symmetricGrading R M)
        (SymmetricAlgebra.lift (symmetricGradedGenerator R M) (SymmetricAlgebra.ι R M m)) = _
      rw [SymmetricAlgebra.lift_ι_apply, symmetricGradedGenerator_apply, DirectSum.coeAlgHom_of]
      rfl)
    (symmetricDecompose_homogeneous R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading.BundleCycles
