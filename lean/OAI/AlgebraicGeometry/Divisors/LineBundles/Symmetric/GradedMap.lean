import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # Graded Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap.BundleCycles

noncomputable section

/-! The symmetric-algebra universal map preserves the actual grading
whenever its linear generators have degree one. -/

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : M →ₗ[R] A) (hf : ∀ m, f m ∈ 𝒜 1)

include hf in
theorem symmetricLift_mem_grade (n : ℕ) (x : SymmetricAlgebra R M) (hx : x ∈ Grading.BundleCycles.symmetricGrading R M n) :
    SymmetricAlgebra.lift f x ∈ 𝒜 n := by
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact SetLike.algebraMap_mem_graded 𝒜 r
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact (𝒜 n).add_mem ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, SymmetricAlgebra.lift_ι_apply]
    simpa only [add_comm 1 n] using SetLike.mul_mem_graded (hf a) ih

def symmetricGradedLift : Grading.BundleCycles.symmetricGrading R M →+*ᵍ 𝒜 where
  __ := (SymmetricAlgebra.lift f).toRingHom
  map_mem {n} {x} hx := symmetricLift_mem_grade 𝒜 f hf n x hx

theorem symmetricGradedLift_generator (m : M) :
    symmetricGradedLift 𝒜 f hf (SymmetricAlgebra.ι R M m) = f m :=
  SymmetricAlgebra.lift_ι_apply f m

variable {N : Type*} [AddCommMonoid N] [Module R N]

def symmetricGradedMap (g : M →ₗ[R] N) : Grading.BundleCycles.symmetricGrading R M →+*ᵍ Grading.BundleCycles.symmetricGrading R N :=
  symmetricGradedLift (Grading.BundleCycles.symmetricGrading R N) ((SymmetricAlgebra.ι R N).comp g) (fun m => by
    change SymmetricAlgebra.ι R N (g m) ∈ LinearMap.range (SymmetricAlgebra.ι R N) ^ 1
    simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R N) (g m))

theorem symmetricGradedMap_generator (g : M →ₗ[R] N) (m : M) :
    symmetricGradedMap g (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (g m) :=
  symmetricGradedLift_generator _ _ _ m

theorem symmetricGradedMap_id : symmetricGradedMap (LinearMap.id : M →ₗ[R] M) = .id (Grading.BundleCycles.symmetricGrading R M) := by
  apply GradedRingHom.coe_ringHom_injective
  have h : SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp LinearMap.id) =
      AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp LinearMap.id)
      (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M m
    exact SymmetricAlgebra.lift_ι_apply _ m
  exact congrArg AlgHom.toRingHom h

theorem symmetricGradedMap_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    (symmetricGradedMap h).comp (symmetricGradedMap g) = symmetricGradedMap (h.comp g) := by
  apply GradedRingHom.coe_ringHom_injective
  have he : (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp h)).comp
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g)) =
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp (h.comp g)) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp h)
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g) (SymmetricAlgebra.ι R M m)) =
        SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp (h.comp g)) (SymmetricAlgebra.ι R M m)
    rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply]
    exact SymmetricAlgebra.lift_ι_apply _ (g m)
  exact congrArg AlgHom.toRingHom he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap.BundleCycles
