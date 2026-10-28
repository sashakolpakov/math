import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerTensorDetection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels

/-! # Scalar Tower Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerFiberIsomorphism

noncomputable section

/-! A coefficient-fiber isomorphism lifts over an algebra when the
kernel and cokernel are finite and the target is flat over the coefficients. -/

open TensorProduct

universe u v w t
variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

theorem scalarTower_surjective_of_quotientTensor
    (I : Ideal R) (hI : I.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (f : M →ₗ[B] N) [Module.Finite B (N ⧸ f.range)]
    (h : Function.Surjective ((f.restrictScalars R).lTensor (R ⧸ I))) :
    Function.Surjective f := by
  let π := f.range.mkQ.restrictScalars R
  have hzero : π.comp (f.restrictScalars R) = 0 := by
    apply LinearMap.ext
    intro m
    exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨m, rfl⟩
  let : Subsingleton ((R ⧸ I) ⊗[R] (N ⧸ f.range)) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (R ⧸ I) (g := π) f.range.mkQ_surjective x
    obtain ⟨z, rfl⟩ := h y
    rw [← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  let : Subsingleton (N ⧸ f.range) := ScalarTowerTensorDetection.finiteAlgebraModule_subsingleton_of_quotientTensor I hI _
  intro y
  exact (Submodule.Quotient.mk_eq_zero f.range).mp (Subsingleton.elim (f.range.mkQ y) 0)

theorem scalarTower_bijective_of_quotientTensor_of_flat
    (I : Ideal R) (hI : I.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (f : M →ₗ[B] N) [Module.Finite B (N ⧸ f.range)] [Module.Finite B f.ker]
    [Module.Flat R N]
    (h : Function.Bijective ((f.restrictScalars R).lTensor (R ⧸ I))) :
    Function.Bijective f := by
  have hsurj := scalarTower_surjective_of_quotientTensor I hI f h.2
  let i := f.ker.subtype.restrictScalars R
  have hex : Function.Exact i (f.restrictScalars R) := by
    intro m
    constructor
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact z.property
  have hi := LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hsurj
    i f.ker.subtype_injective hex (R ⧸ I)
  have hzero : (f.restrictScalars R).comp i = 0 := by
    apply LinearMap.ext
    intro m
    exact m.property
  let : Subsingleton ((R ⧸ I) ⊗[R] f.ker) := by
    apply subsingleton_of_forall_eq 0
    intro z
    apply hi
    rw [map_zero]
    apply h.1
    rw [map_zero, ← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  let : Subsingleton f.ker := ScalarTowerTensorDetection.finiteAlgebraModule_subsingleton_of_quotientTensor I hI _
  refine ⟨LinearMap.ker_eq_bot.mp ?_, hsurj⟩
  apply bot_unique
  intro m hm
  exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : f.ker) 0)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerFiberIsomorphism
