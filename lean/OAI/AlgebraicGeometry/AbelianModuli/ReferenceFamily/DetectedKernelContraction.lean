import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Finiteness.Prod

/-! # Detected Kernel Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DetectedKernelContraction

noncomputable section

/-! A section that detects the kernel on the closed fiber constructs a
linear contraction over a local ring. Its kernel formula survives tensor
product with every module, providing the algebra for arbitrary base change. -/

open scoped TensorProduct

variable {R M N : Type} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem kernel_contraction_of_split_detector
    (d : M →ₗ[R] N) (s : M →ₗ[R] R) (u : R →ₗ[R] M)
    (hs : s.comp u = LinearMap.id) (hd : d.comp u = 0)
    (p : N × R →ₗ[R] M) (hp : p.comp (d.prod s) = LinearMap.id) :
    ∃ v : N →ₗ[R] M, v.comp d + u.comp s = LinearMap.id := by
  have hpu (r : R) : p (0, r) = u r := by
    have h := LinearMap.congr_fun hp (u r)
    change p (d (u r), s (u r)) = u r at h
    have hdu : d (u r) = 0 := LinearMap.congr_fun hd r
    have hsu : s (u r) = r := LinearMap.congr_fun hs r
    rw [hdu, hsu] at h
    exact h
  refine ⟨p.comp (LinearMap.inl R N R), ?_⟩
  apply LinearMap.ext
  intro x
  change p (d x, 0) + u (s x) = x
  rw [← hpu, ← map_add]
  simpa only [Prod.mk_add_mk, add_zero, zero_add, LinearMap.comp_apply,
    LinearMap.prod_apply, LinearMap.id_apply, Function.prod_apply] using LinearMap.congr_fun hp x

theorem exists_local_kernel_contraction
    [IsLocalRing R] [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (d : M →ₗ[R] N) (s : M →ₗ[R] R) (u : R →ₗ[R] M)
    (hs : s.comp u = LinearMap.id) (hd : d.comp u = 0)
    (hdetect : Function.Injective ((d.prod s).lTensor (IsLocalRing.ResidueField R))) :
    ∃ v : N →ₗ[R] M, v.comp d + u.comp s = LinearMap.id := by
  obtain ⟨p, hp⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (d.prod s)).mpr hdetect
  exact kernel_contraction_of_split_detector d s u hs hd p hp

theorem kernel_contraction_tensor
    (d : M →ₗ[R] N) (s : M →ₗ[R] R) (u : R →ₗ[R] M) (v : N →ₗ[R] M)
    (h : v.comp d + u.comp s = LinearMap.id)
    (A : Type) [AddCommGroup A] [Module R A]
    (x : A ⊗[R] M) (hx : d.lTensor A x = 0) :
    x = u.lTensor A (s.lTensor A x) := by
  have he := congrArg (fun f : Module.End R M => f.lTensor A) h
  rw [LinearMap.lTensor_add, LinearMap.lTensor_comp, LinearMap.lTensor_comp,
    LinearMap.lTensor_id] at he
  have hxe := LinearMap.congr_fun he x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.id_apply] using hxe.symm

theorem local_detected_kernel_after_tensor
    [IsLocalRing R] [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (d : M →ₗ[R] N) (s : M →ₗ[R] R) (u : R →ₗ[R] M)
    (hs : s.comp u = LinearMap.id) (hd : d.comp u = 0)
    (hdetect : Function.Injective ((d.prod s).lTensor (IsLocalRing.ResidueField R)))
    (A : Type) [AddCommGroup A] [Module R A]
    (x : A ⊗[R] M) (hx : d.lTensor A x = 0) :
    x = u.lTensor A (s.lTensor A x) := by
  obtain ⟨v, hv⟩ := exists_local_kernel_contraction d s u hs hd hdetect
  exact kernel_contraction_tensor d s u v hv A x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DetectedKernelContraction
