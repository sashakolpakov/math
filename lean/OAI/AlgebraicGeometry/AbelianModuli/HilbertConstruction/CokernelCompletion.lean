import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCokernel
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Cokernel Completion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CokernelCompletion.CokernelCompletionKernel

noncomputable section

/-! The kernel introduced by a finite free completion, and the first
finite free replacement of a two-term flat complex. -/

universe u v w z

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {F : Type z} [AddCommGroup F] [Module R F]
variable (f : M →ₗ[R] N) (v : F →ₗ[R] N)

def inclusion : f.ker →ₗ[R] (f.coprod v).ker :=
  ((LinearMap.inl R M F).comp f.ker.subtype).codRestrict _ (by
    intro x
    change f x.val + v 0 = 0
    rw [x.property, map_zero, add_zero])

def projection : (f.coprod v).ker →ₗ[R] F :=
  (LinearMap.snd R M F).comp (f.coprod v).ker.subtype

theorem exact : Function.Exact (inclusion f v) (projection f v) := by
  intro x
  constructor
  · intro hx
    have hx0 : x.val.2 = 0 := hx
    have hf : f x.val.1 = 0 := by
      have h := x.property
      change f x.val.1 + v x.val.2 = 0 at h
      simpa only [hx0, map_zero, add_zero] using h
    refine ⟨⟨x.val.1, hf⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hx0.symm
  · rintro ⟨y, rfl⟩
    rfl

def kernelIso : (projection f v).ker ≃ₗ[R] f.ker where
  toFun x := ⟨x.val.val.1, by
    change f x.val.val.1 = 0
    have hx : x.val.val.2 = 0 := x.property
    have h := x.val.property
    change f x.val.val.1 + v x.val.val.2 = 0 at h
    simpa only [hx, map_zero, add_zero] using h⟩
  invFun x := ⟨inclusion f v x, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' r x := rfl

theorem finite [IsNoetherianRing R] [Module.Finite R F] [Module.Finite R f.ker] :
    Module.Finite R (f.coprod v).ker := by
  have : IsNoetherian R (f.coprod v).ker :=
    isNoetherian_of_range_eq_ker (inclusion f v) (projection f v)
      (LinearMap.exact_iff.mp (CokernelCompletionKernel.exact f v)).symm
  infer_instance

theorem free [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R F] [Module.Flat R F]
    [Module.Flat R M] [Module.Flat R N] [Module.Finite R f.ker]
    (h : Function.Surjective (f.coprod v)) : Module.Free R (f.coprod v).ker := by
  have : Module.Flat R (M × F) := HilbertConstruction.Flat.Kernel.FlatKernel.prod
  have : Module.Flat R (f.coprod v).ker := HilbertConstruction.Flat.Kernel.FlatKernel.flat _ h
  have : Module.Finite R (f.coprod v).ker := finite f v
  exact Module.free_of_flat_of_isLocalRing

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CokernelCompletion.CokernelCompletionKernel
