import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Fiberwise Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseExactness

noncomputable section

/-! Fiberwise exactness lifts to an actual module sequence when its homology is finite and the outgoing image is flat. -/

open TensorProduct

universe u v w t

variable (R : Type u) [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type t} [AddCommGroup P] [Module R P]

def linearMapToKernel (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : ∀ m, g (f m) = 0) :
    M →ₗ[R] g.ker := f.codRestrict g.ker hfg

abbrev linearKernelCohomology (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : ∀ m, g (f m) = 0) :=
  g.ker ⧸ (linearMapToKernel R f g hfg).range

theorem kernel_finite_of_finite_cohomology (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : ∀ m, g (f m) = 0) [Module.Finite R M]
    [Module.Finite R (linearKernelCohomology R f g hfg)] : Module.Finite R g.ker :=
  Module.Finite.of_submodule_quotient (linearMapToKernel R f g hfg).range

theorem exact_kernel_rangeRestrict (g : N →ₗ[R] P) : Function.Exact g.ker.subtype g.rangeRestrict := by
  intro y
  constructor
  · intro hy
    exact ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext x.property

theorem kernel_flat_of_flat_range (f : M →ₗ[R] N) [Module.Flat R M] [Module.Flat R f.range] :
    Module.Flat R f.ker := by
  let : Module.Flat R f.rangeRestrict.ker := Presentations.Flat.ExactKernels.kernel_flat_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict f).symm)

theorem exact_of_residueFields_of_flat_range
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : ∀ m, g (f m) = 0)
    [Module.Flat R g.range] [Module.Finite R (g.ker ⧸ (linearMapToKernel R f g hfg).range)]
    (h : ∀ p : PrimeSpectrum R,
      Function.Exact (f.lTensor p.asIdeal.ResidueField) (g.lTensor p.asIdeal.ResidueField)) :
    Function.Exact f g := by
  let f' := linearMapToKernel R f g hfg
  have hfcomp : g.ker.subtype.comp f' = f := by
    apply LinearMap.ext
    intro m
    rfl
  have hgcomp : g.comp g.ker.subtype = 0 := by
    apply LinearMap.ext
    intro x
    exact x.property
  have hsurj : Function.Surjective f' := by
    apply ResidueFieldDetection.surjective_of_residueFields_of_finite_cokernel R f'
    intro p x
    have hinj := LinearMap.lTensor_injective_of_exact_of_flat g.rangeRestrict g.surjective_rangeRestrict
      g.ker.subtype g.ker.subtype_injective (exact_kernel_rangeRestrict R g) p.asIdeal.ResidueField
    have hx : g.lTensor p.asIdeal.ResidueField (g.ker.subtype.lTensor p.asIdeal.ResidueField x) = 0 := by
      rw [← LinearMap.lTensor_comp_apply, hgcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
    obtain ⟨y, hy⟩ := (h p _).mp hx
    refine ⟨y, hinj ?_⟩
    rw [← LinearMap.lTensor_comp_apply, hfcomp]
    exact hy
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    exact hfg x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseExactness
