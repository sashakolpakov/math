import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveDual
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # Kernel Support Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.KernelSupportIs.Construction.KernelSupport

noncomputable section

/-! The nonzero fiber-kernel locus of a map of finite projective modules is closed. -/

open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

abbrev dualCokernel (d : M →ₗ[R] N) := Module.Dual R M ⧸ d.dualMap.range

theorem tensor_cokernel (S : Type u) [CommRing S] [Algebra R S] (d : M →ₗ[R] N) :
    Nontrivial (S ⊗[R] (N ⧸ d.range)) ↔ ¬ Function.Surjective (d.baseChange S) := by
  let e := lTensor.equiv S (LinearMap.exact_map_mkQ_range d) d.range.mkQ_surjective
  rw [← e.nontrivial_congr, Submodule.Quotient.nontrivial_iff, ne_eq, LinearMap.range_eq_top]
  rfl

private theorem surjective_square {A B C D : Type*} (f : A → B) (g : C → D)
    (i : A → C) (j : B → D) (hi : Function.Bijective i) (hj : Function.Bijective j)
    (h : ∀ x, j (f x) = g (i x)) : Function.Surjective f ↔ Function.Surjective g := by
  constructor
  · intro hf y
    obtain ⟨z, rfl⟩ := hj.2 y
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨i x, (h x).symm⟩
  · intro hg y
    obtain ⟨z, hz⟩ := hg (j y)
    obtain ⟨x, rfl⟩ := hi.2 z
    exact ⟨x, hj.1 ((h x).trans hz)⟩

theorem dual_surjective_baseChange (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (d : M →ₗ[R] N) :
    Function.Surjective (d.dualMap.baseChange S) ↔ Function.Surjective (d.baseChange S).dualMap :=
  surjective_square (d.dualMap.baseChange S) (d.baseChange S).dualMap
    (ProjectiveDual.Construction.ProjectiveDualBaseChange.map (R := R) S N) (ProjectiveDual.Construction.ProjectiveDualBaseChange.map (R := R) S M)
    (ProjectiveDual.Construction.ProjectiveDualBaseChange.bijective S N) (ProjectiveDual.Construction.ProjectiveDualBaseChange.bijective S M)
    (fun x => LinearMap.congr_fun (ProjectiveDual.Construction.ProjectiveDualBaseChange.naturality S d) x)

theorem field_kernel_iff (K : Type u) [Field K] [Algebra R K]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (d : M →ₗ[R] N) :
    Nontrivial (d.baseChange K).ker ↔ Nontrivial (K ⊗[R] dualCokernel d) := by
  rw [tensor_cokernel K d.dualMap, dual_surjective_baseChange K d]
  simp only [Submodule.nontrivial_iff_ne_bot, ne_eq, LinearMap.ker_eq_bot,
    LinearMap.dualMap_surjective_iff]

theorem fiber_iff_support [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (d : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Nontrivial (d.baseChange p.asIdeal.ResidueField).ker ↔
      p ∈ Module.support R (dualCokernel d) :=
  (field_kernel_iff p.asIdeal.ResidueField d).trans
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct (M := dualCokernel d) p).symm

theorem isClosed_nontrivial_kernel [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (d : M →ₗ[R] N) :
    IsClosed {p : PrimeSpectrum R | Nontrivial (d.baseChange p.asIdeal.ResidueField).ker} := by
  have he : {p : PrimeSpectrum R | Nontrivial (d.baseChange p.asIdeal.ResidueField).ker} =
      Module.support R (dualCokernel d) := Set.ext (fiber_iff_support d)
  rw [he]
  exact Module.isClosed_support (R := R) (M := dualCokernel d)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.KernelSupportIs.Construction.KernelSupport
