import Mathlib.RingTheory.LocalRing.Module

/-! # Residue Field Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection

noncomputable section

/-! A finite module vanishes if all its residue-field fibers vanish; the same criterion detects surjectivity with finite cokernel. -/

open TensorProduct

universe u v w

variable (R : Type u) [CommRing R]

theorem finiteModule_subsingleton_of_residueFields
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M)) : Subsingleton M := by
  apply (Module.support_eq_empty_iff (R := R) (M := M)).mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_nontrivial_iff_subsingleton.mpr (h p))
    ((Module.mem_support_iff_nontrivial_residueField_tensorProduct (M := M) p).mp hp)

theorem surjective_of_residueFields_of_finite_cokernel
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [Module.Finite R (N ⧸ f.range)]
    (h : ∀ p : PrimeSpectrum R, Function.Surjective (f.lTensor p.asIdeal.ResidueField)) :
    Function.Surjective f := by
  let : Subsingleton (N ⧸ f.range) := finiteModule_subsingleton_of_residueFields R (N ⧸ f.range) (by
    intro p
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective p.asIdeal.ResidueField f.range.mkQ_surjective x
    obtain ⟨z, rfl⟩ := h p y
    have hz : f.range.mkQ.comp f = 0 := by
      apply LinearMap.ext
      intro m
      exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨m, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, hz, LinearMap.lTensor_zero, LinearMap.zero_apply])
  intro y
  have hy : f.range.mkQ y = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero f.range).mp hy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection
