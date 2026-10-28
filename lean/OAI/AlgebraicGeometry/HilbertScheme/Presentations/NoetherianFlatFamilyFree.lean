import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedAlgebraFamilyFree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericFreenessNilpotentLift
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Noetherian Flat Family Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NoetherianFlatFamilyFree

noncomputable section

/-! Flat finite-type affine coordinate algebras over a nonzero Noetherian
base become free on a common nonempty principal open, including when the
base has nilpotents. -/

open TensorProduct

universe u v w
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [Nontrivial R]
variable {ι : Type v} [Finite ι] (S : ι → Type w)
variable [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable [∀ i, Algebra.FiniteType R (S i)] [∀ i, Module.Flat R (S i)]

theorem exists_generic_free_noetherian_flat_algebra_family :
    ∃ s : R, ¬ IsNilpotent s ∧ ∀ i, Module.Free (Localization.Away s)
      (Localization.Away s ⊗[R] S i) := by
  let N := nilradical R
  let Q := R ⧸ N
  have hN : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical R
  have hNt : N ≠ ⊤ := by
    intro h
    have hone : (1 : R) ∈ N := h ▸ Submodule.mem_top
    exact not_isNilpotent_one (mem_nilradical.mp hone)
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hNt
  let : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced N).mp
    (Ideal.radical_isRadical _)
  let : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q (Ideal.Quotient.mk N)
    Ideal.Quotient.mk_surjective
  obtain ⟨b, hb, hf⟩ := ReducedAlgebraFamilyFree.exists_generic_free_reduced_algebra_family Q (fun i => Q ⊗[R] S i)
  exact GenericFreenessNilpotentLift.generic_freeness_lift_nilpotent_reduction S N hN b hb hf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NoetherianFlatFamilyFree
