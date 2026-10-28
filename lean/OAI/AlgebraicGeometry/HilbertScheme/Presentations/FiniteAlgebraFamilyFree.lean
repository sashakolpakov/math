import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteTypeAlgebraFree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationFreeRefinement

/-! # Finite Algebra Family Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteAlgebraFamilyFree

noncomputable section

/-! A finite collection of affine coordinate algebras over a domain
becomes free over one common principal open. -/

open TensorProduct
open scoped BigOperators

universe u v w
variable (R : Type u) [CommRing R] [IsDomain R]
variable {ι : Type v} [Finite ι] (S : ι → Type w)
variable [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [∀ i, Algebra.FiniteType R (S i)]

theorem exists_generic_free_finite_algebra_family :
    ∃ s : R, s ≠ 0 ∧ ∀ i, Module.Free (Localization.Away s)
      (Localization.Away s ⊗[R] S i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose a ha hfree using fun i => FiniteTypeAlgebraFree.exists_generic_free_finiteType_algebra R (S i)
  let s := ∏ i, a i
  refine ⟨s, Finset.prod_ne_zero_iff.mpr (fun i _ => ha i), ?_⟩
  intro i
  let : Module.Free (Localization.Away (a i)) (Localization.Away (a i) ⊗[R] S i) := hfree i
  exact Principal.LocalizationFreeRefinement.principalLocalization_free_refinement (S i) (a i) s
    (Finset.dvd_prod_of_mem a (Finset.mem_univ i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteAlgebraFamilyFree
