import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteAlgebraFamilyFree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedPrincipalDomain
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPrincipalFreeRefinement

/-! # Reduced Algebra Family Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedAlgebraFamilyFree

noncomputable section

/-! A finite family of finite-type algebras over a nonzero reduced
Noetherian ring becomes free on a common nonempty principal open. -/

open TensorProduct

universe u v w
variable (R : Type u) [CommRing R] [IsReduced R] [IsNoetherianRing R] [Nontrivial R]
variable {ι : Type v} [Finite ι] (S : ι → Type w)
variable [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [∀ i, Algebra.FiniteType R (S i)]

theorem exists_generic_free_reduced_algebra_family :
    ∃ s : R, ¬ IsNilpotent s ∧ ∀ i, Module.Free (Localization.Away s)
      (Localization.Away s ⊗[R] S i) := by
  obtain ⟨a, _, hA⟩ := ReducedPrincipalDomain.exists_reduced_principal_domain (R := R)
  let A := Localization.Away a
  let : IsDomain A := hA
  obtain ⟨t, ht, hfree⟩ := FiniteAlgebraFamilyFree.exists_generic_free_finite_algebra_family A (fun i => A ⊗[R] S i)
  obtain ⟨r, har, φ, hφ, hu⟩ := IteratedPrincipalFreeRefinement.principal_domain_element_refinement a t ht
  let C := Localization.Away (a * r)
  let D := Localization.Away t
  let : Algebra A C := φ.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)
  let ψ : D →+* C := IsLocalization.Away.lift t hu
  have hψ (x : A) : ψ (algebraMap A D x) = φ x := IsLocalization.Away.lift_eq t hu x
  let : Algebra D C := ψ.toAlgebra
  let : IsScalarTower R D C := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap R C x = ψ (algebraMap R D x)
    rw [IsScalarTower.algebraMap_apply R A D, hψ, hφ])
  refine ⟨a * r, har, ?_⟩
  intro i
  let : Module.Free D (D ⊗[A] (A ⊗[R] S i)) := hfree i
  let : Module.Free D (D ⊗[R] S i) := Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange R A D D (S i))
  exact Principal.LocalizationFreeRefinement.free_baseChange_along_tower (S i) D C

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedAlgebraFamilyFree
