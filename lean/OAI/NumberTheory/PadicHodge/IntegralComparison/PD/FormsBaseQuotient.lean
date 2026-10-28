import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham
import Mathlib.RingTheory.AlgebraTower

/-! # Forms Base Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient

noncomputable section

/-!
# IntegralComparison: divided-power forms are unchanged by a quotient of the base

If R maps surjectively to S and the algebra action factors through S,
the constant differential relations over R and S coincide. The resulting
actual divided-power form modules are therefore canonically isomorphic.
-/

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem ordinaryRelations_le (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n ≤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply Submodule.subset_span
  cases r with
  | add v i a b => exact ⟨.add v i a b, rfl⟩
  | mul v i a b => exact ⟨.mul v i a b, rfl⟩
  | alt v i j hij hne => exact ⟨.alt v i j hij hne, rfl⟩
  | base v i r =>
    refine ⟨.base v i (algebraMap R S r), ?_⟩
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, IsScalarTower.algebraMap_apply R S A]

theorem ordinaryRelations_eq (h : Function.Surjective (algebraMap R S)) (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n := by
  apply le_antisymm (ordinaryRelations_le R S A n)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply Submodule.subset_span
  cases r with
  | add v i a b => exact ⟨.add v i a b, rfl⟩
  | mul v i a b => exact ⟨.mul v i a b, rfl⟩
  | alt v i j hij hne => exact ⟨.alt v i j hij hne, rfl⟩
  | base v i s =>
    obtain ⟨r, rfl⟩ := h s
    refine ⟨.base v i r, ?_⟩
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, IsScalarTower.algebraMap_apply R S A]

/-- The actual form modules over a base and its surjective quotient coincide. -/
def formsEquiv (h : Function.Surjective (algebraMap R S)) (I : Ideal A) (δ : DividedPowers I) (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S A I δ n := by
  unfold AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol
  rw [ordinaryRelations_eq R S A h n]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient
