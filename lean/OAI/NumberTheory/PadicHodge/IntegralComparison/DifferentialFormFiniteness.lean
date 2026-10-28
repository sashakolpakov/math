import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-! # Differential Form Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness

noncomputable section

/-!
# IntegralComparison: finite differential-form modules in arbitrary characteristic

Tensor powers of the finite Kähler module surject onto the original
differential-symbol modules. This construction requires no division by a
factorial and applies over the residue field of positive characteristic.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def tensorSymbols (n : ℕ) :
    PiTensorProduct A (fun _ : Fin n => KaehlerDifferential R A) →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  PiTensorProduct.lift (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A n)

theorem tensorSymbols_tprod (n : ℕ) (v : Fin n → A) :
    tensorSymbols R A n (PiTensorProduct.tprod A (fun i => KaehlerDifferential.D R A (v i))) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v :=
  (PiTensorProduct.lift.tprod (φ := AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A n) _).trans
    (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols_D R A n v)

def rawTensor (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n →ₗ[A] PiTensorProduct A (fun _ : Fin n => KaehlerDifferential R A) :=
  Finsupp.linearCombination A (fun v : Fin n → A =>
    PiTensorProduct.tprod A (fun i => KaehlerDifferential.D R A (v i)))

theorem tensorSymbols_rawTensor (n : ℕ) :
    (tensorSymbols R A n).comp (rawTensor R A n) = (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ := by
  apply Finsupp.lhom_ext
  intro v a
  change tensorSymbols R A n (rawTensor R A n (Finsupp.single v a)) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
  rw [rawTensor, Finsupp.linearCombination_single, map_smul, tensorSymbols_tprod, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

theorem tensorSymbols_surjective (n : ℕ) : Function.Surjective (tensorSymbols R A n) := by
  intro x
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective x
  exact ⟨rawTensor R A n a, LinearMap.congr_fun (tensorSymbols_rawTensor R A n) a⟩

theorem forms_finite [Algebra.EssFiniteType R A] (n : ℕ) : Module.Finite A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Module.Finite.of_surjective (tensorSymbols R A n) (tensorSymbols_surjective R A n)

theorem pdForms_finite [Algebra.EssFiniteType R A] (I : Ideal A) (δ : DividedPowers I) (n : ℕ) :
    Module.Finite A (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) := by
  let : Module.Finite A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) := forms_finite R A n
  exact Module.Finite.of_surjective (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ_surjective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness
