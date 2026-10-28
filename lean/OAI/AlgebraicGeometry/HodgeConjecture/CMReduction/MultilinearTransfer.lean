import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IteratedCup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-! # Multilinear Transfer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MultilinearTransfer.CM.Construction

noncomputable section

/-! Multilinearity extends geometric pullback constructions to the actual
complex spans of rational Hodge maps supplied by BalancedMonomials. -/

open _root_.CategoryTheory
open scoped TensorProduct

theorem multilinear_mem_of_span
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N]
    (F : MultilinearMap R M N) (S : ∀ i, Set (M i)) (P : Submodule R N)
    (h : ∀ v, (∀ i, v i ∈ S i) → F v ∈ P)
    (v : ∀ i, M i) (hv : ∀ i, v i ∈ Submodule.span R (S i)) : F v ∈ P := by
  let G := (P.mkQ.compMultilinearMap F).compLinearMap
    (fun i => (Submodule.span R (S i)).subtype)
  let g (i : ι) (x : {x : Submodule.span R (S i) | (x : M i) ∈ S i}) := x.val
  have hg (i : ι) : Submodule.span R (Set.range (g i)) = ⊤ := by
    simp only [g, Subtype.range_coe_subtype, Set.mem_ofPred_eq,
      Submodule.span_setOfPred_mem_eq_top]
  have hG : G = 0 := by
    apply MultilinearMap.ext_of_span_eq_top (g := fun {i} => g i) hg
    intro x
    change P.mkQ (F (fun i => ((x i).val : M i))) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (h _ (fun i => (x i).property))
  have hz := MultilinearMap.congr_fun hG (fun i => ⟨v i, hv i⟩)
  exact (Submodule.Quotient.mk_eq_zero P).mp hz

theorem h1Cup_algebraic_of_pullback_spans
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p : ℕ) (B : Fin (p + p) → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (v : ∀ i, ComplexMultiplication.WeightOne.CM.Complexification ((B i).variety.rationalCohomology 1))
    (hgeom : ∀ (g : ∀ i, A.toOver ⟶ (B i).toOver), (∀ i, IsMonHom (g i)) →
      IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p)
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (B i).toOver) 1 (v i))) ∈
        A.variety.complexGeometricAlgebraicClasses p)
    (f : ∀ i, ComplexMultiplication.WeightOne.CM.Complexification ((B i).variety.rationalCohomology 1) →ₗ[ℂ]
      ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1))
    (hf : ∀ i, f i ∈ (B i).algebraicH1PullbackSpan A) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p)
      (fun i => ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
        (f i (v i))) ∈ A.variety.complexGeometricAlgebraicClasses p := by
  let S (i : Fin (p + p)) : Set
      (ComplexMultiplication.WeightOne.CM.Complexification ((B i).variety.rationalCohomology 1) →ₗ[ℂ]
        ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :=
    {f | ∃ g : A.toOver ⟶ (B i).toOver,
      IsMonHom g ∧ (ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g).baseChange ℂ = f}
  let e (i : Fin (p + p)) :=
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1).comp
      (LinearMap.applyₗ (v i))
  let F := (IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p)).compLinearMap e
  apply multilinear_mem_of_span F S (A.variety.complexGeometricAlgebraicClasses p) ?_ f hf
  intro a ha
  choose g hg heq using ha
  have h := hgeom g hg
  change IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p)
    (fun i => ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
      (a i (v i))) ∈ _
  have hv (i : Fin (p + p)) :
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1 (a i (v i)) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (B i).toOver) 1 (v i)) := by
    rw [← heq i]
    exact Pairs.CM.SurfaceConstruction.complexification_pullback (g i) 1 (v i)
  simpa only [hv] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MultilinearTransfer.CM.Construction
