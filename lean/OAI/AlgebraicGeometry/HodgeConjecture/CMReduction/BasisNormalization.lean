import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MultilinearTransfer

/-! # Basis Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BasisNormalization.CM.Construction

noncomputable section

/-! Pass from canonical embedding vectors to the chosen rank-one bases.
The product of all normalization scalars is proved nonzero. -/

open _root_.CategoryTheory
open scoped BigOperators

theorem h1Cup_basis_of_canonical
    (E : IntermediateField ℚ ℂ) [NumberField E]
    (p : ℕ) (H : Fin (p + p) → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (g : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin (p + p) → E →ₐ[ℚ] ℂ)
    (hc : IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) (p + p)
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
        ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (τ i)))) ∈
      X.variety.complexGeometricAlgebraicClasses p) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) (p + p)
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
        ((R i).complexComparison ((h i).embeddingBasis (τ i)))) ∈
      X.variety.complexGeometricAlgebraicClasses p := by
  let s : Fin (p + p) → ℂ := fun i => τ i ((h i).equivField 1)
  let u : Fin (p + p) → X.variety.complexCohomology 1 := fun i =>
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i) ((R i).complexComparison ((h i).embeddingBasis (τ i)))
  have hs (i : Fin (p + p)) : s i ≠ 0 := by
    intro hi
    have he : (h i).equivField (1 : E) = 0 := (τ i).injective (hi.trans (map_zero (τ i)).symm)
    exact one_ne_zero ((h i).equivField.injective (he.trans ((h i).equivField.map_zero).symm))
  have hv (i : Fin (p + p)) :
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i) ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (τ i))) =
        s i • u i := by
    rw [Pairs.CM.SurfaceConstruction.field_embeddingVector_normalization E (h i) (τ i), map_smul, map_smul]
  have heq := (IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) (p + p)).map_smul_univ s u
  simp only [hv] at hc
  rw [heq] at hc
  exact (X.variety.complexGeometricAlgebraicClasses p).smul_mem_iff
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)) |>.mp hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BasisNormalization.CM.Construction
