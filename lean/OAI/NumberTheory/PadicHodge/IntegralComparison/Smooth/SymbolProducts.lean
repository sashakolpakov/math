import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap

/-! # Symbol Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SymbolProducts.Betti

noncomputable section

/-! Multiplication of realized differential symbols is the genuine
exterior product of smooth forms, with the standard normalization. -/

open scoped BigOperators _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorTensorValue_append {p q : ℕ}
    (a : Fin p → E [⋀^Fin 1]→L[ℝ] ℂ) (b : Fin q → E [⋀^Fin 1]→L[ℝ] ℂ) :
    AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue (Fin.append a b) =
      AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue a) (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue b) := by
  funext v
  unfold AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem iteratedCovectorWedge_product {p q : ℕ} (c d : ℂ)
    (a : Fin p → E [⋀^Fin 1]→L[ℝ] ℂ) (b : Fin q → E [⋀^Fin 1]→L[ℝ] ℂ) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge p c a) (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge q d b) =
      AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge (p + q) (c * d) (Fin.append a b) := by
  ext v
  rw [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge_apply,
    covectorTensorValue_append]
  have hfun : AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge p c a) (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge q d b) =
      fun w => (c * d) * AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
        (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue a)) (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.covectorTensorValue b)) w := by
    funext w
    simp only [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct, AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth.iteratedCovectorWedge_apply]
    ring
  rw [hfun, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_smul, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_left,
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_right]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, nsmul_eq_mul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

attribute [local instance] AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.tangentNormedGroup AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.tangentNormedSpace

theorem smoothSymbol_product (p q : ℕ) (c d : A) (a : Fin p → A) (b : Fin q → A) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols.smoothSymbol φ hφ p (Fin.cons c a))
        (AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols.smoothSymbol φ hφ q (Fin.cons d b)) =
      AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols.smoothSymbol φ hφ (p + q) (Fin.cons (c * d) (Fin.append a b)) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge_apply, AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.smoothSymbol_covectors, AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.smoothSymbol_covectors,
    AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.smoothSymbol_covectors]
  simp only [Fin.cons_zero, Fin.cons_succ, map_mul, ContinuousMap.mul_apply]
  erw [iteratedCovectorWedge_product (E := E)]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (Fin.append_left _ _ j).trans
      (congrArg (fun z => AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.functionCovector φ hφ z x) (Fin.append_left a b j).symm)
  · exact (Fin.append_right _ _ j).trans
      (congrArg (fun z => AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise.functionCovector φ hφ z x) (Fin.append_right a b j).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SymbolProducts.Betti
