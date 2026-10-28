import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CoefficientAction
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap

/-! # Coefficient Linearity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CoefficientLinearity

noncomputable section

/-! Regular coefficients act through the actual smooth evaluation map in every degree. -/

open scoped _root_.Manifold ContDiff

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

attribute [local instance] SymbolPointwise.tangentNormedGroup SymbolPointwise.tangentNormedSpace

theorem smoothSymbol_coefficient_mul (n : ℕ) (c : A) (a : Fin (n + 1) → A) :
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a 0 (c * a 0)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ c) (hφ c) (HigherSmoothSymbols.smoothSymbol φ hφ n a) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a 0 (c * a 0)) x =
    φ c x • HigherSmoothSymbols.smoothSymbol φ hφ n a x
  simp only [SymbolPointwise.smoothSymbol_covectors, SymbolPointwise.covectors_update_zero, Function.update_self,
    map_mul, ContinuousMap.mul_apply]
  exact AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_coeff _ _ _

theorem smoothFormMap_coefficient_smul (n : ℕ) (c : A) (a : Algebraic.Forms.Form A n) :
    CochainMap.smoothFormMap φ hφ n (c • a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ c) (hφ c) (CochainMap.smoothFormMap φ hφ n a) := by
  let := FormRealization.formSectionModule φ hφ n
  let := FormRealization.formSectionSmulComm φ hφ n
  change CochainMap.smoothFormMap φ hφ n (c • a) = c • CochainMap.smoothFormMap φ hφ n a
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A n).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, smul_add, ihr, ihs]
  | single a z =>
      have hz : Finsupp.single a z = z • Algebraic.Forms.symbol A a := by
        simp [Algebraic.Forms.symbol]
      rw [hz]
      simp only [map_smul, smul_comm c z]
      apply congrArg (z • ·)
      change CochainMap.smoothFormMap φ hφ n (c • Algebraic.Forms.formSymbol A a) =
        c • CochainMap.smoothFormMap φ hφ n (Algebraic.Forms.formSymbol A a)
      rw [Algebraic.CoefficientAction.coefficient_smul_formSymbol, CochainMap.smoothFormMap_symbol, CochainMap.smoothFormMap_symbol]
      exact smoothSymbol_coefficient_mul φ hφ n c a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CoefficientLinearity
