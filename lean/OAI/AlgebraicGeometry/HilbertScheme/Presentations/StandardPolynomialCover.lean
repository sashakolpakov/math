import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule

/-! # Standard Polynomial Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.StandardPolynomialCover.ProjectiveCech

noncomputable section

/-! Evaluating a polynomial cover at its own variables recovers the original module action and Čech complex. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

omit [LinearOrder σ] [Module R M] [IsScalarTower R (MvPolynomial σ R) M] in
theorem polynomialCover_X_module :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverModule R (MvPolynomial σ R) M X = ‹Module (MvPolynomial σ R) M› := by
  unfold Polynomial.CoverModule.ProjectiveCech.polynomialCoverModule
  rw [MvPolynomial.aeval_X_left]
  rfl

theorem polynomialCover_X_exact_iff (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial σ R) M X ℳ d q ↔
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  let Q := Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q
  let μ₀ : Module (MvPolynomial σ R) M := inferInstance
  have h (μ : Module (MvPolynomial σ R) M) (hμ : μ = μ₀) :
      let := μ
      ∀ ht : IsScalarTower R (MvPolynomial σ R) M,
        let := ht
        Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q ↔ Q := by
    subst μ
    dsimp only
    intro ht
    exact Iff.rfl
  exact h _ (polynomialCover_X_module (σ := σ) R M)
    (Polynomial.CoverModule.ProjectiveCech.polynomialCover_scalarTower R (MvPolynomial σ R) M X)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.StandardPolynomialCover.ProjectiveCech
