import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OrderedCechReindexing

/-! # Cover Reindexing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverReindexing.ProjectiveCech

noncomputable section

/-! Ordered reindexing of evaluated polynomial covers preserves their actual Čech exactness. -/

open _root_.MvPolynomial

universe u v w t z

variable {σ : Type u} {κ : Type z} [LinearOrder σ] [LinearOrder κ]
variable (R : Type v) [CommRing R] (A : Type w) [CommRing A] [Algebra R A]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem polynomialCover_ordered_exact_iff (e : σ ≃o κ) (a : σ → A) (b : κ → A)
    (h : ∀ i, b (e i) = a i) (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    CoverModule.ProjectiveCech.polynomialCoverCechExactAt R A M b ℳ d q ↔ CoverModule.ProjectiveCech.polynomialCoverCechExactAt R A M a ℳ d q := by
  let f : MvPolynomial κ R →ₐ[R] MvPolynomial σ R := MvPolynomial.rename e.symm
  have hf : (MvPolynomial.aeval a).comp f = MvPolynomial.aeval b := by
    apply MvPolynomial.algHom_ext
    intro j
    change MvPolynomial.aeval a (MvPolynomial.rename e.symm (X j)) = MvPolynomial.aeval b (X j)
    rw [MvPolynomial.rename_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact (h (e.symm j)).symm.trans (congrArg b (e.apply_symm_apply j))
  let := f.toRingHom.toAlgebra
  let := CoverModule.ProjectiveCech.polynomialCoverModule R A M a
  let := CoverModule.ProjectiveCech.polynomialCoverModule R A M b
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R A M a
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R A M b
  let := CoverModule.ProjectiveCech.polynomialCover_composition_tower R A M a b f hf
  change Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := κ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q
  apply OrderedCechReindexing.ProjectiveCech.ordered_moduleCechExactAt_iff R M e
  intro i
  change MvPolynomial.rename e.symm (X (e i)) = X i
  rw [MvPolynomial.rename_X, e.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverReindexing.ProjectiveCech
