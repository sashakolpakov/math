import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylFourier

/-! # Levi Fourier Fiber -/

namespace OAI.RepresentationTheory.Theta.Adelic.LeviFourierFiber

noncomputable section

/-! Fourier inversion of a single momentum fiber of the weak Levi
kernel. The only analytic premise is Fourier inversion on the actual
translated product test function. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (ψ : AddChar k ℂ) (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]

theorem momentum_fiber_inversion
    (f h : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (q z : Weil.Local.FunctionsMetaplectic.Construction.Position k N) (Q : Weil.Local.FunctionsMetaplectic.Construction.Position k N → k)
    (hQ : ∀ p, Q p - Weil.Local.FunctionsMetaplectic.Construction.dot p q / 2 = -Weil.Local.FunctionsMetaplectic.Construction.dot p z)
    (hInv : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - q) * conj (h x))) (-z) =
      f (z - q) * conj (h z)) :
    (∫ p, ψ (Q p) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h (Sum.elim q p) ∂μ) =
      f (z - q) * conj (h z) := by
  have he (p : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
      ψ (Q p) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h (Sum.elim q p) =
        ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot p z) * Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - q) * conj (h x)) (-p) := by
    rw [Weil.AdelicSplitting.WeylFourier.LocalAnalysis.weylMatrixCoefficient_fourier, ← mul_assoc, ← ψ.map_add_eq_mul]
    rw [← sub_eq_add_neg, hQ]
  simp_rw [he]
  rw [← hInv]
  let F : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ := Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - q) * conj (h x))
  have hn := integral_neg_eq_self (fun p => F p * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot (-z) p)) μ
  change (∫ p, ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot p z) * F (-p) ∂μ) = ∫ p, F p * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot (-z) p) ∂μ
  rw [← hn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [mul_comm]
    congr 1
    congr 1
    simp only [Weil.Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul_neg]
    exact congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => mul_comm _ _))

end

end OAI.RepresentationTheory.Theta.Adelic.LeviFourierFiber
