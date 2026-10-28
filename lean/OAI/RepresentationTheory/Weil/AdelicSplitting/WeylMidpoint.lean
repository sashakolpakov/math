import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts

/-! # Weyl Midpoint -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylMidpoint.Construction

noncomputable section

section

/-! A Weyl coefficient is the Fourier transform of its midpoint correlation. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts.LocalAnalysis

theorem weylMatrixCoefficient_midpoint_fourier
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {N : ℕ} (ψ : AddChar k ℂ)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (q p : Local.FunctionsMetaplectic.Construction.Position k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h (Sum.elim (2 • q) p) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - q) * conj (h (x + q))) (-p) := by
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient, ← integral_add_right_eq_self _ q]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ψ (∑ i, p i * ((x + q) i - (2 • q) i / 2)) *
      f (fun i => (x + q) i - (2 • q) i) * conj (h (x + q)) =
        (f (x - q) * conj (h (x + q))) * ψ (-Local.FunctionsMetaplectic.Construction.dot (-p) x)
    have hq : (fun i => (x + q) i - (2 • q) i) = x - q := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, two_smul]
      abel
    have hp : (∑ i, p i * ((x + q) i - (2 • q) i / 2)) = -Local.FunctionsMetaplectic.Construction.dot (-p) x := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, two_smul]
      congr 1
      field_simp
      ring
    rw [hq, hp]
    ring

end

/-! Rational coordinates for midpoint Fourier coefficients and correlation sums. -/

variable (F : Type) [Field F] [CharZero F] (N : ℕ)

def midpointRationalEquiv : ((Fin N → F) × (Fin N → F)) ≃ (Fin (N + N) → F) where
  toFun z i := Sum.elim (fun j => 2 * z.1 j) (fun j => -z.2 j) (finSumFinEquiv.symm i)
  invFun x := (fun j => x (finSumFinEquiv (.inl j)) / 2, fun j => -x (finSumFinEquiv (.inr j)))
  left_inv z := by
    apply Prod.ext <;> funext i
    all_goals simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_neg]
    all_goals field_simp
  right_inv x := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j
    all_goals simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_neg]
    all_goals field_simp

def correlationPairEquiv : ((Fin N → F) × (Fin N → F)) ≃ ((Fin N → F) × (Fin N → F)) where
  toFun z := (z.2 - z.1, z.2 + z.1)
  invFun z := (fun i => (z.2 i - z.1 i) / 2, fun i => (z.1 i + z.2 i) / 2)
  left_inv z := by
    apply Prod.ext <;> funext i <;> dsimp <;> field_simp <;> ring
  right_inv z := by
    apply Prod.ext <;> funext i <;> dsimp <;> field_simp <;> ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylMidpoint.Construction
