import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisSpectralOperator
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Bracket Spectral Functions -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSpectralFunctions.Construction

noncomputable section

/-! The positive spectral square root of a bracket automorphism
preserves the bracket, and its spectral logarithm is a derivation. -/

variable {L ι : Type*} [AddCommGroup L] [Module ℝ L] [Fintype ι]

theorem positive_eigenbasis_sqrt_preserves
    (B : L →ₗ[ℝ] L →ₗ[ℝ] L) (b : Module.Basis ι ℝ L) (g : L →ₗ[ℝ] L) (w : ι → ℝ)
    (hg : ∀ i, g (b i) = w i • b i) (hw : ∀ i, 0 < w i)
    (hB : ∀ x y, g (B x y) = B (g x) (g y)) :
    ∀ x y, BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.sqrt (w i)) (B x y) =
      B (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.sqrt (w i)) x)
        (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.sqrt (w i)) y) := by
  apply Bilinear.SpectralFunctions.Construction.bilinear_spectral_function_preserves B b g _ w Real.sqrt hg
    (BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis b _) hB
  intro i j
  exact Real.sqrt_mul (le_of_lt (hw i)) (w j)

omit [Fintype ι] in
theorem positive_eigenbasis_sqrt_square
    (b : Module.Basis ι ℝ L) (g : L →ₗ[ℝ] L) (w : ι → ℝ)
    (hg : ∀ i, g (b i) = w i • b i) (hw : ∀ i, 0 < w i) :
    BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.sqrt (w i)) *
      BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.sqrt (w i)) = g := by
  rw [BasisSpectralOperator.Construction.basisSpectralEnd_mul]
  apply b.ext
  intro i
  rw [BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis, Real.mul_self_sqrt (le_of_lt (hw i)), hg]

theorem positive_eigenbasis_log_derivation
    (B : L →ₗ[ℝ] L →ₗ[ℝ] L) (b : Module.Basis ι ℝ L) (g : L →ₗ[ℝ] L) (w : ι → ℝ)
    (hg : ∀ i, g (b i) = w i • b i) (hw : ∀ i, 0 < w i)
    (hB : ∀ x y, g (B x y) = B (g x) (g y)) :
    ∀ x y, BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.log (w i)) (B x y) =
      B (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.log (w i)) x) y +
        B x (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => Real.log (w i)) y) := by
  apply Bilinear.SpectralFunctions.Construction.bilinear_spectral_function_derivation B b g _ w Real.log hg
    (BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis b _) hB
  intro i j
  exact Real.log_mul (ne_of_gt (hw i)) (ne_of_gt (hw j))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSpectralFunctions.Construction
