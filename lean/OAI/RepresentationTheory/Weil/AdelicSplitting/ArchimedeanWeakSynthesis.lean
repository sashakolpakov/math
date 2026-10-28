import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPhasePlancherel
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis

/-! # Archimedean Weak Synthesis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakSynthesis.Construction

noncomputable section

/-! Absolute Fubini interchange between an archimedean weak Gaussian
form and a rapidly decreasing Weyl superposition. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]

include W hW in
theorem archimedeanWeakSynthesis_integrable
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (hq : Continuous q) (a : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace k N))
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace k N × Local.FunctionsMetaplectic.Construction.PhaseSpace k N =>
      ψ (q p.2) * (conj (a p.1) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
        f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu p.1 u).val p.2)) (ν.prod ν) := by
  let C := ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW f u
  let K : Local.FunctionsMetaplectic.Construction.PhaseSpace k N × Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun p =>
    ψ (q p.2) * (conj (a p.1) * (ψ (UnitarySplitting.Oscillator.Construction.standardSymplecticPairing N (-p.1) p.2 / 2) * C (-p.1 + p.2)))
  have hK : Continuous K := by
    unfold K UnitarySplitting.Oscillator.Construction.standardSymplecticPairing
    fun_prop
  have hbound := (measurePreserving_prod_neg_add ν ν).integrable_comp_of_integrable
    ((a.integrable ν).norm.mul_prod (C.integrable ν).norm)
  have hKi : Integrable K (ν.prod ν) := by
    apply hbound.mono' hK.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖ψ (q p.2) * (conj (a p.1) *
        (ψ (UnitarySplitting.Oscillator.Construction.standardSymplecticPairing N (-p.1) p.2 / 2) * C (-p.1 + p.2)))‖ ≤
        ‖a p.1‖ * ‖C (-p.1 + p.2)‖
      simp only [norm_mul, hu, one_mul, RCLike.norm_conj, le_refl]
  convert hKi using 1
  funext p
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hk ψ hc hu]
  rfl

include W hW in
theorem archimedeanWeakGaussian_synthesized_output
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (hq : Continuous q) (a : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace k N))
    (f u h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hh : h.val = UnitarySplitting.WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val) :
    UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν q f.val h.val =
      ∫ v, conj (a v) * UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν q
        f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val ∂ν := by
  have hki := archimedeanWeakSynthesis_integrable hk ψ hc hu W hW ν q hq a f u
  calc
    _ = ∫ w, ∫ v, ψ (q w) * (conj (a v) *
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
          f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val w) ∂ν ∂ν := by
      unfold UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        dsimp only
        rw [UnitarySplitting.WeylSynthesis.Construction.weylMatrixCoefficient_synthesized_output hk ψ hc hu ν a a.continuous
          (a.integrable ν) f u h hh w, integral_const_mul]
    _ = ∫ v, ∫ w, ψ (q w) * (conj (a v) *
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
          f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val w) ∂ν ∂ν :=
      (integral_integral_swap hki).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only [UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => by dsimp only; ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakSynthesis.Construction
