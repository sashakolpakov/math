import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian

/-! # Weak Weyl Synthesis -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylSynthesis.Construction

noncomputable section

/-! Compact Weyl synthesis can be interchanged with the weak Gaussian form. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]

include hn

theorem weakWeylSynthesis_integrable
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q)
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (has : HasCompactSupport a)
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Integrable (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d =>
      ψ (q p.2) * (conj (a p.1) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
        f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu p.1 u).val p.2)) (ν.prod ν) := by
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val u.val
  have hCc : Continuous C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure F d) f u
  have hCs : HasCompactSupport C :=
    WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn (Weak.Construction.referencePositionMeasure F d) f u
  let k : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ := fun p =>
    ψ (q p.2) * (conj (a p.1) *
      (ψ (Oscillator.Construction.standardSymplecticPairing d (-p.1) p.2 / 2) * C (-p.1 + p.2)))
  have hk : Continuous k := by
    unfold k Oscillator.Construction.standardSymplecticPairing
    fun_prop
  have hks : HasCompactSupport k := by
    let T := (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => (p.1, p.1 + p.2)) ''
      (tsupport a ×ˢ tsupport C)
    have hT : IsCompact T := (has.prod hCs).image (by fun_prop)
    apply HasCompactSupport.intro hT
    intro p hp
    by_cases ha0 : a p.1 = 0
    · simp only [k, ha0, map_zero, zero_mul, mul_zero]
    · have hC0 : C (-p.1 + p.2) = 0 := by
        by_contra hne
        apply hp
        refine ⟨(p.1, -p.1 + p.2), ⟨subset_tsupport _ ha0, subset_tsupport _ hne⟩, ?_⟩
        dsimp only
        congr 1
        abel
      simp only [k, hC0, mul_zero]
  have hki := hk.integrable_of_hasCompactSupport (μ := ν.prod ν) hks
  convert hki using 1
  funext p
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hF ψ hc hu]

theorem weakWeylGaussian_synthesized_output
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q)
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (has : HasCompactSupport a)
    (f u h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hh : h.val = WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val h.val =
      ∫ v, conj (a v) * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q
        f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v u).val ∂ν := by
  have hki := weakWeylSynthesis_integrable hF ψ hc hu hn ν q hq a ha has f u
  calc
    _ = ∫ w, ∫ v, ψ (q w) * (conj (a v) *
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v u).val w) ∂ν ∂ν := by
      unfold WeakWeylGaussian.Construction.weakWeylGaussian
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        dsimp only
        rw [WeylSynthesis.Construction.weylMatrixCoefficient_synthesized_output hF ψ hc hu ν a ha
          (ha.integrable_of_hasCompactSupport has) f u h hh w, integral_const_mul]
    _ = ∫ v, ∫ w, ψ (q w) * (conj (a v) *
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v u).val w) ∂ν ∂ν :=
      (integral_integral_swap hki).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only [WeakWeylGaussian.Construction.weakWeylGaussian]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => by dsimp only; ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylSynthesis.Construction
