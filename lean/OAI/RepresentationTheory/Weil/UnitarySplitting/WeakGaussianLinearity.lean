import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian

/-! # Weak Gaussian Linearity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity.Construction

noncomputable section

/-! Sesquilinearity of the nonarchimedean weak Gaussian form. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))

include hF hc hu

theorem weakWeylGaussian_smul_left (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F)
    (z : ℂ) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q (z • f).val h.val =
      z * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val h.val := by
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, map_smul, map_smul,
      inner_smul_right, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu]
    ring

theorem weakWeylGaussian_smul_right (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F)
    (z : ℂ) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val (z • h).val =
      conj z * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val h.val := by
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, map_smul,
      inner_smul_left, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu]
    ring

variable [IsUltrametricDist F] [ν.IsAddHaarMeasure]
variable (hn : ∃ x : F, ψ x ≠ 1)

include hn

theorem weakWeylGaussian_add_left (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q)
    (f₁ f₂ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q (f₁ + f₂).val h.val =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f₁.val h.val +
        WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f₂.val h.val := by
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  rw [← integral_add
    (WeakWeylGaussian.Construction.weakWeylGaussian_integrable_ultra hF ψ hc hn (Weak.Construction.referencePositionMeasure F d) ν q hq f₁ h)
    (WeakWeylGaussian.Construction.weakWeylGaussian_integrable_ultra hF ψ hc hn (Weak.Construction.referencePositionMeasure F d) ν q hq f₂ h)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, map_add, map_add,
      inner_add_right, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu,
      WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu]
    ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity.Construction
