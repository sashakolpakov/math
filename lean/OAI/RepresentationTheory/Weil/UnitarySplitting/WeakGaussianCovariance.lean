import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.HaarScaling

/-! # Weak Gaussian Covariance -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianCovariance.Construction

noncomputable section

/-! Covariance of the weak Gaussian under an actual unitary Weyl lift,
with the positive Haar factor kept explicit. -/

open _root_.MeasureTheory
open scoped NNReal

theorem weakWeylGaussian_covariance
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (k : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (c : ℝ≥0) (hν : ν.map k = c • ν)
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : ∀ v, q (k v) = q v)
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (k v) (U f)) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (c : ℂ) * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q (U f).val (U h).val =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val h.val := by
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  change c • (∫ v, ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
    (U f).val (U h).val v ∂ν) = _
  rw [← integral_smul_nnreal_measure, ← hν]
  change (∫ v, ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
    (U f).val (U h).val v ∂ν.map k.toHomeomorph) = _
  rw [k.toHomeomorph.isClosedEmbedding.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change ψ (q (k v)) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
      (U f).val (U h).val (k v) = ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val v
    rw [hq, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_covariance hF ψ hc hu U hU k hcov]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianCovariance.Construction
