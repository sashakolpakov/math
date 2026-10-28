import OAI.RepresentationTheory.Theta.Adelic.IntrinsicSplittingAssembly
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell
import OAI.RepresentationTheory.Theta.Adelic.RealFirstFactorScalar
import OAI.RepresentationTheory.Theta.Adelic.RealSecondFactorScalar
import OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates
import OAI.RepresentationTheory.Theta.Adelic.RealNormWeilData
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealLeftFactor
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealRightFactor

/-! # Real Local Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealLocalSplitting

noncomputable section

/-! Construct the continuous nonsplit real local splitting in
the specified native frame, with both corrected normalization equations. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldAction
open OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.IntrinsicScaledForms OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.Intrinsic OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters
open OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter

theorem real_local_splitting
    (d : ℝ) (hd : d ≠ 0) (hns : ¬ IsSquare d) {n m : ℕ}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x))
    (hu : ∀ x : ℝ, ‖ψ x‖ = 1) (hn : ∃ x : ℝ, ψ x ≠ 1)
    (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ →ₜ* Circle)
    (hV : ∀ a : ℝˣ, χV (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ n)
    (hW : ∀ a : ℝˣ, χW (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ m)
    (bH bK : ℝˣ)
    (hbH : QuadraticNormSquareQuotient.scalarUnits d bH = Matrix.GeneralLinearGroup.det H)
    (hbK : QuadraticNormSquareQuotient.scalarUnits d bK = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (n * m) ψ (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ (n * m) ψ (s (g, 1)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bK : ℂ) ^ n *
            (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) f.val h.val) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ (n * m) ψ (s (1, g)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bH : ℂ) ^ m *
            (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) f.val h.val) := by
  let E := QuadraticLocalField.FieldModel ℝ d hns
  let σ := QuadraticLocalField.conjugation ℝ d hns
  let HM := QuadraticFieldForms.modelForm d hns H.val
  let KM := -(QuadraticFieldForms.modelForm d hns K.val)
  let c := RealFieldCoordinates.realModelFrame d hns H.val K.val P
  let C := RealFieldCharacters.realSplittingCharacters d hd hns n m χV χW hV hW
  let z := (QuadraticLocalField.algebraEquiv ℝ d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val
  have hz : z ≠ 0 := by
    intro h
    exact (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).ne_zero ((QuadraticLocalField.algebraEquiv ℝ d hns).symm.injective
      (h.trans (map_zero _).symm))
  have hσz : σ z = -z := IntrinsicOpenCell.IntrinsicScaledForms.model_delta_antifixed d hns hd
  have hHM : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ HM = HM := IntrinsicOpenCell.IntrinsicScaledForms.modelForm_hermitian d hns H.val hH
  have hKM : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ KM = -KM := by
    rw [Weil.UnitarySplitting.TracePairing.Construction.adjointMatrix_neg, IntrinsicOpenCell.IntrinsicScaledForms.modelForm_skew d hns K.val hK]
  have hHMdet : HM.det ≠ 0 := IntrinsicOpenCell.Intrinsic.modelForm_det_ne_zero d hns H
  have hKMdet : KM.det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (IntrinsicOpenCell.Intrinsic.modelForm_det_ne_zero d hns K)
  obtain ⟨vK, aK, haK⟩ := Weil.UnitarySplitting.FormScaling.Construction.skewHermitian_diagonal_units σ (QuadraticLocalField.model_finrank ℝ d hns)
    (QuadraticLocalField.conjugation_nontrivial ℝ d hns) KM hKM hKMdet z hz hσz
  obtain ⟨vH, aH, haH⟩ := Weil.UnitarySplitting.FormScaling.Construction.hermitian_diagonal_units σ (QuadraticLocalField.model_finrank ℝ d hns)
    (QuadraticLocalField.conjugation_nontrivial ℝ d hns) HM hHM hHMdet
  let μE : Measure E := Measure.addHaar
  obtain ⟨Γ, hΓ0, hΓ, hnorm⟩ := RealNormWeilData.real_norm_weil_data d hd hns ψ hc hu hn μE
  obtain ⟨sV, hsV, hfV, hcentral⟩ := IntrinsicRealLeftFactor.Intrinsic.native_real_left_factor
    σ HM KM c (RealQuadraticField.realModel_nondiscrete d hns) (continuous_algebraMap ℝ E)
    (QuadraticLocalField.model_finrank ℝ d hns) (QuadraticLocalField.conjugation_nontrivial ℝ d hns) hHM hHMdet ψ hc hu hn
    C.quadratic C.quadratic_kernel μE Γ hΓ0 hΓ z hz hσz vK aK haK
    C.skewHermitian C.skewHermitian_restriction
  obtain ⟨sW, hsW, hfW, _⟩ := IntrinsicRealRightFactor.Intrinsic.native_real_right_factor
    σ HM KM c (RealQuadraticField.realModel_nondiscrete d hns) (continuous_algebraMap ℝ E)
    (QuadraticLocalField.model_finrank ℝ d hns) (QuadraticLocalField.conjugation_nontrivial ℝ d hns) hKM hKMdet ψ hc hu hn
    C.quadratic C.quadratic_kernel μE Γ hΓ0 hΓ vH aH haH C.hermitian C.hermitian_restriction
  obtain ⟨S, hS, hSV, hSW⟩ := IntrinsicSplittingAssembly.Intrinsic.native_splitting_assembly
    σ HM KM c ψ sV sW hsV hsW hcentral
  let s := S.comp (RealFieldCoordinates.realModelPairContinuous d hns H.val K.val)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro g
    exact (hS (QuadraticFieldAction.modelPair d hns H.val K.val g)).trans (RealFieldCoordinates.realModel_dualPair_coordinates d hns H.val K.val P g)
  · intro g u hDiff f h
    let gM := QuadraticFieldForms.modelUnitary d hns H.val g
    have hpair : QuadraticFieldAction.modelPair d hns H.val K.val (g, 1) = (gM, 1) := by
      apply Prod.ext
      · rfl
      · change QuadraticFieldAction.negateUnitary σ (QuadraticFieldForms.modelForm d hns K.val) (QuadraticFieldForms.modelUnitary d hns K.val 1) = 1
        rw [map_one, map_one]
    have hsg : s (g, 1) = sV gM := by
      change S (QuadraticFieldAction.modelPair d hns H.val K.val (g, 1)) = _
      rw [hpair, hSV]
    have hcoord := RealFieldCoordinates.realModel_dualPair_coordinates d hns H.val K.val P (g, 1)
    rw [hpair] at hcoord
    have hDiffM := IntrinsicOpenCell.Intrinsic.modelUnitary_difference d hns H.val g u hDiff
    have hgen := IntrinsicOpenCell.Intrinsic.model_generic_of_difference d hns HM gM u hDiffM
    have hform := (hfV gM hgen).2 f h
    have hscalar := RealFirstFactorScalar.first_factor_scalar d hd hns ψ hc hu hn
      H K bK hbK vK aK haK χW (z • HM) (IntrinsicOpenCell.IntrinsicScaledForms.modelForm_scaled d hns (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) H).symm
      (Weil.UnitarySplitting.FormScaling.Construction.unitaryScaleForm σ HM z gM) u hDiffM Γ hΓ0 hnorm
    change (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant C.quadratic Γ hΓ0 aK n *
      Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ (z • HM) C.skewHermitian (Weil.UnitarySplitting.FormScaling.Construction.unitaryScaleForm σ HM z gM))⁻¹ : Circle) : ℂ) = _ at hscalar
    rw [hsg]
    exact hform.trans (congrArg₂ (fun (a : ℂ) (b : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (n * m)) =>
      a * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ b f.val h.val) hscalar hcoord)
  · intro g u hDiff f h
    let gM := QuadraticFieldAction.negateUnitary σ (QuadraticFieldForms.modelForm d hns K.val) (QuadraticFieldForms.modelUnitary d hns K.val g)
    have hpair : QuadraticFieldAction.modelPair d hns H.val K.val (1, g) = (1, gM) := by
      apply Prod.ext
      · exact map_one (QuadraticFieldForms.modelUnitary d hns H.val)
      · rfl
    have hsg : s (1, g) = sW gM := by
      change S (QuadraticFieldAction.modelPair d hns H.val K.val (1, g)) = _
      rw [hpair, hSW]
    have hcoord := RealFieldCoordinates.realModel_dualPair_coordinates d hns H.val K.val P (1, g)
    rw [hpair] at hcoord
    have hDiffM : gM.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val := IntrinsicOpenCell.Intrinsic.modelUnitary_difference d hns K.val g u hDiff
    have hgen := IntrinsicOpenCell.Intrinsic.model_generic_of_difference d hns KM gM u hDiffM
    have hform := (hfW gM hgen).2 f h
    have hQ : KM = QuadraticFieldForms.modelForm d hns (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (-1) K).val := by
      rw [IntrinsicOpenCell.IntrinsicScaledForms.modelForm_scaled]
      change -(QuadraticFieldForms.modelForm d hns K.val) = (QuadraticLocalField.algebraEquiv ℝ d hns).symm (-1) • QuadraticFieldForms.modelForm d hns K.val
      rw [map_neg, map_one, neg_one_smul]
    have hscalar := RealSecondFactorScalar.second_factor_scalar d hd hns ψ hc hu hn
      H K bH hbH vH aH haH χV hV KM hQ gM u hDiffM Γ hΓ0 hnorm
    change (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant C.quadratic Γ hΓ0 aH m *
      Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ KM C.hermitian gM)⁻¹ : Circle) : ℂ) = _ at hscalar
    rw [hsg]
    exact hform.trans (congrArg₂ (fun (a : ℂ) (b : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (n * m)) =>
      a * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ b f.val h.val) hscalar hcoord)

end

end OAI.RepresentationTheory.Theta.Adelic.RealLocalSplitting
