import OAI.RepresentationTheory.Theta.Adelic.RealLocalSplitting
import OAI.RepresentationTheory.Theta.Adelic.FieldTensorTransport
import OAI.RepresentationTheory.Theta.Adelic.FieldNormalizingScalars
import OAI.RepresentationTheory.Theta.Adelic.FieldCoverNormalization
import OAI.RepresentationTheory.Weil.Local.RealFieldEq

/-! # Real Field Local Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealFieldLocalSplitting

noncomputable section

/-! The exact normalized real local splitting in every archimedean
field presentation, with the specified native forms and frame. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Weil.Local.RealFieldEq.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient
open OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport OAI.RepresentationTheory.Theta.Adelic.FieldTensorTransport
open OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport OAI.RepresentationTheory.Theta.Adelic.FieldNormalizingScalars
open OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback OAI.RepresentationTheory.Theta.Adelic.FieldCoverNormalization

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]

theorem real_field_local_splitting
    (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k)
    (hArch : ¬ ∀ j : ℕ, ‖(j : k)‖ ≤ 1)
    (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm) {n m : ℕ}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val)
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)
    (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
    (hV : ∀ a : kˣ, χV (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ n)
    (hW : ∀ a : kˣ, χW (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ m)
    (bH bK : kˣ)
    (hbH : QuadraticNormSquareQuotient.scalarUnits d bH = Matrix.GeneralLinearGroup.det H)
    (hbK : QuadraticNormSquareQuotient.scalarUnits d bK = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (g, 1)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bK : ℂ) ^ n *
            (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) f.val h.val) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (1, g)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bH : ℂ) ^ m *
            (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) f.val h.val) := by
  let : SecondCountableTopology k := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable k hnd
  let η := Weil.Local.FieldFourier.Construction.fieldCharacter e ψ
  have hηc : Continuous η := hc.comp hi
  have hηu : ∀ x : ℝ, ‖η x‖ = 1 := fun x => hu (e.symm x)
  have hηn : ∃ x : ℝ, η x ≠ 1 := by
    obtain ⟨x, hx⟩ := hn
    refine ⟨e x, ?_⟩
    change ψ (e.symm (e x)) ≠ 1
    rwa [e.symm_apply_apply]
  have hmap := (Weil.Local.RealFieldEq.Construction.realField_selfDual_normalization e he hi ψ hc hu hn).2.2
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ η).IsAddHaarMeasure :=
    (Weil.Local.RealFieldEq.Construction.realField_selfDual_normalization (RingEquiv.refl ℝ) continuous_id continuous_id η hηc hηu hηn).2.1
  have hdR : e d ≠ 0 := (map_ne_zero e).mpr hd
  have hnsR : ¬ IsSquare (e d) := by
    rintro ⟨r, hr⟩
    apply hns
    refine ⟨e.symm r, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    exact hr
  let HR := FieldCharacterTransport.Unitary.fieldFormUnit e d H
  let KR := FieldCharacterTransport.Unitary.fieldFormUnit e d K
  let PR := FieldFrameTransport.fieldFrame e d H.val K.val P
  let χVR := FieldCharacterTransport.fieldMultiplicativeCharacter e he hi d χV
  let χWR := FieldCharacterTransport.fieldMultiplicativeCharacter e he hi d χW
  let bHR := Units.map e.toMonoidHom bH
  let bKR := Units.map e.toMonoidHom bK
  have hbHR : QuadraticNormSquareQuotient.scalarUnits (e d) bHR = Matrix.GeneralLinearGroup.det HR :=
    (FieldCharacterTransport.Unitary.fieldQuadraticUnits_scalar e d bH).symm.trans
      ((congrArg (FieldCharacterTransport.Unitary.fieldQuadraticUnits e d) hbH).trans (FieldCharacterTransport.Unitary.fieldFormUnit_det e d H).symm)
  have hbKR : QuadraticNormSquareQuotient.scalarUnits (e d) bKR = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit (e d) hdR)⁻¹ ^ m * Matrix.GeneralLinearGroup.det KR := by
    have hb := congrArg (FieldCharacterTransport.Unitary.fieldQuadraticUnits e d) hbK
    rw [map_mul, map_pow, map_inv, FieldCharacterTransport.Unitary.fieldQuadraticUnits_delta, ← FieldCharacterTransport.Unitary.fieldFormUnit_det] at hb
    exact (FieldCharacterTransport.Unitary.fieldQuadraticUnits_scalar e d bK).symm.trans hb
  obtain ⟨sR, hsR, hfirstR, hsecondR⟩ := RealLocalSplitting.real_local_splitting
    (e d) hdR hnsR HR KR (FieldCharacterTransport.Unitary.fieldForm_hermitian e d H.val hH) (FieldCharacterTransport.Unitary.fieldForm_skew e d K.val hK) PR
    η hηc hηu hηn χVR χWR
    (FieldCharacterTransport.fieldMultiplicativeCharacter_restriction e he hi d χV n hV)
    (FieldCharacterTransport.fieldMultiplicativeCharacter_restriction e he hi d χW m hW) bHR bKR hbHR hbKR
  let s := (FieldCoverPullback.fieldCoverPullback e he hi (n * m) ψ).comp
    (sR.comp (FieldTensorTransport.fieldPairContinuous e he d H.val K.val))
  refine ⟨s, ?_, ?_, ?_⟩
  · intro g
    exact (FieldCoverPullback.fieldCoverPullback_projection e he hi (n * m) ψ (sR (FieldTensorTransport.fieldPairMap e d H.val K.val g))).trans
      ((congrArg (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e.symm (n * m))
        ((hsR (FieldTensorTransport.fieldPairMap e d H.val K.val g)).trans (FieldTensorTransport.dualPairSymplectic_field e d H.val K.val P g))).trans
          (Weil.Local.FieldOscillator.Construction.fieldSymplecticMap_symm e (n * m) (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g)))
  · intro g u hDiff f h
    let gR := FieldCharacterTransport.Unitary.fieldUnitaryMap e d H.val g
    have hpair : FieldTensorTransport.fieldPairMap e d H.val K.val (g, 1) = (gR, 1) := by
      apply Prod.ext
      · rfl
      · exact map_one (FieldCharacterTransport.Unitary.fieldUnitaryMap e d K.val)
    have hsg : s (g, 1) = FieldCoverPullback.fieldCoverPullback e he hi (n * m) ψ (sR (gR, 1)) := by
      change FieldCoverPullback.fieldCoverPullback e he hi (n * m) ψ (sR (FieldTensorTransport.fieldPairMap e d H.val K.val (g, 1))) = _
      rw [hpair]
      rfl
    have hcoord := FieldTensorTransport.dualPairSymplectic_field e d H.val K.val P (g, 1)
    rw [hpair] at hcoord
    let coeff := (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bK : ℂ) ^ n *
      (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)
    rw [hsg]
    refine FieldCoverNormalization.normalized_cover_pullback e he hi (n * m) ψ hmap (sR (gR, 1))
      (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) coeff ?_ f h
    intro f' h'
    have hr := hfirstR gR (FieldCharacterTransport.Unitary.fieldFormUnit e d u) (FieldCharacterTransport.Unitary.fieldUnitaryMap_difference e d H.val g u hDiff) f' h'
    have hc' := FieldNormalizingScalars.first_scalar_field hArch e he hi ψ hc hu hn d hd n m H u bK χW
    exact hr.trans (congrArg₂ (fun (z : ℂ) (a : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (n * m)) =>
      z * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) η a f'.val h'.val) hc'.symm hcoord)
  · intro g u hDiff f h
    let gR := FieldCharacterTransport.Unitary.fieldUnitaryMap e d K.val g
    have hpair : FieldTensorTransport.fieldPairMap e d H.val K.val (1, g) = (1, gR) := by
      apply Prod.ext
      · exact map_one (FieldCharacterTransport.Unitary.fieldUnitaryMap e d H.val)
      · rfl
    have hsg : s (1, g) = FieldCoverPullback.fieldCoverPullback e he hi (n * m) ψ (sR (1, gR)) := by
      change FieldCoverPullback.fieldCoverPullback e he hi (n * m) ψ (sR (FieldTensorTransport.fieldPairMap e d H.val K.val (1, g))) = _
      rw [hpair]
      rfl
    have hcoord := FieldTensorTransport.dualPairSymplectic_field e d H.val K.val P (1, g)
    rw [hpair] at hcoord
    let coeff := (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bH : ℂ) ^ m *
      (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)
    rw [hsg]
    refine FieldCoverNormalization.normalized_cover_pullback e he hi (n * m) ψ hmap (sR (1, gR))
      (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) coeff ?_ f h
    intro f' h'
    have hr := hsecondR gR (FieldCharacterTransport.Unitary.fieldFormUnit e d u) (FieldCharacterTransport.Unitary.fieldUnitaryMap_difference e d K.val g u hDiff) f' h'
    have hc' := FieldNormalizingScalars.second_scalar_field hArch e he hi ψ hc hu hn d hd n m K u bH χV
    exact hr.trans (congrArg₂ (fun (z : ℂ) (a : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (n * m)) =>
      z * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) η a f'.val h'.val) hc'.symm hcoord)

end

end OAI.RepresentationTheory.Theta.Adelic.RealFieldLocalSplitting
