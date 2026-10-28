import OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi

/-! # Normalization Nonvanishing -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationNonvanishing.Construction

noncomputable section

section

/-! Nonvanishing forced by the actual normalized local operators. The Haar
scale and Gaussian factors below are consequences of the supplied local
splittings, with no extra analytic-normalization hypothesis. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools.LocalAnalysis _root_.MeasureTheory
open scoped InnerProductSpace

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) (v : ArchimedeanAdeles.Construction.Places F)

include D

theorem normalized_correctedFirstFactor_nonvanishing
    (g : Integral.Construction.LocalUnitary F H.val v)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hu : u.val = g.val.val - 1) :
    CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v (Assembly.Construction.localizedUnit F d H v)
      (Assembly.Construction.localizedUnit F d K v) u ≠ 0 ∧
    ∃ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m),
      CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (TensorSpace.Construction.dualPairSymplectic (Assembly.Construction.localizedUnit F d H v).val
          (Assembly.Construction.localizedUnit F d K v).val (P.localFrame v) (g, 1)) f.val h.val ≠ 0 := by
  obtain ⟨f, hf⟩ := NontrivialLocalCharacter.Construction.local_test_one F (n * m) v
  let T := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
    (D.atPlace v (g, 1))
  have hpair : (∫ x, f.val x * star (f.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) ≠ 0 := by
    intro hz
    have hi : ⟪UnitarySplitting.Weak.Construction.testToL2 (ArchimedeanAdeles.Construction.Completion F v) (n * m) f,
        UnitarySplitting.Weak.Construction.testToL2 (ArchimedeanAdeles.Construction.Completion F v) (n * m) f⟫_ℂ = 0 := by
      rw [UnitarySplitting.Weak.Construction.testToL2_inner]
      exact hz
    have hfzero : f = 0 := UnitarySplitting.Weak.Construction.testToL2_injective (ArchimedeanAdeles.Construction.Completion F v) (n * m)
      ((inner_self_eq_zero.mp hi).trans (map_zero _).symm)
    rw [hfzero] at hf
    exact zero_ne_one hf
  have he := (D.normalization v).1 g u hu (T.symm f) f
  change (∫ x, (T (T.symm f)).val x * star (f.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) = _ at he
  rw [T.apply_symm_apply] at he
  have hprod := mul_ne_zero_iff.mp (fun hz => hpair (he.trans hz))
  exact ⟨hprod.1, T.symm f, f, hprod.2⟩

theorem normalized_selfDualMeasure_ne_zero (hN : 0 < n * m) :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v) ≠ 0 := by
  obtain ⟨u, hu⟩ := NontrivialLocalCharacter.Construction.negativeUnitary_open (ArchimedeanAdeles.Construction.rationalScalar F v d) (Assembly.Construction.localizedUnit F d H v).val
  obtain ⟨_, f, h, hx⟩ := normalized_correctedFirstFactor_nonvanishing F d hd n m H K C P D v
    (NontrivialLocalCharacter.Construction.negativeUnitary (Assembly.Construction.localizedUnit F d H v).val) u hu
  intro hμ
  exact hx (CorrectedNormalizationAnalysis.Construction.correctedWeakOpenCellValue_of_measure_zero _ _ hμ (n * m) hN _ _ _)

theorem normalized_fourierHaarScaleSquared_pos (hN : 0 < n * m) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v) := by
  have h := normalized_selfDualMeasure_ne_zero F d hd n m H K C P D v hN
  by_contra! hn
  apply h
  simp [Local.FunctionsMetaplectic.Construction.selfDualMeasure, Real.sqrt_eq_zero_of_nonpos hn]

theorem normalized_selfDualMeasure_isAddHaarMeasure (hN : 0 < n * m) :
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure :=
  FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos _ _
    (normalized_fourierHaarScaleSquared_pos F d hd n m H K C P D v hN)

theorem normalized_schrodingerQuadraticWeilConstant_ne_zero (hN : 0 < n * m) :
    CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d) ≠ 0 := by
  obtain ⟨u, hu⟩ := NontrivialLocalCharacter.Construction.negativeUnitary_open (ArchimedeanAdeles.Construction.rationalScalar F v d) (Assembly.Construction.localizedUnit F d H v).val
  have h := (normalized_correctedFirstFactor_nonvanishing F d hd n m H K C P D v
    (NontrivialLocalCharacter.Construction.negativeUnitary (Assembly.Construction.localizedUnit F d H v).val) u hu).1
  intro hz
  apply h
  simp [CorrectedNormalization.Construction.correctedFirstFactorScalar, hz, Nat.ne_of_gt hN]

theorem normalized_corrected_gaussianIntegral_ne_zero (hN : 0 < n * m) :
    Local.FunctionsMetaplectic.Construction.gaussianIntegral (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v) (-1) ≠ 0 ∧
    Local.FunctionsMetaplectic.Construction.gaussianIntegral (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d) ≠ 0 := by
  have h := normalized_schrodingerQuadraticWeilConstant_ne_zero F d hd n m H K C P D v hN
  constructor <;> intro hz <;> apply h <;>
    simp [CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant, Local.FunctionsMetaplectic.Construction.gaussianIndex, hz, Local.FunctionsMetaplectic.Construction.phase]

theorem normalized_schrodingerQuadraticWeilConstant_norm (hN : 0 < n * m) :
    ‖CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d)‖ = 1 := by
  have h := normalized_corrected_gaussianIntegral_ne_zero F d hd n m H K C P D v hN
  rw [CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant, norm_mul, Local.FunctionsMetaplectic.Construction.gaussianIndex_norm _ _ _ h.1,
    Local.FunctionsMetaplectic.Construction.gaussianIndex_norm _ _ _ h.2, mul_one]

end

/-! A nonzero normalized oscillator pairing forces the rational Cayley
difference matrix to be invertible. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate InnerProductSpace

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem rational_weak_normalization_open (a : Rational.Construction.RestrictedCover F N ψ) (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N)
    (c : ArchimedeanAdeles.Construction.Places F → ℂ)
    (hnorm : ∀ v (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N),
      (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) =
      c v * CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
        (Vacuum.Construction.rationalSymplecticLocal F N v γ) f.val h.val) : (γ.val - 1).det ≠ 0 := by
  obtain ⟨v⟩ : Nonempty (ArchimedeanAdeles.Construction.Places F) :=
    ⟨.inl (Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace F)))⟩
  obtain ⟨f, hf⟩ := NontrivialLocalCharacter.Construction.local_test_one F N v
  let T := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v)
  have hpair : (∫ x, f.val x * conj (f.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) ≠ 0 := by
    intro hz
    have hi : ⟪UnitarySplitting.Weak.Construction.testToL2 (ArchimedeanAdeles.Construction.Completion F v) N f,
        UnitarySplitting.Weak.Construction.testToL2 (ArchimedeanAdeles.Construction.Completion F v) N f⟫_ℂ = 0 := by
      rw [UnitarySplitting.Weak.Construction.testToL2_inner]
      exact hz
    have hfzero : f = 0 := UnitarySplitting.Weak.Construction.testToL2_injective (ArchimedeanAdeles.Construction.Completion F v) N
      ((inner_self_eq_zero.mp hi).trans (map_zero _).symm)
    rw [hfzero] at hf
    exact zero_ne_one hf
  have he := hnorm v (T.symm f) f
  change (∫ x, (T (T.symm f)).val x * conj (f.val x)
    ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) = _ at he
  rw [T.apply_symm_apply] at he
  intro hdet
  have hl : ((Vacuum.Construction.rationalSymplecticLocal F N v γ).val - 1).det = 0 := by
    change (γ.val.map (ArchimedeanAdeles.Construction.rationalScalar F v) - 1).det = 0
    have hm : (γ.val - 1).map (ArchimedeanAdeles.Construction.rationalScalar F v) = γ.val.map (ArchimedeanAdeles.Construction.rationalScalar F v) - 1 := by
      change (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix (γ.val - 1) = _
      rw [map_sub, map_one]
      rfl
    rw [← hm]
    exact (RingHom.map_det (ArchimedeanAdeles.Construction.rationalScalar F v) (γ.val - 1)).symm.trans (by rw [hdet, map_zero])
  rw [CorrectedNormalization.Construction.correctedWeakOpenCellValue, dite_eq_right (not_not.mpr hl), mul_zero] at he
  exact hpair he

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationNonvanishing.Construction
