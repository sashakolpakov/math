import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientWord
import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyScaleProducts

/-! # Cayley Coefficient Relation -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientRelation.Construction

noncomputable section

/-! The normalized Cayley coefficient and its rational operator word
differ by a scalar with a proved positive adelic product. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate _root_.Matrix

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def cayleyCoefficientMultiplier (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N) (v : ArchimedeanAdeles.Construction.Places F) : ℝ :=
  ThetaTest.Construction.rationalLeviCoefficient F (N + N) (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D) v /
    ThetaTest.Construction.rationalLeviCoefficient F (N + N) (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D) v

theorem cayleyCoefficientMultiplier_positive_product (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N) :
    ∃ r : ℝ, 0 < r ∧ HasProd (fun v => (cayleyCoefficientMultiplier F N D v : ℂ)) (r : ℂ) := by
  obtain ⟨p, hp, hP⟩ := ThetaTest.Construction.rationalLeviCoefficient_positive_product F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D)
    (RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D))
    (RationalLevi.Construction.rationalLeviFamily_spec F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D))
  obtain ⟨q, hq, hQ⟩ := ThetaTest.Construction.rationalLeviCoefficient_positive_product F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D)
    (RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D))
    (RationalLevi.Construction.rationalLeviFamily_spec F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D))
  refine ⟨p / q, div_pos hp hq, ?_⟩
  have hh := hP.mul (hQ.inv₀ (Complex.ofReal_ne_zero.mpr hq.ne'))
  simpa only [cayleyCoefficientMultiplier, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv] using! hh

variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F, (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)
variable (W : Rational.Construction.RestrictedCover F (N + N) ψ) (hW : Rational.Construction.IsRationalFourier F (N + N) ψ W)
variable (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N) (hD : D.val = γ.val - 1)
variable (a : Rational.Construction.RestrictedCover F N ψ) (c : ArchimedeanAdeles.Construction.Places F → ℂ)
variable (hnorm : ∀ v (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N),
  (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x * conj (h.val x)
    ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) =
  c v * CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
    (Vacuum.Construction.rationalSymplecticLocal F N v γ) f.val h.val)

include hc hu hμ hW hD hnorm in
theorem rationalCayleyCoefficient_relation (v : ArchimedeanAdeles.Construction.Places F) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N)
    (φ : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N))
    (hφ : φ.val = WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ v)
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) f.val h.val)
    (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (N + N)) :
    WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ v)
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v))
      (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val h.val x =
        (c v * (cayleyCoefficientMultiplier F N D v : ℂ)) *
          (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v)
            (CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord F N ψ hc hu W D v) φ).val x := by
  let := hμ v
  let hg := CayleyScaleProducts.Construction.rationalDifference_det_local F N γ D hD v
  have hU (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
      (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) =
      c v * CorrectedNormalization.Construction.correctedWeakOpenCell (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
        (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v)))
        (Vacuum.Construction.rationalSymplecticLocal F N v γ) hg f.val h.val := by
    rw [← CorrectedNormalization.Construction.correctedWeakOpenCellValue_open _ _ _ _ hg]
    exact hnorm v f h
  have he := CayleyCoefficientFourier.Construction.normalized_weyl_coefficient_fourier (LocalKernel.Construction.completion_nondiscrete F v) (Characters.Construction.localAdditiveCharacter F ψ v)
    (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v)
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v))
    (Vacuum.Construction.rationalSymplecticLocal F N v γ) hg (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D)
    (CayleyScaleProducts.Construction.rationalDifferenceUnit_local F N γ D hD v)
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v)) (c v) hU f h x
  have hw := CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord_apply F N ψ hc hu W hW D v φ x
  rw [hφ] at hw
  rw [← Complex.ofReal_inv, CayleyScaleProducts.Construction.rational_openCellScale_inverse F N γ D hD v] at he
  simp only [Local.FunctionsMetaplectic.Construction.positionMeasure] at hw ⊢
  rw [he, hw, cayleyCoefficientMultiplier, Complex.ofReal_div]
  have hcoef : (ThetaTest.Construction.rationalLeviCoefficient F (N + N) (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D) v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ThetaTest.Construction.rationalLeviCoefficient_pos F (N + N) _ v).ne'
  field_simp [hcoef]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientRelation.Construction
