import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientRelation
import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationNonvanishing
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylTheta
import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction

/-! # Rational Weak Theta -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalWeakTheta.Construction

noncomputable section

/-! Rational weak Cayley normalization with scalar product one preserves
the positive ray of the actual theta functional. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F, (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)
variable (W : Rational.Construction.RestrictedCover F N ψ) (hW : Rational.Construction.IsRationalFourier F N ψ W)
variable (W₂ : Rational.Construction.RestrictedCover F (N + N) ψ) (hW₂ : Rational.Construction.IsRationalFourier F (N + N) ψ W₂)

include hμ in
theorem weakTheta_positionHaar (R : ℕ) (v : ArchimedeanAdeles.Construction.Places F) :
    (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure := by
  let := hμ v
  unfold Local.FunctionsMetaplectic.Construction.positionMeasure
  infer_instance

variable (a : Rational.Construction.RestrictedCover F N ψ) (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) (c : ArchimedeanAdeles.Construction.Places F → ℂ) (hcprod : HasProd c 1)
variable (hnorm : ∀ v (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N),
  (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x * conj (h.val x)
    ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) N) =
  c v * CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
    (Vacuum.Construction.rationalSymplecticLocal F N v γ) f.val h.val)

include hW₂ hcprod hnorm in
theorem rational_weak_weyl_theta (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N) (hD : D.val = γ.val - 1)
    (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ r : ℝ, 0 < r ∧
      ((f.act F N ψ a).weylCoefficients F N ψ hc hu hn (weakTheta_positionHaar F ψ hμ N) W hW h).theta F (N + N) =
        (r : ℂ) *
          ((f.weylCoefficients F N ψ hc hu hn (weakTheta_positionHaar F ψ hμ N) W hW h).act F (N + N) ψ
            (CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord F N ψ hc hu W₂ D)).theta F (N + N) := by
  obtain ⟨r, hr, hprod⟩ := CayleyCoefficientRelation.Construction.cayleyCoefficientMultiplier_positive_product F N ψ D
  have hcp : HasProd (fun v => c v * (CayleyCoefficientRelation.Construction.cayleyCoefficientMultiplier F N D v : ℂ)) (r : ℂ) := by
    simpa only [one_mul] using hcprod.mul hprod
  refine ⟨r, hr, ?_⟩
  apply RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_of_local_scalars F (N + N) _ _ _ _ hcp
  intro v x
  exact CayleyCoefficientRelation.Construction.rationalCayleyCoefficient_relation F N ψ hc hu hμ W₂ hW₂ γ D hD a c hnorm v
    (f v) (h v) ((f.weylCoefficients F N ψ hc hu hn (weakTheta_positionHaar F ψ hμ N) W hW h) v) rfl x

include hc hu hp hn hμ W hW hW₂ hcprod hnorm in
theorem rational_weak_normalization_positive : a ∈ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ := by
  have hg := NormalizationNonvanishing.Construction.rational_weak_normalization_open F N ψ a γ c hnorm
  let D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N := Matrix.GeneralLinearGroup.mkOfDetNeZero (γ.val - 1) hg
  have hD : D.val = γ.val - 1 := rfl
  let word := CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord F N ψ hc hu W₂ D
  have hword : word ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (N + N) ψ :=
    CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord_positive F N ψ hc hu W₂ hW₂ D hp
      (fun v => hn (.inl v)) (weakTheta_positionHaar F ψ hμ (N + N))
  obtain ⟨h, hnonzero⟩ := PositiveTestFamily.Construction.exists_theta_nonzero F N
  intro f
  obtain ⟨r, hr, he⟩ := rational_weak_weyl_theta F N ψ hc hu hn hμ W hW W₂ hW₂ a γ c hcprod hnorm D hD f h
  obtain ⟨ci, hci, hi⟩ := f.weylCoefficients_theta_positive F N ψ hc hu hn
    (weakTheta_positionHaar F ψ hμ N) W hW hp h
  obtain ⟨co, hco, ho⟩ := (f.act F N ψ a).weylCoefficients_theta_positive F N ψ hc hu hn
    (weakTheta_positionHaar F ψ hμ N) W hW hp h
  obtain ⟨ct, hct, ht⟩ := hword (f.weylCoefficients F N ψ hc hu hn (weakTheta_positionHaar F ψ hμ N) W hW h)
  change ((f.weylCoefficients F N ψ hc hu hn (weakTheta_positionHaar F ψ hμ N) W hW h).act F (N + N) ψ
    (CayleyCoefficientWord.Construction.rationalCayleyCoefficientWord F N ψ hc hu W₂ D)).theta F (N + N) = _ at ht
  rw [ho, ht, hi] at he
  have hz : conj (h.theta F N) ≠ 0 := star_ne_zero.mpr hnonzero
  have heq : (co : ℂ) * (f.act F N ψ a).theta F N =
      ((r * ct * ci : ℝ) : ℂ) * f.theta F N := by
    apply mul_right_cancel₀ hz
    simpa only [Complex.ofReal_mul, mul_assoc] using he
  refine ⟨r * ct * ci / co, div_pos (mul_pos (mul_pos hr hct) hci) hco, ?_⟩
  have hcon : (co : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hco.ne'
  apply mul_left_cancel₀ hcon
  rw [heq, Complex.ofReal_div]
  field_simp

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalWeakTheta.Construction
