import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyMatrixBaseChange
import OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity

/-! # Cayley Coefficient Word -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientWord.Construction

noncomputable section

/-! The rational generator word acting on doubled Weyl coefficient space. -/

open scoped Classical _root_.NumberField _root_.Matrix

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (a : Rational.Construction.RestrictedCover F (N + N) ψ) (ha : Rational.Construction.IsRationalFourier F (N + N) ψ a)
variable (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N)

def rationalCayleyCoefficientWord : Rational.Construction.RestrictedCover F (N + N) ψ :=
  QuadraticGenerators.Construction.rationalQuadraticFamily F (N + N) ψ hu hc (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic F N D) *
    RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D) * a *
      QuadraticGenerators.Construction.rationalQuadraticFamily F (N + N) ψ hu hc (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic F N D)

include ha in
theorem rationalCayleyCoefficientWord_apply (v : ArchimedeanAdeles.Construction.Places F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (N + N)) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v)
      (rationalCayleyCoefficientWord F N ψ hc hu a D v) f).val x =
      (ThetaTest.Construction.rationalLeviCoefficient F (N + N) (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D) v : ℂ) *
        Characters.Construction.localAdditiveCharacter F ψ v
          (Local.FunctionsMetaplectic.Construction.quadratic (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D)).val x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v)
          (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v))
          (Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v)
            (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D)).val f.val)
          ((CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D))⁻¹.val *ᵥ x) := by
  let O := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v)
  let B := CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic F N D
  let A := CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D
  let Q := QuadraticGenerators.Construction.rationalQuadraticFamily F (N + N) ψ hu hc B
  let L := RationalLevi.Construction.rationalLeviFamily F (N + N) ψ A
  have hcomp (u w : Vacuum.Construction.CoverAt F (N + N) ψ v) (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N)) :
      O (u * w) g = O u (O w g) := by rw [map_mul]; rfl
  have hq (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N)) :
      (O (Q v) g).val = Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v)
        (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D)).val g.val := by
    funext y
    have hh := (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F (N + N) ψ hu hc B).2 v g y
    change (O (Q v) g).val y = Characters.Construction.localAdditiveCharacter F ψ v (Local.FunctionsMetaplectic.Construction.quadratic (B.val.map (ArchimedeanAdeles.Construction.rationalScalar F v)) y) * g.val y at hh
    rw [show B.val.map (ArchimedeanAdeles.Construction.rationalScalar F v) =
      (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D)).val from
      CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic_map N (ArchimedeanAdeles.Construction.rationalScalar F v) D] at hh
    exact hh
  have hl (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N)) (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (N + N)) :
      (O (L v) g).val y = (ThetaTest.Construction.rationalLeviCoefficient F (N + N) A v : ℂ) *
        g.val ((CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D))⁻¹.val *ᵥ y) := by
    have hh := (RationalLevi.Construction.rationalLeviFamily_spec F (N + N) ψ A).2 v g y
    change (O (L v) g).val y = _ at hh
    rw [Local.FunctionsMetaplectic.Construction.substitutionOperator_apply] at hh
    have he : Rational.Construction.localizeLinear F (N + N) A v =
        CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear (ArchimedeanAdeles.Construction.Completion F v) N (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D) :=
      CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear_map N (ArchimedeanAdeles.Construction.rationalScalar F v) D
    rw [he] at hh
    change (O (L v) g).val y = _
    convert hh using 1
    rw [ThetaTest.Construction.rationalLeviCoefficient, he, Complex.ofReal_inv]
  have hw (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (N + N)) : (O (a v) g).val =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v)) g.val := funext (ha.2 v g)
  change (O (((Q v * L v) * a v) * Q v) f).val x = _
  simp only [hcomp, hq, Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, hl, hw]
  ring

include ha in
theorem rationalCayleyCoefficientWord_positive
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (hn : ∀ v : NumberField.InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
    (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (N + N) (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure) :
    rationalCayleyCoefficientWord F N ψ hc hu a D ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (N + N) ψ := by
  let P := TestFamilyAction.Construction.positiveThetaSubgroup F (N + N) ψ
  have hQ : QuadraticGenerators.Construction.rationalQuadraticFamily F (N + N) ψ hu hc (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic F N D) ∈ P :=
    GaussianOneReciprocity.Construction.rationalQuadratic_mem_positiveThetaSubgroup F (N + N) ψ hc hu hp (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic F N D)
  have hL : RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D) ∈ P := by
    obtain ⟨c, hc, ht⟩ := ThetaTest.Construction.theta_rational_levi_positive F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D)
      (RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D))
      (RationalLevi.Construction.rationalLeviFamily_spec F (N + N) ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear F N D))
    exact fun f => ⟨c, hc, ht f⟩
  have hW : a ∈ P := ThetaFourierPositive.Construction.rationalFourier_mem_positiveThetaSubgroup F (N + N) ψ hc hu hp hn
    (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha
  exact P.mul_mem (P.mul_mem (P.mul_mem hQ hL) hW) hQ

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientWord.Construction
