import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalNormalizationCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier

/-! # Corrected Scalar Products -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedScalarProducts.Construction

noncomputable section

/-! All prescribed corrected normalizing scalars have product one on
rational matrix units. The Gaussian reciprocity and character conditions
are proved separately and combined here. -/

open scoped Classical
open _root_.MeasureTheory

section

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (n m : ℕ)
variable (C : Characters.Construction.GlobalCharacters F d n m)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F C.ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure)

include hn hμ in
theorem correctedFirstFactorScalar_principal_hasProd
    (a : Rational.Construction.RestrictedCover F (n * m) C.ψ) (ha : Rational.Construction.IsRationalFourier F (n * m) C.ψ a)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (u : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ) :
    HasProd (fun v => CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v
      (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1 := by
  have hW := WeightedGaussianReciprocity.Construction.schrodingerWeil_rational_inverse_power_hasProd F (n * m) C.ψ C.ψ_continuous C.ψ_unitary
    C.ψ_principal hn hμ d hd a ha
  have hC := (RationalNormalizationCharacters.Construction.firstFactorCharacter_principal_hasProd F d hd n m C H K u).map Circle.coeHom continuous_subtype_val
  have h := hW.mul hC
  simpa only [RationalNormalizationCharacters.Construction.correctedFirstFactorScalar_eq_character, Circle.coeHom_apply, Circle.coe_one, one_mul] using! h

include hd hn hμ in
theorem correctedSecondFactorScalar_principal_hasProd
    (a : Rational.Construction.RestrictedCover F (n * m) C.ψ) (ha : Rational.Construction.IsRationalFourier F (n * m) C.ψ a)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (u : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ) :
    HasProd (fun v => CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v
      (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1 := by
  have hW := WeightedGaussianReciprocity.Construction.schrodingerWeil_rational_inverse_power_hasProd F (n * m) C.ψ C.ψ_continuous C.ψ_unitary
    C.ψ_principal hn hμ d hd a ha
  have hC := (RationalNormalizationCharacters.Construction.secondFactorCharacter_principal_hasProd F d n m C H K u).map Circle.coeHom continuous_subtype_val
  have h := hW.mul hC
  simpa only [RationalNormalizationCharacters.Construction.correctedSecondFactorScalar_eq_character, Circle.coeHom_apply, Circle.coe_one, one_mul] using! h

end

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hns hN hH hK D in
theorem normalized_corrected_scalar_products :
    (∀ u : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ,
      HasProd (fun v => CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v
        (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1) ∧
    (∀ u : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ,
      HasProd (fun v => CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v
        (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1) := by
  have hn := NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D
  have hμ (v : ArchimedeanAdeles.Construction.Places F) : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure := by
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure :=
      NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D v hN
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  let a := RationalFourier.Construction.rationalFourierFamily F d hd hns n m hN H K hH hK C P D
  have ha := RationalFourier.Construction.rationalFourierFamily_spec F d hd hns n m hN H K hH hK C P D
  exact ⟨correctedFirstFactorScalar_principal_hasProd F d hd n m C hn hμ a ha H K,
    correctedSecondFactorScalar_principal_hasProd F d hd n m C hn hμ a ha H K⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedScalarProducts.Construction
