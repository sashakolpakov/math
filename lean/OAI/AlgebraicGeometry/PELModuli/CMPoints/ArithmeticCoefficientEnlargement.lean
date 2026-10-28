import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticBaseMaps

/-! # Arithmetic Coefficient Enlargement -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticCoefficientEnlargement

noncomputable section

/-! Every finite coefficient enlargement of an existing arithmetic ring
maps into a larger localization of the same ring of integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem arithmetic_coefficients_localize
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (s : Finset B.extension.carrier) :
    letI : Algebra B.R B.extension.carrier := B.toField.toAlgebra
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ φ : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s →+* (B.withDenominator D hD).R,
        (B.withDenominator D hD).toField.comp φ =
          (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s).val.toRingHom ∧
        φ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s)) =
          ArithmeticBaseMaps.arithmeticEnlargementRingHom B D hD hdiv := by
  classical
  let : Algebra B.R B.extension.carrier := B.toField.toAlgebra
  obtain ⟨D, hD, hdiv, hcoeff⟩ := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.finite_coefficients_in_localized_integers
    B.extension.carrier (fun a : s => (a : B.extension.carrier)) B.denominator B.denominator_ne_zero
  let B' := B.withDenominator D hD
  let r := ArithmeticBaseMaps.arithmeticEnlargementRingHom B D hD hdiv
  let : Algebra B.R B'.R := r.toAlgebra
  let F : B'.R →ₐ[B.R] B.extension.carrier := {
    toRingHom := B'.toField
    commutes' a := RingHom.congr_fun (ArithmeticBaseMaps.arithmeticEnlargementRingHom_field B D hD hdiv) a }
  have hs : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s ≤ F.range := by
    apply Algebra.adjoin_le
    intro a ha
    exact hcoeff ⟨a, ha⟩
  let e := AlgEquiv.ofInjective F B'.toField_injective
  let φ := e.symm.toAlgHom.comp (Subalgebra.inclusion hs)
  refine ⟨D, hD, hdiv, φ.toRingHom, ?_, ?_⟩
  · ext a
    change ((e (e.symm (Subalgebra.inclusion hs a))) : B.extension.carrier) = (a : B.extension.carrier)
    rw [e.apply_symm_apply]
    rfl
  · ext a
    exact φ.commutes a

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticCoefficientEnlargement
