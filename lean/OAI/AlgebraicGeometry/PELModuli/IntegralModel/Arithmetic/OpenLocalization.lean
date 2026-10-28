import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization

/-! # Open Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every cofinite arithmetic open in an SpreadingOut model is dominated by the
precise localized ring of integers used in IntegralModel, compatibly with the
generic point and with a prescribed nonzero level inverted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : Base.ArithmeticBaseExtension K κ)

/-- Construct a localization mapping into the actual arithmetic open.
Only an open containing the supplied generic point is needed. -/
theorem Base.ArithmeticBaseExtension.arithmetic_open_localization (U : Arithmetic.Open.ArithmeticOpen B.extension.carrier)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ b : B'.base ⟶ U.U.toScheme, B'.generic ≫ b = U.generic := by
  classical
  let z := U.generic (IsLocalRing.closedPoint B.extension.carrier)
  have hz : U.U.ι z ∈ U.U := z.property
  obtain ⟨V, ⟨a, rfl⟩, ha, hle⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hz
  have ha0 : a ≠ 0 := by
    intro heq
    subst a
    exact ha (Ideal.zero_mem _)
  obtain ⟨D, hD, hdiv, hcoeff⟩ := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.finite_coefficients_in_localized_integers
    B.extension.carrier (fun _ : Unit => (algebraMap (𝓞 B.extension.carrier) B.extension.carrier a)⁻¹)
    N hN
  let B' := B.withDenominator D hD
  obtain ⟨v, hv⟩ := hcoeff ()
  have hunit : IsUnit (algebraMap (𝓞 B.extension.carrier) B'.R a) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨v, ?_⟩
    apply ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations.integersAwayToField_injective B.extension.carrier D hD
    rw [map_mul, ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap, hv, map_one]
    exact mul_inv_cancel₀ (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha0)
  let q : B'.base ⟶ Spec (.of (𝓞 B.extension.carrier)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B'.R))
  have hq : Set.range q ⊆ (U.U : Set (Spec (.of (𝓞 B.extension.carrier)))) := by
    rintro _ ⟨p, rfl⟩
    apply hle
    change algebraMap (𝓞 B.extension.carrier) B'.R a ∉ p.asIdeal
    intro hmem
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hmem hunit)
  let b : B'.base ⟶ U.U.toScheme := IsOpenImmersion.lift U.U.ι q
    (by simpa only [Scheme.Opens.range_ι] using hq)
  have hb : b ≫ U.U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hgeneric : B'.generic ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.extension.carrier)) := by
    change Spec.map (CommRingCat.ofHom (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField B.extension.carrier D hD)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B'.R)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_comp B.extension.carrier D hD)
  refine ⟨D, hD, hdiv, b, ?_⟩
  apply (cancel_mono U.U.ι).mp
  rw [Category.assoc, hb, hgeneric, U.generic_eq]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
