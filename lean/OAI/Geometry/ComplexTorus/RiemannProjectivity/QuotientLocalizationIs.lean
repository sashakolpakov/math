import OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphRegular
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange

/-! # Quotient Localization Is -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.QuotientLocalizationIs.Constructions.QuotientLocalization

noncomputable section

/-! # RiemannProjectivity: quotients of localizations are localizations of the original quotient -/

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

instance quotientTower {K : Type*} [CommRing K] [Algebra K A] [Algebra K B]
    [IsScalarTower K A B] (I : Ideal A) :
    IsScalarTower K (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change Ideal.Quotient.mk _ (algebraMap K B c) =
    Ideal.Quotient.mk _ (algebraMap A B (algebraMap K A c))
  rw [IsScalarTower.algebraMap_apply K A B]

theorem isLocalization (M : Submonoid A) [IsLocalization M B] (I : Ideal A) :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) M)
      (B ⧸ I.map (algebraMap A B)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  exact IsLocalization.isLocalization_of_algEquiv _ e.symm

theorem isLocalization_away (r : A) [IsLocalization.Away r B] (I : Ideal A) :
    IsLocalization.Away (Ideal.Quotient.mk I r) (B ⧸ I.map (algebraMap A B)) := by
  have h := isLocalization (B := B) (Submonoid.powers r) I
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    Ideal.Quotient.algebraMap_eq] using h

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.QuotientLocalizationIs.Constructions.QuotientLocalization
