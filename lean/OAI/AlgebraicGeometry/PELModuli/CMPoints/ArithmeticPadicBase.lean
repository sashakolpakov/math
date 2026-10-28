import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointSpecialization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticBaseMaps

/-! # Arithmetic Padic Base -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPadicBase

/-! Actual q-adic integral and residue maps of the constructed
arithmetic bases, compatible with their specified field embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : IntegralModel.Base.ArithmeticBaseExtension K κ) {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice B.extension.carrier B.embedding q) (hcop : q.Coprime B.denominator)

include hcop in
theorem arithmeticPadic_denominator_isUnit :
    IsUnit (j.integralEmbedding (B.denominator : NumberField.RingOfIntegers B.extension.carrier)) := by
  rw [map_natCast, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact hcop

def arithmeticPadicBaseMap : B.R →+* PadicInt q :=
  IsLocalization.Away.lift (B.denominator : NumberField.RingOfIntegers B.extension.carrier)
    (arithmeticPadic_denominator_isUnit B j hcop)

theorem arithmeticPadicBaseMap_integers :
    (arithmeticPadicBaseMap B j hcop).comp
      (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R) = j.integralEmbedding :=
  IsLocalization.Away.lift_comp _ (arithmeticPadic_denominator_isUnit B j hcop)

theorem arithmeticPadicBaseMap_generic :
    PadicInt.Coe.ringHom.comp (arithmeticPadicBaseMap B j hcop) =
      (j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)).comp B.toField := by
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (B.denominator : NumberField.RingOfIntegers B.extension.carrier))
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun (arithmeticPadicBaseMap_integers B j hcop) a
  have hb : B.toField (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R a) =
      (a : B.extension.carrier) := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ a
  change (arithmeticPadicBaseMap B j hcop (algebraMap _ B.R a) : Padic q) =
    j.completion (NumberField.FinitePlace.embedding j.prime (B.toField (algebraMap _ B.R a)))
  exact (congrArg (PadicInt.Coe.ringHom : PadicInt q →+* Padic q) ha).trans
    ((RingHom.congr_fun j.integral_compatibility a).trans
      (congrArg (j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)) hb.symm))

def arithmeticResidue : B.R →+* ZMod q :=
  PadicInt.toZMod.comp (arithmeticPadicBaseMap B j hcop)

end AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPadicBase

namespace AlgebraicGeometry.PELModuli.CMPoints

/-! Residue maps on every constructed arithmetic model commute with
the specified original PEL residue map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ArithmeticPadicBase.arithmeticPadicBaseMap_compatible
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    {κ : K →+* ℂ} {κL : L →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (C : IntegralModel.Base.ArithmeticBaseExtension L κL)
    (i : B.extension.carrier →+* C.extension.carrier) (hdiv : B.denominator ∣ C.denominator)
    {q : ℕ} [Fact q.Prime]
    (jB : Arithmetic.QadicChoice B.extension.carrier B.embedding q) (hB : q.Coprime B.denominator)
    (jC : Arithmetic.QadicChoice C.extension.carrier C.embedding q) (hC : q.Coprime C.denominator)
    (hf : (jC.completion.toRingHom.comp (NumberField.FinitePlace.embedding jC.prime)).comp i =
      jB.completion.toRingHom.comp (NumberField.FinitePlace.embedding jB.prime)) :
    (ArithmeticPadicBase.arithmeticPadicBaseMap C jC hC).comp (ArithmeticBaseMaps.arithmeticBaseRingHom B C i hdiv) =
      ArithmeticPadicBase.arithmeticPadicBaseMap B jB hB := by
  apply RingHom.ext
  intro a
  apply PadicInt.ext
  exact (RingHom.congr_fun (ArithmeticPadicBase.arithmeticPadicBaseMap_generic C jC hC)
    (ArithmeticBaseMaps.arithmeticBaseRingHom B C i hdiv a)).trans
    ((congrArg (jC.completion.toRingHom.comp (NumberField.FinitePlace.embedding jC.prime))
      (RingHom.congr_fun (ArithmeticBaseMaps.arithmeticBaseRingHom_field B C i hdiv) a)).trans
      ((RingHom.congr_fun hf (B.toField a)).trans
        (RingHom.congr_fun (ArithmeticPadicBase.arithmeticPadicBaseMap_generic B jB hB) a).symm))

theorem ArithmeticPadicBase.arithmeticResidue_compatible
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    {κ : K →+* ℂ} {κL : L →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (C : IntegralModel.Base.ArithmeticBaseExtension L κL)
    (i : B.extension.carrier →+* C.extension.carrier) (hdiv : B.denominator ∣ C.denominator)
    {q : ℕ} [Fact q.Prime]
    (jB : Arithmetic.QadicChoice B.extension.carrier B.embedding q) (hB : q.Coprime B.denominator)
    (jC : Arithmetic.QadicChoice C.extension.carrier C.embedding q) (hC : q.Coprime C.denominator)
    (hf : (jC.completion.toRingHom.comp (NumberField.FinitePlace.embedding jC.prime)).comp i =
      jB.completion.toRingHom.comp (NumberField.FinitePlace.embedding jB.prime)) :
    (ArithmeticPadicBase.arithmeticResidue C jC hC).comp (ArithmeticBaseMaps.arithmeticBaseRingHom B C i hdiv) = ArithmeticPadicBase.arithmeticResidue B jB hB := by
  rw [ArithmeticPadicBase.arithmeticResidue, RingHom.comp_assoc,
    ArithmeticPadicBase.arithmeticPadicBaseMap_compatible B C i hdiv jB hB jC hC hf]
  rfl

theorem Models.RankThreePELModel.GoodIntegralReduction.arithmeticResidue_compatible_with_reduction
    {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field L] [NumberField L]
    {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
    (R : M.GoodIntegralReduction q j) {κL : L →+* ℂ}
    (C : IntegralModel.Base.ArithmeticBaseExtension L κL)
    (i : M.arithmetic.extension.carrier →+* C.extension.carrier)
    (hdiv : M.arithmetic.denominator ∣ C.denominator)
    (jC : Arithmetic.QadicChoice C.extension.carrier C.embedding q) (hC : q.Coprime C.denominator)
    (hf : (jC.completion.toRingHom.comp (NumberField.FinitePlace.embedding jC.prime)).comp i =
      j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)) :
    (ArithmeticPadicBase.arithmeticResidue C jC hC).comp (ArithmeticBaseMaps.arithmeticBaseRingHom M.arithmetic C i hdiv) = R.residue := by
  have h := ArithmeticPadicBase.arithmeticResidue_compatible M.arithmetic C i hdiv j R.denominatorPrimeToQ jC hC hf
  exact h.trans R.integralPadicBaseMap_residue

end AlgebraicGeometry.PELModuli.CMPoints

end

end OAI
