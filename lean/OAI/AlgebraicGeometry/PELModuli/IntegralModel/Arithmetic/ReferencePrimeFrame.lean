import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Generic
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelExistence

/-! # Reference Prime Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison

noncomputable section

/-! The reference prime-frame cover is built from ReferenceFamily's given actual
universal family after reduction and the specified number-field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

abbrev referenceSpace := (Over.pullback B.fieldExtension).obj (Reduction.reduction M.space)
abbrev referenceFamily := Reduced.Generic.reducedGenericPELUniversal (algebraMap K B.extension.carrier) M

theorem primeUnit (p : ℕ) [Fact p.Prime] (x : (referenceSpace B M).left) :
    IsUnit (p : (referenceSpace B M).left.presheaf.stalk x) :=
  Integral.TwoLevelExistence.integer_unit_at_stalk_of_base_unit (referenceSpace B M).hom p
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) x

abbrev primeFrame (p : ℕ) [Fact p.Prime] :=
  IntegralPEL.FrameExistence.IntegralPELFrame.space (referenceFamily B M) (primeUnit B M p)

def primeUniversal (p : ℕ) [Fact p.Prime] :
    IntegralAdded.PELId.IntegralAddedPELLevel P B.extension.carrier
      ((algebraMap K B.extension.carrier).comp
        (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) p N (primeFrame B M p) :=
  IntegralPEL.FrameExistence.IntegralPELFrame.universal (referenceFamily B M) (primeUnit B M p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison
