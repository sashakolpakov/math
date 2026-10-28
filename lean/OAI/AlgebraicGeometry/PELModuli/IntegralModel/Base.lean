import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Open
import OAI.ArithmeticGeometry.Models.IntegerBase
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Basic.Complex.Basic

/-! # Base -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base

noncomputable section

/-!
Concrete arithmetic bases for IntegralModel. The base ring is literally a localization
of a ring of integers. The embedding of the finite extension in ℂ is obtained
from algebraic closedness; it is not an extra existence hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A finite number-field extension with a complex embedding extending the
specified one, together with a nonzero integer to invert. -/
structure ArithmeticBaseExtension
    (K : Type) [Field K] [NumberField K] (κ : K →+* ℂ) where
  extension : Arithmetic.Open.FiniteNumberFieldExtension K
  embedding : extension.carrier →+* ℂ
  embedding_extends : embedding.comp (algebraMap K extension.carrier) = κ
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0

namespace ArithmeticBaseExtension

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

/-- Every finite extension admits the required extension of a complex embedding. -/
def ofFiniteExtension (L : Arithmetic.Open.FiniteNumberFieldExtension K)
    (κ : K →+* ℂ) (N : ℕ) (hN : N ≠ 0) : ArithmeticBaseExtension K κ := by
  let : Algebra K ℂ := κ.toAlgebra
  let φ : L.carrier →ₐ[K] ℂ := IsAlgClosed.lift
  exact {
    extension := L
    embedding := φ.toRingHom
    embedding_extends := by ext x; exact φ.commutes x
    denominator := N
    denominator_ne_zero := hN }

abbrev R (B : ArithmeticBaseExtension K κ) :=
  Localization.Away
    (B.denominator : NumberField.RingOfIntegers B.extension.carrier)

abbrev base (B : ArithmeticBaseExtension K κ) : Scheme :=
  Spec (CommRingCat.of B.R)

def toField (B : ArithmeticBaseExtension K κ) : B.R →+* B.extension.carrier :=
  ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField B.extension.carrier
    B.denominator B.denominator_ne_zero

theorem toField_injective (B : ArithmeticBaseExtension K κ) :
    Function.Injective B.toField :=
  ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations.integersAwayToField_injective B.extension.carrier
    B.denominator B.denominator_ne_zero

def generic (B : ArithmeticBaseExtension K κ) : Arithmetic.Open.fieldBase B.extension.carrier ⟶ B.base :=
  Spec.map (CommRingCat.ofHom B.toField)

def fieldExtension (B : ArithmeticBaseExtension K κ) :
    Arithmetic.Open.fieldBase B.extension.carrier ⟶ Arithmetic.Open.fieldBase K :=
  Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier))

def complexPoint (B : ArithmeticBaseExtension K κ) : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B.base :=
  Spec.map (CommRingCat.ofHom B.embedding) ≫ B.generic

theorem generic_dominant (B : ArithmeticBaseExtension K κ) : IsDominant B.generic := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  change RingHom.ker B.toField ≤ nilradical B.R
  rw [(RingHom.injective_iff_ker_eq_bot B.toField).mp B.toField_injective]
  exact bot_le

theorem complexPoint_dominant (B : ArithmeticBaseExtension K κ) :
    IsDominant B.complexPoint := by
  let : IsDominant B.generic := B.generic_dominant
  have hfield : Surjective (Spec.map (CommRingCat.ofHom B.embedding)) :=
    ⟨Function.surjective_to_subsingleton _⟩
  change IsDominant (Spec.map (CommRingCat.ofHom B.embedding) ≫ B.generic)
  infer_instance

theorem denominator_isUnit (B : ArithmeticBaseExtension K κ) :
    IsUnit (B.denominator : B.R) := by
  simpa using IsLocalization.Away.algebraMap_isUnit
    (S := B.R) (B.denominator : NumberField.RingOfIntegers B.extension.carrier)

end ArithmeticBaseExtension

/-- An actual geometric point of a base scheme. -/
structure GeometricPoint (B : Scheme) where
  field : Type
  [fieldStructure : Field field]
  [algebraicallyClosed : IsAlgClosed field]
  morphism : Spec (CommRingCat.of field) ⟶ B

attribute [instance] GeometricPoint.fieldStructure GeometricPoint.algebraicallyClosed

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
