import OAI.AlgebraicGeometry.Betti.AffineDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.FinTrdeg

/-! # Function Field Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType

noncomputable section

/-!
# Finite generation of the actual function field

The structure morphism supplies the base algebra. A nonempty affine open has
finite-type sections, and the genuine function field is their fraction field.
The proved compatibility of section maps and germs therefore gives essential
finite type, without adding an algebra structure or generation hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

/-- A nonempty affine chart proves essential finite type of the actual
function field over the global sections of an affine base. -/
theorem functionFieldBase_essFiniteType_of_affineOpen
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    Algebra.EssFiniteType Γ(Y, ⊤) X.functionField := by
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra f U
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := Betti.AffineDimension.Realization.functionFieldBase_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.FiniteType Γ(Y, ⊤) Γ(X, U) :=
    f.finiteType_appLE (isAffineOpen_top Y) hU le_top
  let : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp Γ(Y, ⊤) Γ(X, U) X.functionField

/-- An integral scheme locally of finite type over an affine base has an
essentially finite-type function field for its canonical base-section algebra. -/
theorem functionFieldBase_essFiniteType
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f] :
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    Algebra.EssFiniteType Γ(Y, ⊤) X.functionField := by
  let U : X.Opens :=
    (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty U := ⟨⟨genericPoint X, X.affineCover.covers (genericPoint X)⟩⟩
  exact functionFieldBase_essFiniteType_of_affineOpen f U hU

/-- Ring-homomorphism form of the same actual function-field result. -/
theorem functionFieldBaseMap_essFiniteType
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f] :
    (Betti.AffineDimension.Realization.functionFieldBaseMap f).hom.EssFiniteType :=
  functionFieldBase_essFiniteType f

section Scalars

variable {K : Type u} [CommRing K]

/-- Essential finite type descends along the canonical isomorphism from the
actual scalar ring to the global functions on its spectrum. -/
theorem functionFieldScalarMap_essFiniteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    (FunctionFieldScalar.functionFieldScalarMap f).EssFiniteType := by
  exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (Betti.AffineDimension.Realization.functionFieldBaseMap f)).mpr
      (functionFieldBaseMap_essFiniteType f)

/-- The function field of an integral scheme locally of finite type over
`Spec K` is essentially of finite type over the intended scalar ring `K`. -/
theorem functionFieldScalar_essFiniteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Algebra.EssFiniteType K X.functionField :=
  functionFieldScalarMap_essFiniteType f

end Scalars

variable {K : Type u} [Field K]

/-- The function field of an integral scheme locally of finite type over a
field has finite transcendence degree for its actual structural algebra. -/
theorem functionFieldScalar_finTrdeg
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    FinTrdeg K X.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := functionFieldScalar_essFiniteType f
  infer_instance

/-- In particular, its transcendence degree is a finite cardinal. -/
theorem functionFieldScalar_trdeg_lt_aleph0
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Algebra.trdeg K X.functionField < Cardinal.aleph0 := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := functionFieldScalar_finTrdeg f
  exact trdeg_lt_aleph0 K X.functionField

end

end OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType
