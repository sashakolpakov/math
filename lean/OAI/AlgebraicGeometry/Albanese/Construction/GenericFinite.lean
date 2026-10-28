import OAI.AlgebraicGeometry.Albanese.Construction.DominantDimension

/-! # Generic Finite -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.GenericFinite

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Canonical pullback makes the function fields of a dominant morphism an
algebra tower over the ground field. -/
theorem dominantFunctionField_isScalarTower (i : X ⟶ Y) [IsDominant i]
    (f : Y ⟶ Spec (.of K)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    letI := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
    IsScalarTower K Y.functionField X.functionField := by
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  let _ := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (DominantDimension.dominantFunctionFieldMap_scalar i f).symm

/-- Equality of dimensions for a dominant map makes its function-field
extension algebraic. Finiteness of the ground-field transcendence degrees is
used before cancelling cardinal addition. -/
theorem dominantFunctionField_isAlgebraic_of_dimension_eq
    (i : X ⟶ Y) [IsDominant i] (f : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) :
    letI := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
    Algebra.IsAlgebraic Y.functionField X.functionField := by
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  let _ := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
  have := dominantFunctionField_isScalarTower i f
  have heq := trdeg_add_eq K Y.functionField (A := X.functionField)
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast f,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (i ≫ f), hd] at heq
  apply trdeg_eq_zero_iff.mp
  rcases Cardinal.add_eq_left_iff.mp heq with h | h
  · exact False.elim (Cardinal.natCast_lt_aleph0.not_ge ((le_max_left _ _).trans h))
  · exact h

/-- The algebraic extension in the equal-dimension case is actually finite:
finite type over the ground field supplies essential finite type over the
intermediate function field. -/
theorem dominantFunctionField_finite_of_dimension_eq
    (i : X ⟶ Y) [IsDominant i] (f : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) :
    letI := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
    Module.Finite Y.functionField X.functionField := by
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  let _ := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
  have := dominantFunctionField_isScalarTower i f
  have := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_essFiniteType (i ≫ f)
  have := Algebra.EssFiniteType.of_comp K Y.functionField X.functionField
  have := dominantFunctionField_isAlgebraic_of_dimension_eq i f hd
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- In characteristic zero the generic finite extension is separable, so its
map of function fields is formally unramified. -/
theorem dominantFunctionField_formallyUnramified_of_dimension_eq [CharZero K]
    (i : X ⟶ Y) [IsDominant i] (f : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) :
    (DominantDimension.dominantFunctionFieldMap i).hom.FormallyUnramified := by
  have : CharZero Y.functionField :=
    charZero_of_injective_ringHom (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f).injective
  let _ := (DominantDimension.dominantFunctionFieldMap i).hom.toAlgebra
  have := dominantFunctionField_isAlgebraic_of_dimension_eq i f hd
  have : Algebra.IsSeparable Y.functionField X.functionField := inferInstance
  have := Algebra.FormallyEtale.of_isSeparable Y.functionField X.functionField
  exact inferInstanceAs (Algebra.FormallyUnramified Y.functionField X.functionField)

end

end OAI.AlgebraicGeometry.Albanese.Construction.GenericFinite
