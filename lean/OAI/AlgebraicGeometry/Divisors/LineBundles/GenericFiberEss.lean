import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFunctorTo

/-! # Generic Fiber Ess -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss.BundleCycles.GenericFiberFields

noncomputable section

/-! Above the generic point of the base, its function field maps into
the actual source stalk. These scalar maps agree with the morphism's
native generic-stalk field embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp.BundleCycles.BirationalValuationSection

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

abbrev fieldAlgebra : Algebra Y.functionField X.functionField := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra

abbrev stalkAlgebra (x : X) (hx : f x = genericPoint Y) :
    Algebra Y.functionField (X.presheaf.stalk x) :=
  (BirationalValuationComp.BundleCycles.BirationalValuationSection.pointStalkMap f (genericPoint Y) x hx).hom.toAlgebra

theorem stalkTower (x : X) (hx : f x = genericPoint Y) :
    letI := fieldAlgebra f hη
    letI := stalkAlgebra f x hx
    IsScalarTower Y.functionField (X.presheaf.stalk x) X.functionField := by
  let := fieldAlgebra f hη
  let := stalkAlgebra f x hx
  apply IsScalarTower.of_algebraMap_eq'
  have h := BirationalValuationComp.BundleCycles.BirationalValuationSection.pointStalkMap_functionField f hη (genericPoint Y) x hx
  change BirationalValuationComp.BundleCycles.BirationalValuationSection.pointStalkMap f (genericPoint Y) x hx ≫
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη at h
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at h
  exact (congrArg CommRingCat.Hom.hom h).symm

theorem field_trdeg_one {K : Type u} [Field K]
    (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] [LocallyOfFiniteType (f ≫ g)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g)) :
    letI := fieldAlgebra f hη
    Algebra.trdeg Y.functionField X.functionField = 1 := by
  let := fieldAlgebra f hη
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let : IsScalarTower K Y.functionField X.functionField :=
    IsScalarTower.of_algHom (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_finTrdeg g
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_essFiniteType (f ≫ g)
  have h := trdeg_add_eq K Y.functionField (A := X.functionField)
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast g, ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (f ≫ g),
    ← hdim, Nat.cast_add, Nat.cast_one] at h
  rw [add_comm ((Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g : ℕ) : Cardinal),
    add_comm ((Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g : ℕ) : Cardinal)] at h
  exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp h

theorem field_essFiniteType {K : Type u} [Field K]
    (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType (f ≫ g)] :
    letI := fieldAlgebra f hη
    Algebra.EssFiniteType Y.functionField X.functionField := by
  let := fieldAlgebra f hη
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let : IsScalarTower K Y.functionField X.functionField :=
    IsScalarTower.of_algHom (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_essFiniteType (f ≫ g)
  exact Algebra.EssFiniteType.of_comp K Y.functionField X.functionField

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss.BundleCycles.GenericFiberFields
