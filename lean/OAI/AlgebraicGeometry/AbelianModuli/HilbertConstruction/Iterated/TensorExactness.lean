import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctorComparison

/-! # Tensor Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness

noncomputable section

/-! Exactness for native extension along a composite scalar map is
exactness for the explicit iterated tensor complexes used in local algebra. -/

open _root_.CategoryTheory

universe u

def iteratedTensorScalarIso
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] :
    ModuleCat.extendScalars ((algebraMap A B).comp (algebraMap R A)) ≅
      Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R A ⋙
        Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor A B :=
    ModuleCat.extendScalarsComp (algebraMap R A) (algebraMap A B) ≪≫
      Functor.isoWhiskerRight (Scalar.FunctorComparison.ScalarFunctorComparison.iso R A).symm
        (ModuleCat.extendScalars (algebraMap A B)) ≪≫
      Functor.isoWhiskerLeft (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R A)
        (Scalar.FunctorComparison.ScalarFunctorComparison.iso A B).symm

theorem iterated_tensor_exact_iff_composite
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] (S : ShortComplex (ModuleCat.{u} R)) :
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A B
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact ↔
      (S.map (ModuleCat.extendScalars ((algebraMap A B).comp (algebraMap R A)))).Exact :=
  (ShortComplex.exact_iff_of_iso (S.mapNatIso (iteratedTensorScalarIso (A := A)))).symm

theorem iterated_tensor_exact_of_composite
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B]
    (S : ShortComplex (ModuleCat.{u} R))
    (h : (S.map (ModuleCat.extendScalars ((algebraMap A B).comp (algebraMap R A)))).Exact) :
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A B
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact :=
  (iterated_tensor_exact_iff_composite S).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness
