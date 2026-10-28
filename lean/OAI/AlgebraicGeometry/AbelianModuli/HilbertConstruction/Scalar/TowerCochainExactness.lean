import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness

/-! # Tower Cochain Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TowerCochainExactness

noncomputable section

/-! Exactness of an actual tensor complex transfers to iterated base change along a scalar tower. -/
open _root_.CategoryTheory
universe u

theorem tensor_baseChange_exactAt_of_scalar_tower
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (h : (Module.TensorFunctor.ModuleTensorFunctor.complex B C).ExactAt q) :
    (Module.TensorFunctor.ModuleTensorFunctor.complex B
      (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S).mapHomologicalComplex (.up ℕ)).obj C)).ExactAt q := by
  let T := C.sc q
  have hnative : (T.map (ModuleCat.extendScalars (algebraMap R B))).Exact := by
    have hi : (T.map (Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact ↔
        (T.map (ModuleCat.extendScalars (algebraMap R B))).Exact := by
      have ht := Tensor.ScalarExactness.tensor_shortComplex_exact_iff_native (algebraMap R B) T
      rw [toAlgebra_algebraMap] at ht
      exact ht
    exact hi.mp h
  have hcomp : (T.map (ModuleCat.extendScalars
      ((algebraMap S B).comp (algebraMap R S)))).Exact := by
    rw [← IsScalarTower.algebraMap_eq R S B]
    exact hnative
  have hiter := Iterated.TensorExactness.iterated_tensor_exact_of_composite (A := S) T hcomp
  exact (Base.ChangeTensorExactness.baseChange_shortComplex_exact_iff_tensor (B := B)
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R S T)).mp hiter

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TowerCochainExactness
