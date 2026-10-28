import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Extension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Tensor Homology Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.TensorHomologyComparison

noncomputable section

/-! Native scalar extension and the underlying tensor complex have the same homology after restriction to base coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def nativeTensorHomologyComparisonIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    letI : Algebra R B := f.toAlgebra
    (ModuleCat.restrictScalars.{u} f).obj
      ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj D).homology q) ≅
        (Module.TensorFunctor.ModuleTensorFunctor.complex B D).homology q := by
  let : Algebra R B := f.toAlgebra
  let C := ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj D
  exact ((C.sc q).mapHomologyIso (ModuleCat.restrictScalars.{u} f)).symm ≪≫
    HomologicalComplex.homologyMapIso ((Tensor.Extension.TensorExtension.complexIso f).app D) q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.TensorHomologyComparison
