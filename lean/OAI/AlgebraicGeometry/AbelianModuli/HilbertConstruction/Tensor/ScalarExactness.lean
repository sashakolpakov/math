import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Extension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Scalar Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarExactness

noncomputable section

/-! Exactness for the underlying tensor complex is equivalent to exactness for native scalar extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)

theorem restrictScalars_shortComplex_exact_iff (S : ShortComplex (ModuleCat.{u} B)) :
    (S.map (ModuleCat.restrictScalars f)).Exact ↔ S.Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

theorem tensor_shortComplex_exact_iff_native (S : ShortComplex (ModuleCat.{u} R)) :
    letI : Algebra R B := f.toAlgebra
    (S.map (Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact ↔ (S.map (ModuleCat.extendScalars f)).Exact := by
  let : Algebra R B := f.toAlgebra
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (Extension.TensorExtension.iso f))).trans
    (restrictScalars_shortComplex_exact_iff f (S.map (ModuleCat.extendScalars f)))

theorem tensor_exactAt_iff_native (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    letI : Algebra R B := f.toAlgebra
    (Module.TensorFunctor.ModuleTensorFunctor.complex B C).ExactAt q ↔
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj C).ExactAt q := by
  let : Algebra R B := f.toAlgebra
  change ((C.sc q).map (Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact ↔
    ((C.sc q).map (ModuleCat.extendScalars f)).Exact
  exact tensor_shortComplex_exact_iff_native f (C.sc q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarExactness
