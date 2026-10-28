import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.QuasiIso

/-! # Module Tensor Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor

noncomputable section

/-! The actual tensor functor used by the Cech model preserves homology when its tensor factor is flat. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
universe u

variable {R : Type u} [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]

def tensorLeftIso : HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ≅ tensorLeft (ModuleCat.of R A) := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a m
  rfl

instance tensor_preservesFiniteColimits : PreservesFiniteColimits (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) A) :=
  preservesFiniteColimits_of_natIso (tensorLeftIso (R := R) A).symm

instance tensor_preservesFiniteLimits [Module.Flat R A] : PreservesFiniteLimits (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) A) :=
  preservesFiniteLimits_of_natIso (tensorLeftIso (R := R) A).symm

def flatHomologyIso [Module.Flat R A]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj (C.homology q) ≅ (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C).homology q :=
  ((C.sc q).mapHomologyIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)).symm

theorem flat_map_quasiIso [Module.Flat R A]
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (a : C ⟶ D) [QuasiIso a] :
    QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A a) := by infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor
