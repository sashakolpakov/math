import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tensor Pairwise Limits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorPairwiseLimits

noncomputable section

/-! Flat tensor products preserve the finite overlap diagram of module sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def flatTensorPairwiseLimit (f : R →+* Γ(X, ⊤)) (M : X.Modules)
    (N : ModuleCat.{u} R) [Module.Flat R N]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) :
    IsLimit ((tensorLeft N).mapCone
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f M).mapCone (Pairwise.cocone U).op)) := by
  classical
  letI := Fintype.ofFinite ι
  exact isLimitOfPreserves (tensorLeft N) (Coefficient.ModulePresheaf.coefficientPairwiseLimit f M U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorPairwiseLimits
