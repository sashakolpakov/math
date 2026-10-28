import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Coproduct Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections

noncomputable section

/-! Sections of finite coproducts have finite modules whenever their summands do. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

theorem finite_coproduct_sections {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (M : ι → X.Modules) (U : X.Opens)
    (hM : ∀ i, Module.Finite Γ(X, U) Γ(M i, U)) :
    Module.Finite Γ(X, U) Γ(∐ M, U) := by
  let : HasZeroMorphisms X.Modules := CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  let F : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U)) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : HasBiproduct M := HasBiproduct.of_hasCoproduct M
  let : F.Additive := by
    constructor
    intro A B f g
    apply ModuleCat.hom_ext
    ext x
    rfl
  let : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  let : PreservesLimit (Discrete.functor M) F := by
    infer_instance
  let : PreservesBiproduct M F := preservesBiproduct_of_preservesProduct F
  let e : F.obj (∐ M) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U)) (∀ i, F.obj (M i)) :=
    F.mapIso (biproduct.isoCoproduct M).symm ≪≫
      F.mapBiproduct M ≪≫ biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)
  have hfinite (i : ι) : Module.Finite (X.ringCatSheaf.obj.obj (op U)) (F.obj (M i)) := hM i
  let : Module.Finite (X.ringCatSheaf.obj.obj (op U)) (∀ i, F.obj (M i)) :=
    @Module.Finite.pi _ _ ι (fun i ↦ F.obj (M i)) inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hfinite
  have hsum : Module.Finite (X.ringCatSheaf.obj.obj (op U)) (F.obj (∐ M)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact hsum

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections
