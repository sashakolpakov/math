/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Free Sheaf Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeSheafSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {X : Scheme.{u}}

theorem finite_freeSheaf_globalSections
    (X : Scheme.{u}) (I : Type u) [Finite I] :
    Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free I (R := X.ringCatSheaf))) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let U := fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf
  let : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  let : F.Additive := by
    change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Additive
    unfold SheafOfModules.evaluation
    infer_instance
  let : PreservesLimit (Discrete.functor U) F := by
    dsimp [F]
    infer_instance
  let : PreservesBiproduct U F :=
    preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op ⊤))
        (∀ i, F.obj (U i)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫
      F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫
      ModuleCat.piIsoPi (F.obj ∘ U)
  have hfinite (i : I) :
      Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (F.obj (U i)) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      (X.ringCatSheaf.obj.obj (op ⊤))
    infer_instance
  have : Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (∀ i, F.obj (U i)) :=
    @Module.Finite.pi _ _ I (fun i ↦ F.obj (U i)) inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hfinite
  exact Module.Finite.equiv e.symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeSheafSections
