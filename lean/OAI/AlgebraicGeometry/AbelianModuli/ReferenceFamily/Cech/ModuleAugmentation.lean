import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleDifferential
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Augmentation

/-! # Module Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleAugmentation

noncomputable section

/-! The original Cech augmentation and its differential identities are
retained in the actual algebraic module category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem cechAugmentation_smul (V : X.Opens) (a b : Γ(X, V)) :
    (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (TermModules.structureAbelianSheaf X) U).hom.app (op V) (a * b) =
      a • (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (TermModules.structureAbelianSheaf X) U).hom.app (op V) b := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U 0 V).injective
  funext i
  erw [SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_apply, TermModules.cechTermCoordinates_smul, SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_apply]
  exact (X.presheaf.map (homOfLE (show V ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤ V from inf_le_left)).op).hom.map_mul a b

def cechModuleAugmentation : HilbertConstruction.Line.Bundles.structureModule X ⟶ TermModules.cechTermModule X U 0 :=
  ModuleHomOf.moduleHomOfAbelian (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (TermModules.structureAbelianSheaf X) U) (cechAugmentation_smul X U)

theorem cechModuleAugmentation_underlying :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (cechModuleAugmentation X U) =
      SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (TermModules.structureAbelianSheaf X) U :=
  ModuleHomOf.moduleHomOfAbelian_underlying _ _

theorem cechModuleDifferential_comp (n : ℕ) :
    ModuleDifferential.cechModuleDifferential X U n ≫ ModuleDifferential.cechModuleDifferential X U (n + 1) = 0 := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  erw [Functor.map_comp, Functor.map_zero, ModuleDifferential.cechModuleDifferential_underlying,
    ModuleDifferential.cechModuleDifferential_underlying]
  exact SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechDifferential_comp (TermModules.structureAbelianSheaf X) U n

theorem cechModuleAugmentation_comp :
    cechModuleAugmentation X U ≫ ModuleDifferential.cechModuleDifferential X U 0 = 0 := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  erw [Functor.map_comp, Functor.map_zero, cechModuleAugmentation_underlying,
    ModuleDifferential.cechModuleDifferential_underlying]
  exact SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_comp (TermModules.structureAbelianSheaf X) U

def cechModuleAugmentedShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (cechModuleAugmentation X U) (ModuleDifferential.cechModuleDifferential X U 0)
    (cechModuleAugmentation_comp X U)

def cechModuleShortComplex (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (ModuleDifferential.cechModuleDifferential X U n) (ModuleDifferential.cechModuleDifferential X U (n + 1))
    (cechModuleDifferential_comp X U n)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleAugmentation
