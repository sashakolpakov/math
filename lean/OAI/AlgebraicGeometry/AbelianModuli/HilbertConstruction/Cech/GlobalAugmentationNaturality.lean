/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation

/-! # Global Augmentation Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationNaturality.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- The global-sections Cech augmentation is natural in the sheaf. -/
theorem cechGlobalSectionsAugmentation_naturality
    {G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U ≫
        ((cechComplexFunctor U).map f.hom).f 0 =
      (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map f ≫ GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation G U := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (IntrinsicCech.Cochains.cechCochainAddEquiv G.obj U 0).injective
  funext i
  let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  have hnative :
      ((cechComplexFunctor U).map f.hom).f 0 ≫
          Limits.Pi.π (fun j : Fin 1 → ι ↦
            G.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i =
        Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k))) := by
    change Limits.Pi.map (fun j : Fin 1 → ι ↦ f.hom.app
      (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) ≫ _ = _
    exact Limits.Pi.map_π _ i
  have hmap := ConcreteCategory.congr_hom hnative
    (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x)
  have hmap' :
      IntrinsicCech.Cochains.cechCochainAddEquiv G.obj U 0
          (((cechComplexFunctor U).map f.hom).f 0
            (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x)) i =
        f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
          (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0
            (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x) i) := by
    rw [IntrinsicCech.Cochains.cechCochainAddEquiv_apply, IntrinsicCech.Cochains.cechCochainAddEquiv_apply]
    change
      (Limits.Pi.π (fun j : Fin 1 → ι ↦
        G.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i)
          (((cechComplexFunctor U).map f.hom).f 0
            (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x)) =
        f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
          ((Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i)
              (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x))
    calc
      _ = (Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k))))
            (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x) := hmap
      _ = _ := rfl
  have hΓ := ConcreteCategory.congr_hom (eΓ.hom.naturality f) x
  simp only [ConcreteCategory.comp_apply] at hΓ
  have hΓ' :
      f.hom.app (op ⊤) (eΓ.hom.app F x) =
        eΓ.hom.app G ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map f x) := by
    exact hΓ.symm
  calc
    _ = f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
        (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0
          (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x) i) := hmap'
    _ = f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
        (F.obj.map (homOfLE le_top).op (eΓ.hom.app F x)) := by
      rw [GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation_apply]
    _ = G.obj.map (homOfLE le_top).op
        (f.hom.app (op ⊤) (eΓ.hom.app F x)) := by
      exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE le_top).op) _
    _ = G.obj.map (homOfLE le_top).op
        (eΓ.hom.app G ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map f x)) := by rw [hΓ']
    _ = IntrinsicCech.Cochains.cechCochainAddEquiv G.obj U 0
        (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation G U ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map f x)) i := by
      rw [GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation_apply]
    _ = _ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationNaturality.IntrinsicCech
