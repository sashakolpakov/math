import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Relative Structure Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureSections.Construction

noncomputable section

/-! The structure presheaf on a scheme over Spec R, with its actual R-module action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual structure presheaf, with scalars in the literal base ring R. -/
def relativeStructureSections : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := by
    let : Algebra R Γ(X, U.unop) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U.unop).toAlgebra
    exact ModuleCat.of R Γ(X, U.unop)
  map {U V} i := ConcreteCategory.ofHom (C := ModuleCat R) {
    toFun := (X.presheaf.map i).hom
    map_add' := (X.presheaf.map i).hom.map_add
    map_smul' r s := by
      change X.presheaf.map i (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U.unop r * s) =
        Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V.unop r * X.presheaf.map i s
      rw [map_mul]
      exact congrArg (fun x => x * X.presheaf.map i s)
        (RingHom.congr_fun (Infinitesimal.ChartRestriction.Construction.baseOpenSectionsMap_restrict f (leOfHom i.unop)) r) }
  map_id U := by
    let : Algebra R Γ(X, U.unop) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (X.presheaf.map_id U) s
  map_comp {U V W} i j := by
    let : Algebra R Γ(X, U.unop) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U.unop).toAlgebra
    let : Algebra R Γ(X, V.unop) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V.unop).toAlgebra
    let : Algebra R Γ(X, W.unop) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f W.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp i j) s

theorem relativeStructureSections_smul (U : X.Opens) (r : R)
    (s : (relativeStructureSections f).obj (op U)) :
    (show Γ(X, U) from r • s) = Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U r * (show Γ(X, U) from s) := rfl

theorem baseOpenSectionsMap_comp (g : Y ⟶ X) (U : X.Opens) :
    (g.app U).hom.comp (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U) =
      Affine.InfinitesimalSections.Construction.baseOpenSectionsMap (g ≫ f) (g ⁻¹ᵁ U) := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)) ≫ g.app U).hom = _
  rw [Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Pullback of actual functions is R-linear. -/
def relativeStructureSectionsPullback (g : Y ⟶ X) :
    relativeStructureSections f ⟶
      (TopologicalSpace.Opens.map g.base).op ⋙ relativeStructureSections (g ≫ f) where
  app U := ConcreteCategory.ofHom (C := ModuleCat R) (show (relativeStructureSections f).obj U →ₗ[R]
      (relativeStructureSections (g ≫ f)).obj (op (g ⁻¹ᵁ U.unop)) from {
    toFun := fun s => (g.app U.unop).hom s
    map_add' := map_add _
    map_smul' r s := by
      change g.app U.unop (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U.unop r * (show Γ(X, U.unop) from s)) =
        Affine.InfinitesimalSections.Construction.baseOpenSectionsMap (g ≫ f) (g ⁻¹ᵁ U.unop) r * g.app U.unop s
      rw [map_mul]
      exact congrArg (fun x => x * g.app U.unop s)
        (RingHom.congr_fun (baseOpenSectionsMap_comp f g U.unop) r) })
  naturality _ _ i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (g.naturality i) s

theorem relativeStructureSectionsPullback_apply (g : Y ⟶ X) (U : X.Opens)
    (s : (relativeStructureSections f).obj (op U)) :
    (relativeStructureSectionsPullback f g).app (op U) s = g.app U s := rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureSections.Construction
