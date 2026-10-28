import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Module Stalk -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleStalk

noncomputable section

/-! The stalk of the structure module is the actual local ring,
linearly. Global scalar endomorphisms induce multiplication by their
germs on every module stalk. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

attribute [local instance] Module.StalkExactness.stalkModule

def structureModuleStalkAddIso (x : X) :
    (Line.Bundles.structureModule X).presheaf.stalk x ≅
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (X.presheaf.stalk x) :=
  colimit.isoColimitCocone ⟨_, isColimitOfPreserves
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))⟩

theorem structureModuleStalkAddIso_germ (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) :
    (structureModuleStalkAddIso x).hom ((Line.Bundles.structureModule X).presheaf.germ U x hx r) =
      X.presheaf.germ U x hx r := by
  have h : (Line.Bundles.structureModule X).presheaf.germ U x hx ≫
      (structureModuleStalkAddIso x).hom =
        (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}).map (X.presheaf.germ U x hx) :=
    colimit.isoColimitCocone_ι_hom (C := AddCommGrpCat.{u}) ..
  exact ConcreteCategory.congr_hom h r

def structureModuleStalkEquiv (x : X) :
    (Module.StalkExactness.moduleStalkFunctor x).obj (Line.Bundles.structureModule X) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  __ := (structureModuleStalkAddIso x).addCommGroupIsoToAddEquiv
  map_smul' := by
    intro r m
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ :=
      (Line.Bundles.structureModule X).presheaf.exists_le_germ_eq m hxU
    let rV := X.presheaf.map (homOfLE hVU).op r
    have hr : X.presheaf.germ V x hxV rV = X.presheaf.germ U x hxU r :=
      X.presheaf.germ_res_apply (homOfLE hVU) x hxV r
    change (structureModuleStalkAddIso x).hom
        (X.presheaf.germ U x hxU r • (Line.Bundles.structureModule X).presheaf.germ V x hxV m) =
      X.presheaf.germ U x hxU r *
        (show X.presheaf.stalk x from
          (structureModuleStalkAddIso x).hom ((Line.Bundles.structureModule X).presheaf.germ V x hxV m))
    rw [← hr]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) (Line.Bundles.structureModule X).val x V hxV,
      structureModuleStalkAddIso_germ, structureModuleStalkAddIso_germ]
    exact map_mul (X.presheaf.germ V x hxV).hom rV m

def structureModuleStalkIso (x : X) :
    (Module.StalkExactness.moduleStalkFunctor x).obj (Line.Bundles.structureModule X) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  (structureModuleStalkEquiv x).toModuleIso

theorem moduleStalkFunctor_globalScalar (x : X) (M : X.Modules) (r : Γ(X, ⊤)) :
    (Module.StalkExactness.moduleStalkFunctor x).map (Global.ModuleScalars.globalModuleScalar M r) =
      X.presheaf.germ ⊤ x trivial r • 𝟙 ((Module.StalkExactness.moduleStalkFunctor x).obj M) := by
  apply ModuleCat.hom_ext
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Global.ModuleScalars.globalModuleScalar M r).mapPresheaf (M.presheaf.germ U x hxU m) =
    X.presheaf.germ ⊤ x trivial r • M.presheaf.germ U x hxU m
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change M.presheaf.germ U x hxU
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m) = _
  exact (PresheafOfModules.germ_smul (R := X.presheaf) M.val x U hxU _ m).trans
    (congrArg (fun z : X.presheaf.stalk x => z • M.presheaf.germ U x hxU m)
      (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hxU r))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleStalk
