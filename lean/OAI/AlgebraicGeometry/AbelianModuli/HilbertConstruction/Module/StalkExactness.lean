import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Stalk Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness

noncomputable section

/-! The actual additive stalk of a scheme module, with its natural
local-ring action, forms an exact functor. These stalks jointly detect
exactness of module sheaves. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

variable {X : Scheme.{u}}

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

local instance stalkModule (x : X) (M : X.Modules) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let P : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
  exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) P x

def moduleStalkMap (x : X) {M N : X.Modules} (f : M ⟶ N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  __ := ((TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).map f.mapPresheaf).hom
  map_smul' := by
    intro r m
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    let rV := X.presheaf.map (homOfLE hVU).op r
    have hr : X.presheaf.germ V x hxV rV = X.presheaf.germ U x hxU r :=
      X.presheaf.germ_res_apply (homOfLE hVU) x hxV r
    rw [← hr]
    erw [← PresheafOfModules.germ_smul M.val x V hxV]
    let sf : M.presheaf.stalk x →+ N.presheaf.stalk x :=
      ((TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).map f.mapPresheaf).hom
    have hf (a : M.presheaf.obj (.op V)) :
        sf (M.presheaf.germ V x hxV a) = N.presheaf.germ V x hxV (f.app V a) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV f.mapPresheaf a
    change sf (M.presheaf.germ V x hxV (rV • m)) =
      X.presheaf.germ V x hxV rV • sf (M.presheaf.germ V x hxV m)
    rw [hf, hf]
    rw [f.app_smul]
    exact PresheafOfModules.germ_smul (R := X.presheaf) N.val x V hxV rV (f.app V m)

def moduleStalkFunctor (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map f := ModuleCat.ofHom (moduleStalkMap x f)
  map_id M := by
    apply ModuleCat.hom_ext
    ext m
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.toPresheaf X) ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).map_id M) m
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext m
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.toPresheaf X) ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).map_comp f g) m

def moduleStalkForgetIso (x : X) :
    moduleStalkFunctor x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    ext m
    rfl)

instance moduleStalkFunctor_additive (x : X) : (moduleStalkFunctor x).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    ext m
    have : (TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).Additive :=
      TopCat.instAdditivePresheafStalkFunctor x
    have h := (TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x).map_add
      (f := f.mapPresheaf) (g := g.mapPresheaf)
    exact ConcreteCategory.congr_hom h m

local instance moduleStalkUnderlying_additive (x : X) :
    (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)).Additive :=
  Functor.additive_of_iso (moduleStalkForgetIso x)

instance moduleStalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor x) := by
  let G := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) :=
    TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor x
  have : PreservesFiniteLimits (moduleStalkFunctor x ⋙ G) :=
    preservesFiniteLimits_of_natIso (moduleStalkForgetIso x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

instance moduleStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (moduleStalkFunctor x) := by
  classical
  let G := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x
  have : F.IsLeftAdjoint := (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).isLeftAdjoint
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesFiniteColimits (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X) := inferInstance
  have : PreservesFiniteColimits (moduleStalkFunctor x ⋙ G) :=
    preservesFiniteColimits_of_natIso (moduleStalkForgetIso x).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ G

theorem moduleShortComplex_exact_iff_stalk (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, (S.map (moduleStalkFunctor x)).Exact := by
  rw [← S.exact_map_iff_of_faithful (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)]
  erw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  apply forall_congr'
  intro x
  rw [(S.map (moduleStalkFunctor x)).exact_iff_exact_map_forget₂]
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (moduleStalkForgetIso x))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness
