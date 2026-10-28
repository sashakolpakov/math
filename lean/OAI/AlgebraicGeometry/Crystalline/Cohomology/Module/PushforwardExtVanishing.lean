import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.PushforwardResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal

/-! # Pushforward Ext Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing

noncomputable section

/-! Local exactness plus affine section vanishing makes the actual direct-image module sheaf coefficient-Ext-acyclic. -/

open _root_.CategoryTheory Abelian Limits Opposite _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y)
  {F : TopCat.Sheaf (ModuleCat.{u} R) X} (I : InjectiveResolution F)

abbrev sections (Z : TopCat.{u}) : TopCat.Sheaf (ModuleCat.{u} R) Z ⥤ ModuleCat.{u} R :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance sections_additive (Z : TopCat.{u}) : (sections R Z).Additive where
  map_add := rfl

local instance : HasExt.{u + 1} (ConstantSheaf.ConstantSheafSections.Sheaves R Y) := HasExt.standard _

theorem ext_subsingleton (hlocal : PushforwardResolution.ModulePushforwardResolution.LocallyExact R f I)
    (n : ℕ) (hI : (((sections R X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1)) :
    Subsingleton (Abelian.Ext.{u + 1} (ConstantSheaf.ConstantSheafSections.coefficient R Y)
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F) (n + 1)) := by
  let J := PushforwardResolution.ModulePushforwardResolution.resolution R f I hlocal
  have hs : (((sections R Y).mapHomologicalComplex (.up ℕ)).obj J.cocomplex).ExactAt (n + 1) := hI
  let e := (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) (ModuleCat.{u} R)
      (isTerminalTop : IsTerminal (⊤ : Opens Y))) (.up ℕ)).app J.cocomplex
  have hJ := hs.of_iso e.symm
  have hz :=
    @SheafGlobal.SheafGlobalExtVanishing.ext_eq_zero.{u, u, u, u + 1} _ _ (Opens.grothendieckTopology Y) R _ _ _
      (inferInstanceAs (HasExt.{u + 1} (ConstantSheaf.ConstantSheafSections.Sheaves R Y))) _ J n hJ
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing
