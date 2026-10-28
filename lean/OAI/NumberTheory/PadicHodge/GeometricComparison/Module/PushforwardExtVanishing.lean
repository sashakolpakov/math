import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal

/-! # Pushforward Ext Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing

noncomputable section

/-! Local exactness plus affine section vanishing makes the actual direct-image module sheaf coefficient-Ext-acyclic. -/

open _root_.CategoryTheory Abelian Limits Opposite _root_.TopologicalSpace

variable (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
  {F : TopCat.Sheaf (ModuleCat R) X} (I : InjectiveResolution F)

abbrev sections (Z : TopCat.{0}) : TopCat.Sheaf (ModuleCat R) Z ⥤ ModuleCat R :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance sections_additive (Z : TopCat.{0}) : (sections R Z).Additive where
  map_add := rfl

local instance : HasExt.{1} (ConstantSheaf.ConstantSheafSections.Sheaves R Y) := HasExt.standard _

theorem ext_subsingleton (hlocal : PushforwardResolution.ModulePushforwardResolution.LocallyExact R f I)
    (n : ℕ) (hI : (((sections R X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1)) :
    Subsingleton (Abelian.Ext.{1} (ConstantSheaf.ConstantSheafSections.coefficient R Y)
      ((TopCat.Sheaf.pushforward (ModuleCat R) f).obj F) (n + 1)) := by
  let J := PushforwardResolution.ModulePushforwardResolution.resolution R f I hlocal
  have hs : (((sections R Y).mapHomologicalComplex (.up ℕ)).obj J.cocomplex).ExactAt (n + 1) := hI
  let e := (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) (ModuleCat R)
      (isTerminalTop : IsTerminal (⊤ : Opens Y))) (.up ℕ)).app J.cocomplex
  have hJ := hs.of_iso e.symm
  have hz :=
    @AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal.SheafGlobalExtVanishing.ext_eq_zero.{0, 0, 0, 1} _ _ (Opens.grothendieckTopology Y) R _ _ _
      (inferInstanceAs (HasExt.{1} (ConstantSheaf.ConstantSheafSections.Sheaves R Y))) _ J n hJ
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing
