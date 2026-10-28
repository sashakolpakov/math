import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafTensor
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Sheaf Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafRestriction.Construction

noncomputable section

/-! Restriction of module presheaves and compatibility with sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.TopologicalSpace

universe u

def moduleSheafificationUnit {X : Scheme.{u}} (P : X.PresheafOfModules) :
    P ⟶ (SheafTensor.Construction.sheafifyModule P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P

theorem moduleSheafificationUnit_locallyInjective {X : Scheme.{u}}
    (P : X.PresheafOfModules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (moduleSheafificationUnit P) := by
  change Presheaf.IsLocallyInjective _ (CategoryTheory.toSheafify _ P.presheaf)
  infer_instance

theorem moduleSheafificationUnit_locallySurjective {X : Scheme.{u}}
    (P : X.PresheafOfModules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (moduleSheafificationUnit P) := by
  change Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ P.presheaf)
  infer_instance

/-- A locally bijective map to a sheaf exhibits that sheaf as the sheafification. -/
def sheafificationIsoOfLocallyBijective {X : Scheme.{u}}
    {P : X.PresheafOfModules} {M : X.Modules} (q : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) q]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) q] :
    SheafTensor.Construction.sheafifyModule P ≅ M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hq := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf _).map q)
  have hq' := (Opens.grothendieckTopology X).W_iff _ |>.mp hq
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map (F.map q)) := hq'
  have : IsIso (F.map q) := isIso_of_reflects_iso (F.map q)
    (SheafOfModules.toSheaf X.ringCatSheaf)
  let e : F.obj P ≅ F.obj M.val := asIso (F.map q)
  exact e ≪≫ SheafTensor.Construction.sheafifyModuleIso M

/-- Restriction of a module presheaf along an open immersion. -/
def restrictModulePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (F := f.opensFunctor)
    (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

theorem restrictModulePresheaf_locallyInjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {P Q : Y.PresheafOfModules} (q : P ⟶ Q)
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology Y) q] :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      ((restrictModulePresheaf f).map q) :=
  Presheaf.isLocallyInjective_whisker (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) f.opensFunctor
    ((PresheafOfModules.toPresheaf _).map q)

theorem restrictModulePresheaf_locallySurjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {P Q : Y.PresheafOfModules} (q : P ⟶ Q)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology Y) q] :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      ((restrictModulePresheaf f).map q) :=
  Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) f.opensFunctor
    ((PresheafOfModules.toPresheaf _).map q)

/-- Sheafifying and then restricting is canonically isomorphic to
restricting and then sheafifying. -/
def restrictSheafificationIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : Y.PresheafOfModules) :
    SheafTensor.Construction.sheafifyModule ((restrictModulePresheaf f).obj P) ≅ (SheafTensor.Construction.sheafifyModule P).restrict f := by
  letI := moduleSheafificationUnit_locallyInjective P
  letI := moduleSheafificationUnit_locallySurjective P
  let q := (restrictModulePresheaf f).map (moduleSheafificationUnit P)
  have hqi := restrictModulePresheaf_locallyInjective f (moduleSheafificationUnit P)
  have hqs := restrictModulePresheaf_locallySurjective f (moduleSheafificationUnit P)
  exact @sheafificationIsoOfLocallyBijective X _ ((SheafTensor.Construction.sheafifyModule P).restrict f) q hqi hqs

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafRestriction.Construction
