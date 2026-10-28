/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSheaf.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Underlying Additive Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness

/-!
# The additive sheaf underlying a scheme module

This is the narrow scheme-module bridge used by sheaf cohomology. It follows
the API proposed upstream in Mathlib PR #36345: forget the module structure,
then sheafify the underlying additive presheaf. The resulting functor is
additive, faithful, and preserves finite limits and all colimits.

This is a source-preserving Apache-2.0 port of AINTLIB's
`ForMathlib/SchemeModuleSheaf.lean`.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

universe u v u₁ u₂ u₃ v₁ v₂ v₃

private theorem preservesColimitsOfShape_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    {J : Type u} [Category.{v} J] (F : C ⥤ E)
    [PreservesColimitsOfShape J ((reflector R) ⋙ F)] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 K)) (asIso (reflectorAdjunction R).counit).symm).symm
      ⟨fun hc ↦ ⟨?_⟩⟩
  let hc₂ := colimit.isColimit (K ⋙ R)
  let ψ := IsColimit.uniqueUpToIso (isColimitOfPreserves (reflector R) hc₂) hc
  have φ := IsColimit.ofIsoColimit
    (isColimitOfPreserves (reflector R ⋙ F) hc₂)
    (Functor.mapCoconeMapCocone (H := reflector R) (H' := F)
      (colimit.cocone (K ⋙ R))).symm
  exact IsColimit.ofIsoColimit φ ((Cocone.functoriality _ F).mapIso ψ)

private theorem preservesColimitsOfSize_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    (F : C ⥤ E) [PreservesColimitsOfSize.{v, u} ((reflector R) ⋙ F)]
    [HasColimitsOfSize.{v, u} D] : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflector_comp R F

namespace ModuleSheaf

open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

variable (X) in
/-- The additive sheaf underlying a scheme module. -/
@[simps!]
noncomputable def toSheaf : X.Modules ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance : (ModuleSheaf.toSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance : PreservesFiniteLimits (ModuleSheaf.toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.toSheaf X.ringCatSheaf))

instance : (ModuleSheaf.toSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance : PreservesColimitsOfSize.{v, u} (ModuleSheaf.toSheaf X) := by
  let : Reflective (toPresheafOfModules X) :=
    { L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
      adj := PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj) }
  have : PreservesColimitsOfSize.{v, u}
      (reflector (toPresheafOfModules X) ⋙ ModuleSheaf.toSheaf X) :=
    comp_preservesColimits (PresheafOfModules.toPresheaf
      X.ringCatSheaf.obj)
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  exact preservesColimitsOfSize_of_reflector_comp
    (toPresheafOfModules X) _

instance : PreservesColimits (ModuleSheaf.toSheaf X) where

/-- The additive sheaf underlying a scheme module. -/
noncomputable abbrev sheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
  (ModuleSheaf.toSheaf X).obj M

/-- The additive-sheaf morphism underlying a morphism of scheme modules. -/
noncomputable abbrev Hom.sheafHom {M N : X.Modules} (f : M ⟶ N) :
    sheaf M ⟶ sheaf N :=
  (ModuleSheaf.toSheaf X).map f

end ModuleSheaf

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness
