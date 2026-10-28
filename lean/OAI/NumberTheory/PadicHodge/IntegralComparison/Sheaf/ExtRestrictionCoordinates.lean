import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExtPullbackComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Ext Restriction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates

noncomputable section

/-! The original exact-functor Ext pullback has the actual presheaf restriction coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u} R, F.op.HasPointwiseRightKanExtension P]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]

abbrev restriction : Sheaf K (ModuleCat.{u} R) ⥤ Sheaf J (ModuleCat.{u} R) :=
  F.sheafPushforwardContinuous (ModuleCat.{u} R) J K

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates.restriction F R J K
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R K
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction.constantIso F R J K (ModuleCat.of R R)

variable [(F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).Linear R]
  [PreservesFiniteLimits (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K)]
  [PreservesFiniteColimits (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K)]

theorem element (M : Sheaf K (ModuleCat.{u} R)) (α : Ext.{max u z} A M 0) :
    IntegralComparison.Ext.ZeroPresheafSections.equivalence R J ((T).obj M)
      (IntegralComparison.Ext.ExtPullbackComparison.component T R A (e).inv 0 M α) =
    (PresheafSectionRestriction.map F R J K).app M
      (IntegralComparison.Ext.ZeroPresheafSections.equivalence R K M α) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective A M).2 α
  have hm := IntegralComparison.Ext.ExtPullbackComparison.component_mk T R A (e).inv a
  have hs := IntegralComparison.Ext.ZeroPresheafSections.equivalence_mk R K M a
  have ht := IntegralComparison.Ext.ZeroPresheafSections.equivalence_mk R J ((T).obj M) ((e).inv ≫ (T).map a)
  exact (congrArg (IntegralComparison.Ext.ZeroPresheafSections.equivalence R J ((T).obj M)) hm).trans
    (ht.trans ((congrArg ULift.up
      (ConstantSection.SectionRestriction.adjunction F R J K (ModuleCat.of R R) M a)).trans
        (congrArg (fun x => (PresheafSectionRestriction.map F R J K).app M x) hs.symm)))

theorem component (M : Sheaf K (ModuleCat.{u} R)) :
    IntegralComparison.Ext.ExtPullbackComparison.component T R A (e).inv 0 M ≫
      ((IntegralComparison.Ext.ZeroPresheafSections.iso R J).app ((T).obj M)).hom =
    ((IntegralComparison.Ext.ZeroPresheafSections.iso R K).app M).hom ≫
      (PresheafSectionRestriction.map F R J K).app M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact element F R J K M

theorem complexes (L : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ) :
    IntegralComparison.Ext.ExtPullbackComparison.complexMap T R A (e).inv L ≫
      (PresheafSectionComplex.complexIso R J
        (((T).mapHomologicalComplex (.up ℕ)).obj L)).hom =
    (PresheafSectionComplex.complexIso R K L).hom ≫
      PresheafSectionRestriction.complexMap F R J K L := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component F R J K (L.X i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates
