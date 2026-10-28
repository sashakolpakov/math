import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalSectionsIn
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeStructure
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Birational Structure -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalStructure.Construction.BirationalStructureSheaf

noncomputable section

/-! Descent of the structure sheaf along a proper morphism with a dense
lift of the generic point of a normal integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [IsReduced X] [IsIntegral Y]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
variable (f : X ⟶ Y) [IsProper f]
variable (g : Spec Y.functionField ⟶ X) [IsDominant g]
variable (hg : g ≫ f = Y.fromSpecStalk (genericPoint Y))

include hY hg

theorem isIso_app_affine (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIso (f.app U) := by
  have := NormalSectionsIn.Construction.NormalSections.affine hY U hU
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : IsIso U.toSpecΓ := hU.isoSpec.isIso_hom
  have : IsIso U.toSpecΓ.appTop := by
    rw [Scheme.Opens.toSpecΓ_appTop]
    infer_instance
  have := GenericLift.Construction.GenericLiftRestriction.isDominant_lift f g hg U
  have hi := ProperBirational.Construction.ProperBirationalFunctions.isIso_appTop (f ∣_ U ≫ U.toSpecΓ)
    (GenericLift.Construction.GenericLiftRestriction.lift f g hg U)
    (GenericLift.Construction.GenericLiftRestriction.lift_comp_affine f g hg U)
  rw [Scheme.Hom.comp_appTop] at hi
  have hir : IsIso (f ∣_ U).appTop :=
    (isIso_comp_left_iff U.toSpecΓ.appTop (f ∣_ U).appTop).mp hi
  let t := X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
  have ht : IsIso t := X.presheaf.map_isIso _
  have hc : IsIso (f.app (U.ι ''ᵁ ⊤) ≫ t) := by
    rw [← morphismRestrict_appTop]
    exact hir
  have hc' : IsIso (f.app (U.ι ''ᵁ ⊤)) :=
    (isIso_comp_right_iff (f.app (U.ι ''ᵁ ⊤)) t).mp hc
  exact (congrArg (fun W : Y.Opens => IsIso (f.app W)) U.ι_image_top).mp hc'

theorem isIso_ringSheaf : IsIso f.toRingCatSheafHom := by
  let B := {U : Y.Opens // IsAffineOpen U ∧ Nonempty U}
  have hB : Opens.IsBasis (Set.range (fun U : B => U.1)) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro U y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact ⟨V, ⟨⟨V, hV, ⟨⟨y, hyV⟩⟩⟩, rfl⟩, hyV, hVU⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro U
  have : Nonempty U.1 := U.2.2
  have hi := isIso_app_affine hY f g hg U.1 U.2.1
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective (f.app U.1)).mp hi

theorem isIso_app (U : Y.Opens) : IsIso (f.app U) := by
  have hs : IsIso f.toRingCatSheafHom := isIso_ringSheaf hY f g hg
  let e := @asIso _ _ _ _ f.toRingCatSheafHom hs
  let e' := (sheafToPresheaf _ _).mapIso e
  have hi : IsIso (f.toRingCatSheafHom.hom.app (.op U)) := (e'.app (.op U)).isIso_hom
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective (f.toRingCatSheafHom.hom.app (.op U))).mp hi

theorem isIso_unit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mp (isIso_app hY f g hg U)

def iso : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (isIso_unit hY f g hg)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalStructure.Construction.BirationalStructureSheaf
