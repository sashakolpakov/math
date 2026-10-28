import OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafBridge
import OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport
import OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Scalar Closed Support -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarClosedSupport

noncomputable section

/-! # Forgetting scalars retains the actual sheaf of sections with closed support -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "J" => Opens.grothendieckTopology Y
local notation "G" => sheafCompose J (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Scalar forgetting preserves finite limits on the actual sheaf categories. -/
instance scalarSheafCompose_preservesFiniteLimits : PreservesFiniteLimits (G) := by
  let : PreservesFiniteLimits ((G) ⋙ sheafToPresheaf J AddCommGrpCat.{0}) := by
    change PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{0} R) ⋙
      (Functor.whiskeringRight (Opens Y)ᵒᵖ (ModuleCat.{0} R) AddCommGrpCat.{0}).obj
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (G)
    (sheafToPresheaf J AddCommGrpCat.{0})

set_option backward.isDefEq.respectTransparency false in
/-- The original restriction-pushforward and the literal intersection model agree. -/
def scalarOpenRestrictionIso (O : Opens Y) (F : TopCat.Sheaf (ModuleCat.{0} R) Y) :
    (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.openRestrictionPushforward Y O).obj ((G).obj F) ≅
      (G).obj (CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardSheaf O F) :=
  (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{0}).preimageIso <|
    NatIso.ofComponents (fun U => AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso
      Y O U.unop ((G).obj F)) (by
        intro U V i
        exact AlgebraicTopology.Support.SectionRestrictionConeNaturality.TopCat.Sheaf.supportedOutsideIntersectionIso_naturality
          Y O i.unop ((G).obj F))

set_option backward.isDefEq.respectTransparency false in
/-- Both actual restriction maps restrict a section to the same intersection open. -/
theorem scalarOpenRestrictionIso_restriction (O : Opens Y)
    (F : TopCat.Sheaf (ModuleCat.{0} R) Y) :
    (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward Y O).app ((G).obj F) ≫
        (scalarOpenRestrictionIso R Y O F).hom =
      (G).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf.toOpenRestrictionPushforward_intersection Y O U.unop ((G).obj F)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-forgotten native support kernel is the unchanged original support kernel. -/
def scalarClosedSupportIso (O : Opens Y) (F : TopCat.Sheaf (ModuleCat.{0} R) Y) :
    (G).obj (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F) ≅
      (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y O).obj ((G).obj F) :=
  PreservesKernel.iso (G) (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F) ≪≫
    kernel.mapIso ((G).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F))
      ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward Y O).app ((G).obj F))
      (Iso.refl _) (scalarOpenRestrictionIso R Y O F).symm (by
        apply (cancel_mono (scalarOpenRestrictionIso R Y O F).hom).mp
        simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
          Iso.refl_hom, Category.id_comp]
        exact (scalarOpenRestrictionIso_restriction R Y O F).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The support comparison preserves the actual inclusion into all sections. -/
theorem scalarClosedSupportIso_inclusion (O : Opens Y)
    (F : TopCat.Sheaf (ModuleCat.{0} R) Y) :
    (scalarClosedSupportIso R Y O F).hom ≫
        (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).app ((G).obj F) =
      (G).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F) := by
  simp only [scalarClosedSupportIso, Iso.trans_hom, kernel.mapIso,
    AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion,
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion, Category.assoc,
    kernel.lift_ι, Iso.refl_hom, Category.comp_id, PreservesKernel.iso_hom,
    kernelComparison_comp_ι]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarClosedSupport
