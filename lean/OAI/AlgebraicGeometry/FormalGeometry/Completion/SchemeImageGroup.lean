import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroupOperations
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject

/-! # Scheme Image Group -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroup

noncomputable section

/-! The scheme-theoretic image of a quasi-compact group homomorphism
over a field is an actual group scheme. Its closed inclusion and its
dominant factor map are group homomorphisms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

namespace Construction

universe u
variable {K : Type u} [Field K] {X Y : Over (Spec (CommRingCat.of K))}
  [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] [QuasiCompact f.left]

instance overSchemeImageGrpObj : GrpObj (OverSchemeImage.Construction.overSchemeImage f) :=
  GroupSubobject.Construction.grpObjOfMono (OverSchemeImage.Construction.overSchemeImageInclusion f) (SchemeImageGroupOperations.Construction.overSchemeImageOne f)
    (SchemeImageGroupOperations.Construction.overSchemeImageMul f) (SchemeImageGroupOperations.Construction.overSchemeImageInv f) (SchemeImageGroupOperations.Construction.overSchemeImageOne_inclusion f)
    (SchemeImageGroupOperations.Construction.overSchemeImageMul_inclusion f) (SchemeImageGroupOperations.Construction.overSchemeImageInv_inclusion f)

instance overSchemeImageInclusion_isMonHom : IsMonHom (OverSchemeImage.Construction.overSchemeImageInclusion f) :=
  GroupSubobject.Construction.grpObjOfMono_isMonHom (OverSchemeImage.Construction.overSchemeImageInclusion f) (SchemeImageGroupOperations.Construction.overSchemeImageOne f)
    (SchemeImageGroupOperations.Construction.overSchemeImageMul f) (SchemeImageGroupOperations.Construction.overSchemeImageInv f) (SchemeImageGroupOperations.Construction.overSchemeImageOne_inclusion f)
    (SchemeImageGroupOperations.Construction.overSchemeImageMul_inclusion f) (SchemeImageGroupOperations.Construction.overSchemeImageInv_inclusion f)

instance overSchemeImageFactor_isMonHom : IsMonHom (OverSchemeImage.Construction.overSchemeImageFactor f) where
  one_hom := rfl
  mul_hom := by
    apply (cancel_mono (OverSchemeImage.Construction.overSchemeImageInclusion f)).mp
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      OverSchemeImage.Construction.overSchemeImageFactor_inclusion]

instance overSchemeImageIsCommMonObj [IsCommMonObj Y] : IsCommMonObj (OverSchemeImage.Construction.overSchemeImage f) where
  mul_comm := by
    apply (cancel_mono (OverSchemeImage.Construction.overSchemeImageInclusion f)).mp
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroup
