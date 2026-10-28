import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSchemeImage
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.SchemeDominance
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverDominantClosedFactorization
import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Scheme Image Group Operations -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroupOperations

noncomputable section

/-! Multiplication and inversion descend to the actual scheme-theoretic
image of a quasi-compact group homomorphism over a field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

namespace Construction

universe u
variable {K : Type u} [Field K] {X Y : Over (Spec (CommRingCat.of K))}
  [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] [QuasiCompact f.left]

theorem overSchemeImage_exists_mul : ∃ m : OverSchemeImage.Construction.overSchemeImage f ⊗ OverSchemeImage.Construction.overSchemeImage f ⟶ OverSchemeImage.Construction.overSchemeImage f,
    m ≫ OverSchemeImage.Construction.overSchemeImageInclusion f =
      (OverSchemeImage.Construction.overSchemeImageInclusion f ⊗ₘ OverSchemeImage.Construction.overSchemeImageInclusion f) ≫ MonObj.mul := by
  have := Product.SchemeDominance.Construction.tensorMap_schemeDominant (OverSchemeImage.Construction.overSchemeImageFactor f) (OverSchemeImage.Construction.overSchemeImageFactor f)
  apply OverDominantClosedFactorization.Construction.overFactorThroughClosed_of_dominant
    (OverSchemeImage.Construction.overSchemeImageFactor f ⊗ₘ OverSchemeImage.Construction.overSchemeImageFactor f)
    ((OverSchemeImage.Construction.overSchemeImageInclusion f ⊗ₘ OverSchemeImage.Construction.overSchemeImageInclusion f) ≫ MonObj.mul)
    (OverSchemeImage.Construction.overSchemeImageInclusion f) (MonObj.mul ≫ OverSchemeImage.Construction.overSchemeImageFactor f)
  rw [tensorHom_comp_tensorHom_assoc, OverSchemeImage.Construction.overSchemeImageFactor_inclusion,
    ← IsMonHom.mul_hom, Category.assoc, OverSchemeImage.Construction.overSchemeImageFactor_inclusion]

theorem overSchemeImage_exists_inv : ∃ r : OverSchemeImage.Construction.overSchemeImage f ⟶ OverSchemeImage.Construction.overSchemeImage f,
    r ≫ OverSchemeImage.Construction.overSchemeImageInclusion f = OverSchemeImage.Construction.overSchemeImageInclusion f ≫ GrpObj.inv := by
  apply OverDominantClosedFactorization.Construction.overFactorThroughClosed_of_dominant (OverSchemeImage.Construction.overSchemeImageFactor f)
    (OverSchemeImage.Construction.overSchemeImageInclusion f ≫ GrpObj.inv) (OverSchemeImage.Construction.overSchemeImageInclusion f)
    (GrpObj.inv ≫ OverSchemeImage.Construction.overSchemeImageFactor f)
  rw [← Category.assoc, OverSchemeImage.Construction.overSchemeImageFactor_inclusion, ← GrpObj.inv_hom,
    Category.assoc, OverSchemeImage.Construction.overSchemeImageFactor_inclusion]

def overSchemeImageOne : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ OverSchemeImage.Construction.overSchemeImage f :=
  MonObj.one ≫ OverSchemeImage.Construction.overSchemeImageFactor f

omit [QuasiCompact f.left] in
theorem overSchemeImageOne_inclusion : overSchemeImageOne f ≫ OverSchemeImage.Construction.overSchemeImageInclusion f =
    MonObj.one := by
  rw [overSchemeImageOne, Category.assoc, OverSchemeImage.Construction.overSchemeImageFactor_inclusion, IsMonHom.one_hom]

def overSchemeImageMul : OverSchemeImage.Construction.overSchemeImage f ⊗ OverSchemeImage.Construction.overSchemeImage f ⟶ OverSchemeImage.Construction.overSchemeImage f :=
  (overSchemeImage_exists_mul f).choose

theorem overSchemeImageMul_inclusion : overSchemeImageMul f ≫ OverSchemeImage.Construction.overSchemeImageInclusion f =
    (OverSchemeImage.Construction.overSchemeImageInclusion f ⊗ₘ OverSchemeImage.Construction.overSchemeImageInclusion f) ≫ MonObj.mul :=
  (overSchemeImage_exists_mul f).choose_spec

def overSchemeImageInv : OverSchemeImage.Construction.overSchemeImage f ⟶ OverSchemeImage.Construction.overSchemeImage f :=
  (overSchemeImage_exists_inv f).choose

theorem overSchemeImageInv_inclusion : overSchemeImageInv f ≫ OverSchemeImage.Construction.overSchemeImageInclusion f =
    OverSchemeImage.Construction.overSchemeImageInclusion f ≫ GrpObj.inv :=
  (overSchemeImage_exists_inv f).choose_spec

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroupOperations
