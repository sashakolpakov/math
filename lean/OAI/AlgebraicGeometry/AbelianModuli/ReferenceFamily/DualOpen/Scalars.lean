import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Scalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Scalars

noncomputable section

/-! The native scalar map restricts to each actual family open,
and the constructed product chart intertwines its scalar pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (c : ℂ)

def dualOpenScalar : U.toScheme ⟶ U.toScheme :=
  (Dual.Scalars.dualFamilyScalar X c).left.resLE U U (Dual.Scalars.dualFamilyScalar_preimage X c U).ge

theorem dualOpenScalar_ι : dualOpenScalar X U c ≫ U.ι = U.ι ≫ (Dual.Scalars.dualFamilyScalar X c).left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem dualOpenProductIso_scalar :
    (Product.dualOpenProductIso X U).hom ≫ dualOpenScalar X U c =
      (Dual.Scalars.dualFamilyScalar (Product.dualReducedOpenOver X U) c).left ≫ (Product.dualOpenProductIso X U).hom := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, dualOpenScalar_ι, ← Category.assoc, Product.dualOpenProductIso_hom_ι,
    Category.assoc, Product.dualOpenProductIso_hom_ι]
  have h : Dual.Scalars.dualFamilyScalar (Product.dualReducedOpenOver X U) c ≫
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ Product.dualReducedOpenInclusion X U) =
    (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ Product.dualReducedOpenInclusion X U) ≫ Dual.Scalars.dualFamilyScalar X c := by
    simp only [Dual.Scalars.dualFamilyScalar, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  exact (congrArg (fun f : LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X U ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) h).symm

def dualOpenScalarSection : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U) →+* Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U) :=
  U.topIso.hom.hom.comp ((dualOpenScalar X U c).appTop.hom.comp U.topIso.inv.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Scalars
