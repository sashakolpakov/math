import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotient
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Normalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian

/-! # Translation Quotient Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample

noncomputable section

/-! The actual normalized difference line descends to the quotient by
the full translation kernel, with its original pullback and identity
normalization retained. No relative cube identity is used here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq.Geometric

variable {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme} (Q : TranslationQuotient.AmpleTranslationQuotient A L P)

theorem TranslationQuotient.AmpleTranslationQuotient.difference_values_equal {T : Over S} (a b : T ⟶ A.scheme)
    (hab : a ≫ Q.isogeny.hom = b ≫ Q.isogeny.hom) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b := by
  have hz : (a * b⁻¹) ≫ Q.isogeny.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]
  obtain ⟨z, he, _⟩ := (Q.kernel T (a * b⁻¹)).mp hz
  apply Picard.ThetaConstruction.RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_eq_of_div_zero A L a b
  exact (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P T (a * b⁻¹)).mpr ⟨z, he⟩

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_product_locallyNoetherian :
    IsLocallyNoetherian (Q.target.scheme ⊗ A.scheme).left :=
  Picard.PoincareBundle.Product.Noetherian.product_noetherian Q.target.scheme A.scheme

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_etale : Etale Q.isogeny.hom.left := Q.etale

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_product_affine : IsAffineHom (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : IsAffineHom (Over.Hom.left (𝟙 A.scheme)) :=
    inferInstanceAs (IsAffineHom (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorAffine Q.isogeny.hom (𝟙 A.scheme)

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_product_flat : Flat (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Flat (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Flat (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorFlat Q.isogeny.hom (𝟙 A.scheme)

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_product_surjective : Surjective (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Surjective (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Surjective (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorSurjective Q.isogeny.hom (𝟙 A.scheme)

local instance TranslationQuotient.AmpleTranslationQuotient.quotient_product_finitelyPresented :
    LocallyOfFinitePresentation (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : LocallyOfFinitePresentation (Over.Hom.left (𝟙 A.scheme)) :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@LocallyOfFinitePresentation) Q.isogeny.hom
    (𝟙 A.scheme) inferInstance inferInstance

def TranslationQuotient.AmpleTranslationQuotient.descendedDifference : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme Q.target.scheme :=
  (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).rigidifiedQuotientLine Q.isogeny.hom
    (fun {_T} _ a b hab => Q.difference_values_equal a b hab)

def TranslationQuotient.AmpleTranslationQuotient.descendedDifference_pullbackIso :
    (Scheme.Modules.pullback (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left).obj
      Q.descendedDifference.bundle.sheaf ≅ (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).normalizedQuotientLinePullbackIso Q.isogeny.hom
    (fun {_T} _ a b hab => Q.difference_values_equal a b hab)

theorem TranslationQuotient.AmpleTranslationQuotient.descendedDifference_pullback_class :
    Line.Bundles.LineBundle.pullbackClass (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf Q.descendedDifference.bundle) =
        Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) :=
  Quotient.sound ⟨Q.descendedDifference_pullbackIso⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample
