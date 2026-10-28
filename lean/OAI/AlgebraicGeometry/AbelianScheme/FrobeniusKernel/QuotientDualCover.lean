import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Quotient Dual Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualCover.Construction

noncomputable section

/-! The Poincare family cover is an actual finite flat surjective
homomorphism, and the schemes used for its action equations are proper. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

theorem groupHom_whiskerRight {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {X Y Z : C} [GrpObj X] [GrpObj Y] [GrpObj Z] (p : X ⟶ Y) [IsMonHom p] :
    IsMonHom (p ▷ Z) := inferInstance

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

def quotientDualPoincareCover : D.abelian.scheme ⊗ B.scheme ⟶
    (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme ⊗ B.scheme :=
  (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme

instance quotientDualPoincareCover_monHom : IsMonHom (quotientDualPoincareCover D f) := by
  exact @groupHom_whiskerRight (Over (Spec (.of k))) inferInstance inferInstance inferInstance
    D.abelian.scheme (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme B.scheme
    D.abelian.group (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.group B.group
    (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection (CharacterQuotient.Construction.isogenyCharacterQuotient D f).groupHom

instance quotientDualPoincareCover_finite : IsFinite (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@IsFinite)
    (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection (𝟙 B.scheme) (CharacterQuotient.Construction.isogenyCharacterQuotient D f).finite
    (inferInstanceAs (IsFinite (𝟙 B.scheme.left)))

instance quotientDualPoincareCover_flat : Flat (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  have : Flat (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Flat (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorFlat (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection (𝟙 B.scheme)

instance quotientDualPoincareCover_surjective : Surjective (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  have : Surjective (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Surjective (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorSurjective (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection (𝟙 B.scheme)

instance quotientDualPoincareCover_fp : LocallyOfFinitePresentation (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@LocallyOfFinitePresentation)
    (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection (𝟙 B.scheme) (CharacterQuotient.Construction.isogenyCharacterQuotient D f).finitelyPresented
    (inferInstanceAs (LocallyOfFinitePresentation (𝟙 B.scheme.left)))

instance quotientDualPoincareSource_proper : IsProper (D.abelian.scheme ⊗ B.scheme).hom := by
  dsimp
  infer_instance

instance quotientDualPoincareTarget_noetherian :
    IsLocallyNoetherian ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme ⊗ B.scheme).left :=
  Picard.PoincareBundle.Product.Noetherian.product_noetherian (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme B.scheme

instance quotientDualPoincareKernel_proper : IsProper (Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (quotientDualPoincareCover D f)
  infer_instance

instance quotientDualPoincareAction_proper :
    IsProper ((D.abelian.scheme ⊗ B.scheme) ⊗ Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  dsimp only [Over.tensorObj_hom]
  infer_instance

instance quotientDualPoincareTriple_proper :
    IsProper (((D.abelian.scheme ⊗ B.scheme) ⊗ Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)) ⊗
      Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  dsimp only [Over.tensorObj_hom]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualCover.Construction
