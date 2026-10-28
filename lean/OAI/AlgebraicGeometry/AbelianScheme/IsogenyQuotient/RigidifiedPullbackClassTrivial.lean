import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedBundleRelativeZero
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps

/-! # Rigidified Pullback Class Trivial -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPullbackClassTrivial.Construction

noncomputable section

/-! The pullback of a normalized line is actually trivial whenever its
relative Picard pullback is zero, over a locally noetherian parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps.Construction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (f : A ⟶ B) [IsMonHom f]
  {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]

set_option backward.isDefEq.respectTransparency false in
theorem rigidifiedLine_pullback_class_trivial
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B).left)
    (e : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ B)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 T) ⊗ₘ f).left) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  have hs : (lift (𝟙 T) (1 : T ⟶ A)).left ≫ ((𝟙 T) ⊗ₘ f).left =
      (𝟙 T.left) ≫ (lift (𝟙 T) (1 : T ⟶ B)).left := by
    rw [Category.id_comp]
    have hs' : lift (𝟙 T) (1 : T ⟶ A) ≫ ((𝟙 T) ⊗ₘ f) = lift (𝟙 T) (1 : T ⟶ B) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    exact congrArg Over.Hom.left hs'
  let e' := FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso ((𝟙 T) ⊗ₘ f).left
    (lift (𝟙 T) (1 : T ⟶ A)).left (𝟙 T.left) (lift (𝟙 T) (1 : T ⟶ B)).left hs L.sheaf e
  have h' : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 T) ⊗ₘ f).left)) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
    have hr := (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans h
    simp only [Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf] at hr
    rw [id_tensorHom]
    exact hr
  exact RigidifiedBundleRelativeZero.Construction.rigidifiedBundle_class_trivial_of_relative_zero A _ e' h'

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPullbackClassTrivial.Construction
