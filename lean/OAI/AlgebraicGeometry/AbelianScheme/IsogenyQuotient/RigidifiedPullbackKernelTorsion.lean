import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.PullbackKernelTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedBundleRelativeZero
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps

/-! # Rigidified Pullback Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPullbackKernelTorsion.Construction

noncomputable section

/-! A normalized line whose relative class is killed by isogeny
pullback has torsion bounded by the actual isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps.Construction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  {T : Over (Spec (.of k))} [IsAffine T.left] [IsLocallyNoetherian T.left]

set_option backward.isDefEq.respectTransparency false in
theorem rigidifiedLine_pullback_kernel_torsion
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B).left)
    (e : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ B)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T)
    (n : ℕ) (hn : ∀ (U : Over (Spec (.of k))) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) ^ n = 1 := by
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
  exact Product.PullbackKernelTorsion.Construction.productPullbackTrivialClass_torsion f T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    (RigidifiedBundleRelativeZero.Construction.rigidifiedBundle_class_trivial_of_relative_zero A _ e' h') n hn

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPullbackKernelTorsion.Construction
