import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageMultiplication
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageHomogeneity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedHomogeneousEvaluation

/-! # Point Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.PointProducts.Construction

noncomputable section

/-! Both tensor products of the actual Picard-image point lines are
constructed from the descended family, its group law and its homogeneity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

def picardImagePointLine {T : Over (Spec (.of k))} (x : T ⟶ C) (a : T ⟶ B) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left :=
  (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac).pullback (lift x a).left

set_option backward.isDefEq.respectTransparency false in
theorem picardImagePointLine_tensor_left {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]
    (x y : T ⟶ C) (a : T ⟶ B) :
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (picardImagePointLine D βv hβv βh hβh q i hfac y a).sheaf ≅
        (picardImagePointLine D βv hβv βh hβh q i hfac (x * y) a).sheaf) := by
  let Q := ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
  have h := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (HomogeneousPicardEvaluation.Construction.homogeneousEvaluationSection B a).left)
    (ProductPicard.ImageMultiplication.Construction.normalizedProductPicardImageLine_class_mul D βv hβv βh hβh q i hfac x y)
  rw [map_mul] at h
  change HomogeneousPicardEvaluation.Construction.nativeHomogeneous_evaluateClass B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line (x * y))) a =
    HomogeneousPicardEvaluation.Construction.nativeHomogeneous_evaluateClass B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x)) a *
      HomogeneousPicardEvaluation.Construction.nativeHomogeneous_evaluateClass B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line y)) a at h
  rw [RigidifiedHomogeneousEvaluation.Construction.rigidifiedFamily_evaluation_class, RigidifiedHomogeneousEvaluation.Construction.rigidifiedFamily_evaluation_class,
    RigidifiedHomogeneousEvaluation.Construction.rigidifiedFamily_evaluation_class] at h
  exact Quotient.exact h.symm

omit [GrpObj C] [IsMonHom q] in
set_option backward.isDefEq.respectTransparency false in
theorem picardImagePointLine_tensor_right {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]
    (x : T ⟶ C) (a b : T ⟶ B) :
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (picardImagePointLine D βv hβv βh hβh q i hfac x b).sheaf ≅
        (picardImagePointLine D βv hβv βh hβh q i hfac x (a * b)).sheaf) :=
  Quotient.exact (RigidifiedHomogeneousEvaluation.Construction.rigidifiedFamily_pointClass_mul
    (ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac) x a
    (ProductPicard.ImageHomogeneity.Construction.normalizedProductPicardImageLine_homogeneous D βv hβv βh hβh q i hfac) b).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.PointProducts.Construction
