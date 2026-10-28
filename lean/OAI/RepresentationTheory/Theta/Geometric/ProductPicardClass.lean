import OAI.RepresentationTheory.Theta.Geometric.ProductFrames
import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback

/-! # Product Picard Class -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductPicardClass

noncomputable section

/-! Finite native theta tensor products and their intrinsic Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ}

def thetaProductBundle : {r : ℕ} → (Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X
  | 0, f => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (f 0) (AlgebraicQuotient.algebraicTwistBundle n 1)
  | r + 1, f => (thetaProductBundle (fun k : Fin (r + 1) => f k.castSucc)).tensor
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (f (Fin.last (r + 1))) (AlgebraicQuotient.algebraicTwistBundle n 1))

theorem thetaProductBundle_sheaf {r : ℕ} (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :
    (ProductPicardClass.thetaProductBundle f).sheaf = ProductFrames.thetaProductModule f := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (ProductPicardClass.thetaProductBundle (fun k : Fin (r + 1) => f k.castSucc)).sheaf _ = _
      rw [ih]
      rfl

theorem thetaProductBundle_class {r : ℕ} (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ProductPicardClass.thetaProductBundle f) =
      ∏ k, Picard.PicardPullback.picardPullback (f k) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1)) := by
  induction r with
  | zero => rw [Fin.prod_univ_one]; rfl
  | succ r ih =>
      change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ProductPicardClass.thetaProductBundle (fun k : Fin (r + 1) => f k.castSucc)) *
        Picard.PicardPullback.picardPullback (f (Fin.last (r + 1))) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1)) = _
      rw [Fin.prod_univ_castSucc, ih]

theorem thetaProduct_classes_eq_of_iso {r s : ℕ}
    (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (g : Fin (s + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (h : Nonempty (ProductFrames.thetaProductModule f ≅ ProductFrames.thetaProductModule g)) :
    (∏ k, Picard.PicardPullback.picardPullback (f k) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1))) =
      ∏ k, Picard.PicardPullback.picardPullback (g k) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1)) := by
  rw [← thetaProductBundle_class, ← thetaProductBundle_class]
  apply Quotient.sound
  obtain ⟨e⟩ := h
  exact ⟨eqToIso (thetaProductBundle_sheaf f) ≪≫ e ≪≫ (eqToIso (thetaProductBundle_sheaf g)).symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric.ProductPicardClass
