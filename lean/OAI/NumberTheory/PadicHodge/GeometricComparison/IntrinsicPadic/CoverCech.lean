import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindex

/-! # Cover Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoverCech.IntrinsicPadicGeometricCoverCech

noncomputable section

/-! The actual common affine-pair refinement compares both chosen
coordinate-cover Cech totals to the paired coefficient diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe w z
variable {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  (u : X₁ ⟶ X₂)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

def sourceMap (P : X₁.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ) :
    CechCone.Total.CechConeTotal.total (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) P ⟶
      CechCone.Total.CechConeTotal.total U ((Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ P) :=
  CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
    (Cover.IntrinsicPadicGeometricCoverRefinements.source p u) P

def targetMap (P : X₂.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ) :
    CechCone.Total.CechConeTotal.total (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) P ⟶
      CechCone.Total.CechConeTotal.total U ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ P) :=
  CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
    (Cover.IntrinsicPadicGeometricCoverRefinements.target p u) P

theorem source_augmentation (P : X₁.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (M : CochainComplex A ℕ) (η : (Functor.const X₁.left.affineOpensᵒᵖ).obj M ⟶ P) :
    CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) P M η ≫ sourceMap p u P =
      CechCone.Total.CechConeTotal.augmentation U ((Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ P) M
        (Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.source u.left).op η) :=
  CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.augmentation (Affine.MapPairs.AffineMapPairs.source u.left) U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
    (Cover.IntrinsicPadicGeometricCoverRefinements.source p u) P M η

theorem target_augmentation (P : X₂.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (M : CochainComplex A ℕ) (η : (Functor.const X₂.left.affineOpensᵒᵖ).obj M ⟶ P) :
    CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) P M η ≫ targetMap p u P =
      CechCone.Total.CechConeTotal.augmentation U ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ P) M
        (Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.target u.left).op η) :=
  CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.augmentation (Affine.MapPairs.AffineMapPairs.target u.left) U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
    (Cover.IntrinsicPadicGeometricCoverRefinements.target p u) P M η

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoverCech.IntrinsicPadicGeometricCoverCech
