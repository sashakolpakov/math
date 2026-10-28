import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindex

/-! # Morphism Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement

noncomputable section

/-! Both projections of the common affine-pair cover induce augmented refinement maps of the original full Cech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w z
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] (u : X₁ ⟶ X₂)

def source : FormalCoproduct.mk (MorphismCover.Index p k n u)
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).obj ∘ MorphismCover.pairs p k n u) ⟶
      FormalCoproduct.mk (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X₁) (CechSliceResolution.opens p k n X₁) where
  f := MorphismCover.sourceIndex p k n u
  φ i := homOfLE (MorphismCover.le_source p k n u i)
def target : FormalCoproduct.mk (MorphismCover.Index p k n u)
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).obj ∘ MorphismCover.pairs p k n u) ⟶
      FormalCoproduct.mk (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X₂) (CechSliceResolution.opens p k n X₂) where
  f := MorphismCover.targetIndex p k n u
  φ _ := 𝟙 _

variable [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u

def sourceMap (P : X₁.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ) :
    GeometricComparison.CechCone.Total.CechConeTotal.total (CechSliceResolution.opens p k n X₁) P ⟶
      GeometricComparison.CechCone.Total.CechConeTotal.total U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ P) :=
  GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) U
    (CechSliceResolution.opens p k n X₁) (source p k n u) P

def targetMap (P : X₂.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ) :
    GeometricComparison.CechCone.Total.CechConeTotal.total (CechSliceResolution.opens p k n X₂) P ⟶
      GeometricComparison.CechCone.Total.CechConeTotal.total U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ P) :=
  GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) U
    (CechSliceResolution.opens p k n X₂) (target p k n u) P

omit [Fintype k] [CharP k p] in
theorem source_augmentation (P : X₁.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (M : CochainComplex A ℕ) (η : (Functor.const X₁.left.affineOpensᵒᵖ).obj M ⟶ P) :
    GeometricComparison.CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.opens p k n X₁) P M η ≫ sourceMap p k n u P =
      GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ P) M
        (Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op η) :=
  GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) U
    (CechSliceResolution.opens p k n X₁) (source p k n u) P M η

omit [Fintype k] [CharP k p] in
theorem target_augmentation (P : X₂.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (M : CochainComplex A ℕ) (η : (Functor.const X₂.left.affineOpensᵒᵖ).obj M ⟶ P) :
    GeometricComparison.CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.opens p k n X₂) P M η ≫ targetMap p k n u P =
      GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ P) M
        (Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op η) :=
  GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) U
    (CechSliceResolution.opens p k n X₂) (target p k n u) P M η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement
