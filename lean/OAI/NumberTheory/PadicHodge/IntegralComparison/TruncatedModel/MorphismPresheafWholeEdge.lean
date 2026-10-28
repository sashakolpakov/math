import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents

/-! # Morphism Presheaf Whole Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafWholeEdge

noncomputable section

/-! The actual model cover refinements preserve arbitrary section
cones as whole cochain maps, before crystalline specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]

abbrev source (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K) :=
  GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₁)
    (MorphismRefinement.source p k n u) K M η

abbrev target (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M ⟶ K) :=
  GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₂)
    (MorphismRefinement.target p k n u) K M η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafWholeEdge
