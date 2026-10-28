import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex

/-! # Morphism Presheaf Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement

noncomputable section

/-! The two geometric cover refinements act on an arbitrary
presheaf complex, before choosing crystalline coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]

def sourceMap (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ A) ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (CechSliceResolution.opens p k n X₁) K).total (.up ℕ) ⟶
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u)
        (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ) :=
  GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₁)
    (MorphismRefinement.source p k n u) K

def targetMap (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ A) ℕ) :=
  GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₂)
    (MorphismRefinement.target p k n u) K

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement
