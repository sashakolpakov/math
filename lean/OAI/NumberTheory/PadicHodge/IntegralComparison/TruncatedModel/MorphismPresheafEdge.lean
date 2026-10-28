import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents

/-! # Morphism Presheaf Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafEdge

noncomputable section

/-! The actual model cover refinements preserve arbitrary section
cones, before specializing to the crystalline resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]

abbrev source_component (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K) (q : ℕ) :=
  GeometricComparison.CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₁)
    (MorphismRefinement.source p k n u) K M η q

abbrev target_component (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M ⟶ K) (q : ℕ) :=
  GeometricComparison.CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents.augmentation (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
    (MorphismCover.pairs p k n u)
    (CechSliceResolution.opens p k n X₂)
    (MorphismRefinement.target p k n u) K M η q

omit [Fintype k] [CharP k p] in
theorem source_native_component (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K) (q : ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.opens p k n X₁) K M η).f q ≫
      (MorphismPresheafRefinement.sourceMap p k n u K).f q =
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex
        (.up ℕ)).obj K) M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) K M η)).f q :=
  source_component p k n u K M η q

omit [Fintype k] [CharP k p] in
theorem target_native_component (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M ⟶ K) (q : ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.opens p k n X₂) K M η).f q ≫
      (MorphismPresheafRefinement.targetMap p k n u K).f q =
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex
        (.up ℕ)).obj K) M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) K M η)).f q :=
  target_component p k n u K M η q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafEdge
