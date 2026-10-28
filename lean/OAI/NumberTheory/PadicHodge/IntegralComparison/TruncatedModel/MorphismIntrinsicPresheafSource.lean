import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedInferred
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafFrameGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

/-! # Morphism Intrinsic Presheaf Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicPresheafSource.Intrinsic

noncomputable section

/-! Frame comparison and global-edge cancellation composed before choosing
native crystalline coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance directCoefficientRing :
    Ring (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ULift.ring

local instance directCoefficientCategory :
    Category (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  @ModuleCat.moduleCategory (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring)

local instance directCoefficientAbelian :
    Abelian (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  @ModuleCat.abelian (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring)

abbrev source
    (F : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (φ : F ⟶ K)
    (ψ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj F) ⟶
      (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K))
    (hψ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).map φ) = ψ)
    (M : CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K)
    (a : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₁) K).total (.up ℕ))
    (c : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ))
    (ha : a = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map
      (CechSliceResolution.opens p k n X₁) K M η)
    (hc : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)
      M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) K M η) = c)
    (q : ℕ) (N : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (i : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₁) K).total (.up ℕ)).homology q ⟶ N)
    (h : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ)).homology q ⟶ N)
    (j : M.homology q ⟶ N)
    [Epi (HomologicalComplex.homologyMap a q)]
    (hh : HomologicalComplex.homologyMap c q ≫ h = j)
    (hi : HomologicalComplex.homologyMap a q ≫ i = j)
    (K₀ K₁ : CochainComplex (ModuleCat.{0} (WittVector p k)) ℕ)
    (e₀ : ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj K₀ ≅
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (CechSliceResolution.opens p k n X₁) F).total (.up ℕ))
    (e₁ : ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj K₁ ≅
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u)
        (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
          (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj F)).total (.up ℕ)) :=
  @ExactRefinedGlobal.Comparison.source
    (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring))
    (@ModuleCat.moduleCategory (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring))
    (@ModuleCat.abelian (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring))
    _ _ _ q _ _ _
    (IntrinsicPresheafFrameGlobal.MorphismIntrinsicComparison.source p k n u
      F K φ ψ hψ M η a c ha hc q N i h j hh hi).symm
    (ModuleCat.{0} (WittVector p k))
    (@ModuleCat.moduleCategory (WittVector p k) (WittVector.instCommRing p k).toRing)
    (@ModuleCat.abelian (WittVector p k) (WittVector.instCommRing p k).toRing)
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) _ _ _ _ e₀ e₁

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicPresheafSource.Intrinsic
