import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedInferred
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare

/-! # Intrinsic Presheaf Frame Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafFrameGlobal.MorphismIntrinsicComparison

noncomputable section

/-! Draft: specialize the coefficient category before choosing coefficient
complexes or comparison maps. The original frame and global-edge proofs are retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem homology_square {C : Type*} [Category C] [Abelian C]
    {K L M N : CochainComplex C ℕ}
    {a : K ⟶ L} {b : L ⟶ N} {c : K ⟶ M} {d : M ⟶ N}
    (h : a ≫ b = c ≫ d) (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫ HomologicalComplex.homologyMap b q =
      HomologicalComplex.homologyMap c q ≫ HomologicalComplex.homologyMap d q :=
  (HomologicalComplex.homologyMap_comp a b q).symm.trans
    ((congrArg (fun e => HomologicalComplex.homologyMap e q) h).trans
      (HomologicalComplex.homologyMap_comp c d q))

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
    (hi : HomologicalComplex.homologyMap a q ≫ i = j) :=
  RefinedInferred.Comparison.source
    (C := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (homology_square
      (C := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (MorphismPresheafNaturalityCoordinates.source.{1,2}
        p k n u (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) φ ψ hψ) q)
    (MorphismPresheafCoordinates.Comparison.source
      p k n u K M η a c ha hc q N i h j hh hi)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafFrameGlobal.MorphismIntrinsicComparison
