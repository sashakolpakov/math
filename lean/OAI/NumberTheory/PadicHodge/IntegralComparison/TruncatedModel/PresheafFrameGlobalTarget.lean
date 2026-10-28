import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedInferred
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare

/-! # Presheaf Frame Global Target -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafFrameGlobalTarget.MorphismIntrinsic

noncomputable section

/-! Geometric frame homotopy, refinement, and global-edge cancellation
composed with abstract coefficient complexes. -/

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

abbrev target
    (F : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (φ : F ⟶ K)
    (ψ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj F) ⟶
      (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K))
    (hψ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).map φ) = ψ)
    (F' K' : CochainComplex ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (α : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj F) ⟶ F')
    (β : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1, 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K) ⟶ K')
    (ψ' : F' ⟶ K')
    (hψ' : Homotopy (ψ ≫ β) (α ≫ ψ'))
    (M : CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M ⟶ K)
    (a : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₂) K).total (.up ℕ))
    (c : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ))
    (ha : a = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map
      (CechSliceResolution.opens p k n X₂) K M η)
    (hc : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K)
      M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) K M η) = c)
    (q : ℕ) (G B₁ B₂ : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (a₀ : M.homology q ⟶ G)
    (p₁ : G ⟶ ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u) K').total (.up ℕ)).homology q)
    (h : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u) K').total (.up ℕ)).homology q ⟶ B₁) (g : B₂ ⟶ B₁)
    (i : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₂) K).total (.up ℕ)).homology q ⟶ B₂)
    (j₁ : G ⟶ B₁) (j₂ : M.homology q ⟶ B₂)
    [Epi (HomologicalComplex.homologyMap a q)]
    (hb : HomologicalComplex.homologyMap c q ≫
      HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u)) β) q = a₀ ≫ p₁)
    (hh : p₁ ≫ h = j₁) (ha₀ : a₀ ≫ j₁ = j₂ ≫ g)
    (hi : HomologicalComplex.homologyMap a q ≫ i = j₂) :=
  RefinedInferred.Comparison.target
    (C := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (homology_square
      (C := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (MorphismPresheafNaturalityCoordinates.target.{1,2}
        p k n u (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) φ ψ hψ) q)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare.CechTotalHomotopySquare.homology.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
      ψ β α ψ' hψ' q)
    (MorphismPresheafCoordinates.Comparison.target
      p k n u K M η a c ha hc q G _ B₁ B₂ a₀ p₁
      (HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u)) β) q)
      h g i j₁ j₂ hb hh ha₀ hi)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafFrameGlobalTarget.MorphismIntrinsic
