import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafFrameGlobalTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobalTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

/-! # Morphism Intrinsic Presheaf Target -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicPresheafTarget.Intrinsic

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

local instance directCoefficientRing :
    Ring (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ULift.ring

local instance directCoefficientCategory :
    Category (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  @ModuleCat.moduleCategory _ (ULift.ring)

local instance directCoefficientAbelian :
    Abelian (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  @ModuleCat.abelian _ (ULift.ring)

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
    (hi : HomologicalComplex.homologyMap a q ≫ i = j₂)
    (K₀ K₁ K₂ : CochainComplex (ModuleCat.{0} (WittVector p k)) ℕ)
    (e₀ : ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj K₀ ≅
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (CechSliceResolution.opens p k n X₂) F).total (.up ℕ))
    (e₁ : ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj K₁ ≅
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u)
        (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
          (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj F)).total (.up ℕ))
    (e₂ : ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj K₂ ≅
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u) F').total (.up ℕ)) :=
  @ExactRefinedGlobalTarget.Comparison.target
    (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (ULift.ring))
    (@ModuleCat.moduleCategory _ (ULift.ring))
    (@ModuleCat.abelian _ (ULift.ring))
    _ _ _ _ _ q _ _ _ _ _
    (PresheafFrameGlobalTarget.MorphismIntrinsic.target p k n u
      F K φ ψ hψ F' K' α β ψ' hψ' M η a c ha hc q G B₁ B₂ a₀ p₁ h g i j₁ j₂ hb hh ha₀ hi).symm
    (ModuleCat.{0} (WittVector p k))
    (@ModuleCat.moduleCategory _ (inferInstance : Ring (WittVector p k)))
    (@ModuleCat.abelian _ (inferInstance : Ring (WittVector p k)))
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) _ _ _ _ _ e₀ e₁ e₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicPresheafTarget.Intrinsic
