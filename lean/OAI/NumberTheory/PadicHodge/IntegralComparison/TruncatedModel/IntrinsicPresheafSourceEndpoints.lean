import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicPresheafSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite

/-! # Intrinsic Presheaf Source Endpoints -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafSourceEndpoints.MorphismIntrinsic

noncomputable section

/-! Transport the native source comparison to equal endpoints before
choosing the concrete coefficient complexes and resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem close {α : Sort*} {a b : α} (h : a = b)
    (l r : α) (hl : l = a) (hr : r = b) : l = r :=
  hl.trans (h.trans hr.symm)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  fun (m : K₀ ⟶ K₁) hm =>
    close (show @Eq
      (@Quiver.Hom
        (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
        (@ModuleCat.moduleCategory
          (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring).toQuiver
        _ N)
      (Witt.IntrinsicCechComposite.Intrinsic.composite p k
        (CechSliceResolution.opens p k n X₁) φ q
        (Witt.IntrinsicCechCoefficientComposite.Intrinsic.coefficientIso p k
          (CechSliceResolution.opens p k n X₁)
          (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) K₀ e₀ q).hom i)
      ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (HomologicalComplex.homologyMap (c := ComplexShape.up ℕ) m q) ≫
        Witt.IntrinsicCechCoefficientComposite.Intrinsic.composite p k
          (MorphismCover.pairs p k n u)
          (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) K₁ e₁ ψ q h)
    from MorphismIntrinsicPresheafSource.Intrinsic.source p k n u
      F K φ ψ hψ M η a c ha hc q N i h j hh hi K₀ K₁ e₀ e₁ m hm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafSourceEndpoints.MorphismIntrinsic
