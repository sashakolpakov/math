import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafEdgeCoordinates

/-! # Presheaf Edge Homology Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafEdgeHomologyCoordinates.Morphism

noncomputable section

/-! Take homology of the original edge-coordinate identity before specializing
the coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]

private theorem homology_of_edge {C : Type*} [Category C] [Abelian C]
    {K L M : CochainComplex C ℕ} {a : K ⟶ L} {b : L ⟶ M} {c : K ⟶ M}
    (h : a ≫ b = c) (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫ HomologicalComplex.homologyMap b q =
      HomologicalComplex.homologyMap c q :=
  (HomologicalComplex.homologyMap_comp a b q).symm.trans
    (congrArg (fun e => HomologicalComplex.homologyMap e q) h)

omit [Fintype k] [CharP k p] in
theorem source
    (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K)
    (a : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₁) K).total (.up ℕ))
    (c : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ))
    (ha : a = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map
      (CechSliceResolution.opens p k n X₁) K M η)
    (hc : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)
      M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) K M η) = c)
    (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫
      HomologicalComplex.homologyMap (MorphismPresheafRefinement.sourceMap p k n u K) q =
    HomologicalComplex.homologyMap c q :=
  homology_of_edge (MorphismPresheafEdgeCoordinates.source
    p k n u K M η a c ha hc) q

omit [Fintype k] [CharP k p] in
theorem target
    (K : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ A) ℕ)
    (M : CochainComplex A ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M ⟶ K)
    (a : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₂) K).total (.up ℕ))
    (c : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ))
    (ha : a = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map
      (CechSliceResolution.opens p k n X₂) K M η)
    (hc : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K)
      M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) K M η) = c)
    (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫
      HomologicalComplex.homologyMap (MorphismPresheafRefinement.targetMap p k n u K) q =
    HomologicalComplex.homologyMap c q :=
  homology_of_edge (MorphismPresheafEdgeCoordinates.target
    p k n u K M η a c ha hc) q

universe uR vM

omit [Fintype k] [CharP k p] in
theorem source_module {R : Type uR} [CommRing R]
    (K : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ (ModuleCat.{vM} R)) ℕ)
    (M : CochainComplex (ModuleCat.{vM} R) ℕ)
    (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M ⟶ K)
    (a : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₁) K).total (.up ℕ))
    (c : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := (ModuleCat.{vM} R)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ))
    (ha : a = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map
      (CechSliceResolution.opens p k n X₁) K M η)
    (hc : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := (ModuleCat.{vM} R)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)
      M (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) K M η) = c)
    (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫
      HomologicalComplex.homologyMap (MorphismPresheafRefinement.sourceMap p k n u K) q =
    HomologicalComplex.homologyMap c q :=
  source p k n u K M η a c ha hc q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafEdgeHomologyCoordinates.Morphism
