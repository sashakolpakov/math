import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafEdgeHomologyCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobal

/-! # Morphism Presheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates.Comparison

noncomputable section

/-! Cancel the original global edges before specializing the coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]

private theorem cancel_source {C : Type*} [Category C]
    {G K P N : C} {e : G ⟶ K} [Epi e]
    {r : K ⟶ P} {p : G ⟶ P} {i : K ⟶ N} {h : P ⟶ N} {j : G ⟶ N}
    (hr : e ≫ r = p) (hh : p ≫ h = j) (hi : e ≫ i = j) : r ≫ h = i :=
  GeometricComparison.RefinedGlobal.RefinedGlobalConeNaturality.source e r p i h j hr hh hi

private theorem cancel_target {C : Type*} [Category C]
    {G₁ G₂ K₂ P₁ P₂ B₁ B₂ : C} {e : G₂ ⟶ K₂} [Epi e]
    {r : K₂ ⟶ P₂} {p₁ : G₁ ⟶ P₁} {p₂ : G₂ ⟶ P₂}
    {a : G₂ ⟶ G₁} {b : P₂ ⟶ P₁} {g : B₂ ⟶ B₁}
    {i : K₂ ⟶ B₂} {h : P₁ ⟶ B₁} {j₁ : G₁ ⟶ B₁} {j₂ : G₂ ⟶ B₂}
    (hr : e ≫ r = p₂) (hb : p₂ ≫ b = a ≫ p₁) (hh : p₁ ≫ h = j₁)
    (ha : a ≫ j₁ = j₂ ≫ g) (hi : e ≫ i = j₂) : r ≫ b ≫ h = i ≫ g :=
  GeometricComparison.RefinedGlobal.RefinedGlobalConeNaturality.target e r p₁ p₂ a b g i h j₁ j₂ hr hb hh ha hi

abbrev source
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
    (q : ℕ) (N : A)
    (i : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₁) K).total (.up ℕ)).homology q ⟶ N)
    (h : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ)).homology q ⟶ N)
    (j : M.homology q ⟶ N)
    [Epi (HomologicalComplex.homologyMap a q)]
    (hh : HomologicalComplex.homologyMap c q ≫ h = j)
    (hi : HomologicalComplex.homologyMap a q ≫ i = j) :=
  cancel_source (e := HomologicalComplex.homologyMap a q)
    (PresheafEdgeHomologyCoordinates.Morphism.source
      p k n u K M η a c ha hc q) hh hi

abbrev target
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
    (q : ℕ) (G P B₁ B₂ : A)
    (a₀ : M.homology q ⟶ G) (p₁ : G ⟶ P)
    (b₀ : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ)).homology q ⟶ P)
    (h : P ⟶ B₁) (g : B₂ ⟶ B₁)
    (i : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex
      (CechSliceResolution.opens p k n X₂) K).total (.up ℕ)).homology q ⟶ B₂)
    (j₁ : G ⟶ B₁) (j₂ : M.homology q ⟶ B₂)
    [Epi (HomologicalComplex.homologyMap a q)]
    (hb : HomologicalComplex.homologyMap c q ≫ b₀ = a₀ ≫ p₁)
    (hh : p₁ ≫ h = j₁) (ha₀ : a₀ ≫ j₁ = j₂ ≫ g)
    (hi : HomologicalComplex.homologyMap a q ≫ i = j₂) :=
  cancel_target (e := HomologicalComplex.homologyMap a q)
    (PresheafEdgeHomologyCoordinates.Morphism.target
      p k n u K M η a c ha hc q) hb hh ha₀ hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates.Comparison
