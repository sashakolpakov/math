import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement

/-! # Morphism Presheaf Naturality Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates

noncomputable section

/-! Refinement naturality with an explicit coordinate map, before specializing
the coefficient complexes to the original crystalline comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe a b
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

variable (R : Type a) [CommRing R]

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

private theorem replace_right {C : Type*} [Category C] {X Y Z W : C}
    {a : X ⟶ Y} {b : Y ⟶ W} {c : X ⟶ Z} {d e : Z ⟶ W}
    (h : a ≫ b = c ≫ d) (h' : d = e) : a ≫ b = c ≫ e :=
  h.trans (congrArg (fun t => c ≫ t) h')

abbrev source
    {K L : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{max a b} R) ℕ}
    (η : K ⟶ L)
    (δ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj L))
    (h : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).map η) = δ) :=
  replace_right
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.refinement_naturality.{a, b} R
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) U
      (CechSliceResolution.opens p k n X₁)
      (MorphismRefinement.source p k n u) η)
    (congrArg (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{a, b} R E) h)

abbrev target
    {K L : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{max a b} R) ℕ}
    (η : K ⟶ L)
    (δ : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj L))
    (h : (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{a, b} R (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).map η) = δ) :=
  replace_right
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.refinement_naturality.{a, b} R
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) U
      (CechSliceResolution.opens p k n X₂)
      (MorphismRefinement.target p k n u) η)
    (congrArg (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{a, b} R E) h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates
