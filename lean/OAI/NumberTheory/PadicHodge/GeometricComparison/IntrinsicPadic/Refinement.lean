import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalRefinementMaps
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneComponentHomology

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Refinement.IntrinsicPadicGeometricComparisonRefinement

noncomputable section

/-! Refining the original integral-to-injective Cech comparison
agrees on H-one with the actual paired comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

def sourceIntegralRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n))

def sourceIntegralHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n))

def sourceInjectiveHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X₁ Y₁ f₁ n).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex)

def sourceOriginalComparison := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R
  (IntegralComparison.NonemptyCechNerve.nerve (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁))
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)

def sourceOriginalHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)

omit [IsSeparated Y₂.hom] in
theorem source_coordinates : CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U
    (((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourcePullback p u).mapHomologicalComplex (.up ℕ)).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)) =
    CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology.homology.{1, 2, 0, 0} R U _ _
    (fun q _ V => IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.source_coordinates_component p u f₁ hp₁ n I₁ q V)

omit [IsSeparated Y₂.hom] in
theorem source : sourceOriginalHOne p f₁ hp₁ n I₁ ≫
    sourceInjectiveHOne p u f₁ n I₁ =
      sourceIntegralHOne p u n ≫ CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  (CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinement_homology.{1, 2, 0, 0, 0, 0} R (Affine.MapPairs.AffineMapPairs.source u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)).trans
      (congrArg (fun a => sourceIntegralHOne p u n ≫ a) (source_coordinates p u f₁ hp₁ n I₁))

def targetIntegralRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n))

def targetIntegralHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n))

def targetInjectiveHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X₂ Y₂ f₂ n).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex)

def targetOriginalComparison := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R
  (IntegralComparison.NonemptyCechNerve.nerve (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂))
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)

def targetOriginalHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)

omit [IsSeparated Y₁.hom] in
theorem target_coordinates : CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U
    (((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetPullback p u).mapHomologicalComplex (.up ℕ)).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)) =
    CechHomotopy.IntrinsicPadicGeometricCechHomotopy.targetComparisonHOne p u f₂ hp₂ n I₂ :=
  CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology.homology.{1, 2, 0, 0} R U _ _
    (fun q _ V => IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.target_coordinates_component p u f₂ hp₂ n I₂ q V)

omit [IsSeparated Y₁.hom] in
theorem target : targetOriginalHOne p f₂ hp₂ n I₂ ≫
    targetInjectiveHOne p u f₂ n I₂ =
      targetIntegralHOne p u n ≫ CechHomotopy.IntrinsicPadicGeometricCechHomotopy.targetComparisonHOne p u f₂ hp₂ n I₂ :=
  (CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinement_homology.{1, 2, 0, 0, 0, 0} R (Affine.MapPairs.AffineMapPairs.target u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)).trans
      (congrArg (fun a => targetIntegralHOne p u n ≫ a) (target_coordinates p u f₂ hp₂ n I₂))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Refinement.IntrinsicPadicGeometricComparisonRefinement
