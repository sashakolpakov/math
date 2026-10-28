import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementConeCoordinates

/-! # Section Refinement Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRefinementData.IntrinsicPadicGeometricSectionRefinementData

noncomputable section

/-! The original comparison and cone refinements in the actual
composed native section-functor H-one coordinates. -/

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

def sourceIntegralMap := CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne.mapHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n)

def targetIntegralMap := CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne.mapHOne.{1, 2} R (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n)

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor
  (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₁ n

def sourceMap := Section.FunctorRefinementOne.SectionFunctorRefinementHOne.mapHOne.{1, 2} R S₁ I₁.cocomplex
  (Affine.MapPairs.AffineMapPairs.source u.left) (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)

def sourcePulledHOne := Section.FunctorRefinementOne.SectionFunctorRefinementHOne.pulledHOne.{1, 2} R S₁ I₁.cocomplex (Affine.MapPairs.AffineMapPairs.source u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁) U
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)

omit [IsSeparated Y₂.hom] in
theorem source_coordinates : sourcePulledHOne p u f₁ hp₁ n I₁ =
    CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology.homology.{1, 2, 0, 0} R U _ _
    (fun q _ W => IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.source_coordinates_component p u f₁ hp₁ n I₁ q W)

omit [IsSeparated Y₂.hom] in
theorem source_naturality : Refinement.IntrinsicPadicGeometricComparisonRefinement.sourceOriginalHOne p f₁ hp₁ n I₁ ≫
    sourceMap p u f₁ n I₁ = sourceIntegralMap p u n ≫
      sourcePulledHOne p u f₁ hp₁ n I₁ :=
  Section.FunctorRefinementOne.SectionFunctorRefinementHOne.naturality.{1, 2} R S₁ I₁.cocomplex (Affine.MapPairs.AffineMapPairs.source u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)

local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "S₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor
  (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₂ n

def targetMap := Section.FunctorRefinementOne.SectionFunctorRefinementHOne.mapHOne.{1, 2} R S₂ I₂.cocomplex
  (Affine.MapPairs.AffineMapPairs.target u.left) (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)

def targetPulledHOne := Section.FunctorRefinementOne.SectionFunctorRefinementHOne.pulledHOne.{1, 2} R S₂ I₂.cocomplex (Affine.MapPairs.AffineMapPairs.target u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂) U
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)

omit [IsSeparated Y₁.hom] in
theorem target_coordinates : targetPulledHOne p u f₂ hp₂ n I₂ =
    CechHomotopy.IntrinsicPadicGeometricCechHomotopy.targetComparisonHOne p u f₂ hp₂ n I₂ :=
  CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology.homology.{1, 2, 0, 0} R U _ _
    (fun q _ W => IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.target_coordinates_component p u f₂ hp₂ n I₂ q W)

omit [IsSeparated Y₁.hom] in
theorem target_naturality : Refinement.IntrinsicPadicGeometricComparisonRefinement.targetOriginalHOne p f₂ hp₂ n I₂ ≫
    targetMap p u f₂ n I₂ = targetIntegralMap p u n ≫
      targetPulledHOne p u f₂ hp₂ n I₂ :=
  Section.FunctorRefinementOne.SectionFunctorRefinementHOne.naturality.{1, 2} R S₂ I₂.cocomplex (Affine.MapPairs.AffineMapPairs.target u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRefinementData.IntrinsicPadicGeometricSectionRefinementData
