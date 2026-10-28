import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts

/-! # Coefficient Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement

noncomputable section

/-! On the actual common integral cover, refinement and geometric
pullback commute with the original crystalline coefficient comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p
local notation "P₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X₁ n
local notation "P₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X₂ n
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))

def sourceIso := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (S ⋙ P₁)
def targetIso := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (T ⋙ P₂)

def sourceRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₁)
def targetRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₂)

def sourceBigRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n))
def targetBigRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n))

theorem source : ((G).mapHomologicalComplex (.up ℕ)).map (sourceRefinement p u n) ≫
    (sourceIso p u n).hom = (IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X₁ n).hom ≫
      sourceBigRefinement p u n :=
  CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total (Affine.MapPairs.AffineMapPairs.source u.left) G U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u) P₁

theorem target : ((G).mapHomologicalComplex (.up ℕ)).map (targetRefinement p u n) ≫
    (targetIso p u n).hom = (IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X₂ n).hom ≫
      targetBigRefinement p u n :=
  CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total (Affine.MapPairs.AffineMapPairs.target u.left) G U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u) P₂

def geometricMap := (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n)
def geometricBigMap := (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (IntegralSource.IntrinsicPadicGeometricIntegralSource.transformation p u n)

theorem naturality : ((G).mapHomologicalComplex (.up ℕ)).map (geometricMap p u n) ≫
    (sourceIso p u n).hom = (targetIso p u n).hom ≫ geometricBigMap p u n :=
  CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
    (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement
