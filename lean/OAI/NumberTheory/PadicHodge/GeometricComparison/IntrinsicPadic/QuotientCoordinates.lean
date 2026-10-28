import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.IsoSquare

/-! # Quotient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates

noncomputable section

/-! Original Witt-to-p-adic quotient coordinates commute with the
actual common-cover refinements and with geometric section pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "P₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X₁ n
local notation "P₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X₂ n

def sourceCoefficientIso := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (S ⋙ P₁)
def targetCoefficientIso := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (T ⋙ P₂)
def sourceWittIso := CechAssembly.Iso.CechAssemblyIso.totalIso E
  (Functor.isoWhiskerLeft S (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₁ n))
def targetWittIso := CechAssembly.Iso.CechAssemblyIso.totalIso E
  (Functor.isoWhiskerLeft T (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₂ n))
def sourceIso := sourceWittIso p u n ≪≫ (sourceCoefficientIso p u n).symm
def targetIso := targetWittIso p u n ≪≫ (targetCoefficientIso p u n).symm

def sourceRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₁)
def targetRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₂)

def sourceRestrictedRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P₁ ⋙ (G).mapHomologicalComplex (.up ℕ)))
def targetRestrictedRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P₂ ⋙ (G).mapHomologicalComplex (.up ℕ)))

theorem source : CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceRefinement p u n ≫
    (sourceIso p u n).hom = (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₁ n).hom ≫
      ((G).mapHomologicalComplex (.up ℕ)).map (sourceRefinement p u n) := by
  let old := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G
    (IntegralComparison.NonemptyCechNerve.nerve (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁))
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)) P₁
  have h₁ := (CechAssembly.RefinedIso.CechAssemblyRefinedIso.naturality (Affine.MapPairs.AffineMapPairs.source u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
    (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₁ n)).symm
  have h₂ := IntegralComparison.InverseCoordinateHomology.inverse old (sourceCoefficientIso p u n)
    (((G).mapHomologicalComplex (.up ℕ)).map (sourceRefinement p u n))
    (sourceRestrictedRefinement p u n)
    (CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total (Affine.MapPairs.AffineMapPairs.source u.left) G U
      (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u) P₁)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

theorem target : CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetRefinement p u n ≫
    (targetIso p u n).hom = (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₂ n).hom ≫
      ((G).mapHomologicalComplex (.up ℕ)).map (targetRefinement p u n) := by
  let old := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G
    (IntegralComparison.NonemptyCechNerve.nerve (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂))
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)) P₂
  have h₁ := (CechAssembly.RefinedIso.CechAssemblyRefinedIso.naturality (Affine.MapPairs.AffineMapPairs.target u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
    (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₂ n)).symm
  have h₂ := IntegralComparison.InverseCoordinateHomology.inverse old (targetCoefficientIso p u n)
    (((G).mapHomologicalComplex (.up ℕ)).map (targetRefinement p u n))
    (targetRestrictedRefinement p u n)
    (CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total (Affine.MapPairs.AffineMapPairs.target u.left) G U
      (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u) P₂)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

def transformation : T ⋙ P₂ ⟶ S ⋙ P₁ :=
  Functor.whiskerRight (Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation ℤ_[p] u)
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p] ⋙
      (IntegralComparison.Module.IdealQuotient.functor ℤ_[p] ((Ideal.span {(p : ℤ_[p])}) ^ (n + 1))).mapHomologicalComplex (.up ℕ))

def geometricMap := (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (transformation p u n)
def restrictedMap := (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (ReducedBaseIso.IntrinsicPadicGeometricReducedBaseIso.targetMap p u n)

theorem naturality : CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.geometricMap p u n ≫
    (sourceIso p u n).hom = (targetIso p u n).hom ≫
      ((G).mapHomologicalComplex (.up ℕ)).map (geometricMap p u n) := by
  have h₁ := CechAssembly.IsoSquare.CechAssemblyIsoSquare.naturality E
    (Functor.isoWhiskerLeft S (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₁ n))
    (Functor.isoWhiskerLeft T (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X₂ n))
    (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n)
    (ReducedBaseIso.IntrinsicPadicGeometricReducedBaseIso.targetMap p u n)
    (ReducedBaseIso.IntrinsicPadicGeometricReducedBaseIso.naturality p u n)
  have h₂ := IntegralComparison.InverseCoordinateHomology.inverse (targetCoefficientIso p u n) (sourceCoefficientIso p u n)
    (((G).mapHomologicalComplex (.up ℕ)).map (geometricMap p u n)) (restrictedMap p u n)
    (CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (transformation p u n))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates
