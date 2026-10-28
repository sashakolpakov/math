import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ReducedDeRhamNaturality

/-! # De Rham Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction

noncomputable section

/-! The original native integral de Rham reduction agrees with
both the geometric and source-refinement maps on the common cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.opens p u
local notation "U₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₁
local notation "U₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂

def commonReduction := IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality.reduction ℤ_[p] I X₁ V
  (fun i => (Cover.IntrinsicPadicGeometricCover.opens p u i).property) (Cover.IntrinsicPadicGeometricCover.cover p u)

theorem old_coordinates (Z : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper Z.hom] [Smooth Z.hom]
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] Z 1) :
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] Z (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] Z) I 1).hom
      (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p Z (n + 1) x) =
    IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality.reduction ℤ_[p] I Z (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] Z)
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] Z) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] Z) x :=
  IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality.coordinates ℤ_[p] I Z (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] Z)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] Z) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] Z) x

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₁ 1) :
    QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.sourceMap p u n
      ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X₁ U₁ I 1).hom
        (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X₁ (n + 1) x)) = commonReduction p u n x :=
  (congrArg (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.sourceMap p u n) (old_coordinates p n X₁ x)).trans
    (IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality.refinement ℤ_[p] I U₁ V
      (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.coverRefinement p u)
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X₁) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₁)
      (fun i => (Cover.IntrinsicPadicGeometricCover.opens p u i).property) (Cover.IntrinsicPadicGeometricCover.cover p u) x)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₂ 1) :
    QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.targetMap p u n
      ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X₂ U₂ I 1).hom
        (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X₂ (n + 1) x)) =
          commonReduction p u n (DeRham.Int.pullback u 1 x) :=
  (congrArg (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.targetMap p u n) (old_coordinates p n X₂ x)).trans
    (IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality.naturality ℤ_[p] I u U₂ V
      (Cover.IntrinsicPadicGeometricCover.targetIndex p u) (Cover.IntrinsicPadicGeometricCover.le_preimage p u)
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X₂) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₂)
      (fun i => (Cover.IntrinsicPadicGeometricCover.opens p u i).property) (Cover.IntrinsicPadicGeometricCover.cover p u) x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction
