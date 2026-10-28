import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOpenCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainComponent
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechRefinement

/-! # Quotient One Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates

/-! Native small quotient H-one coordinates preserve the actual
common source refinement and geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

def sourceMap := HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) 1
def targetMap := HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) 1
def geometricMap := HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) 1
def openIso := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ_[p]) (.up ℕ) 1).mapIso
  (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.sourceIso p u n)
def sourceOpenMap := HomologicalComplex.homologyMap
  (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.sourceRefinement p u n) 1
def targetOpenMap := HomologicalComplex.homologyMap
  (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.targetPullback p u n) 1

theorem source : sourceMap p u n ≫ (openIso p u n).hom =
    HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₁ n).hom 1 ≫ sourceOpenMap p u n :=
  CochainComponent.CochainComponentHomologySquare.pair
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n)
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.sourceIso p u n).hom
    (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₁ n).hom
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.sourceRefinement p u n) 1
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.source_component p u n 1)

theorem target : targetMap p u n ≫ geometricMap p u n ≫ (openIso p u n).hom =
    HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₂ n).hom 1 ≫ targetOpenMap p u n :=
  CochainComponent.CochainComponentHomologySquare.triple
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n)
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.sourceIso p u n).hom
    (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₂ n).hom
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.targetPullback p u n) 1
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.target_component p u n 1)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates

/-! Original native small quotient comparisons preserve the
three-term quotient H-one coordinates on the actual common cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens ℤ_[p] u
local notation "V₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁

def opens := (S).obj ∘ U
def coverRefinement := NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G
  ((Affine.MapPairs.AffineMapPairs.source u.left).obj ∘ U) V₁ (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)

def sourceMap := HomologicalComplex.homologyMap (Integral.QuotientCechRefinement.IntegralQuotientCechRefinement.map ℤ_[p] X₁ I
  ((G).obj ∘ V₁) (opens p u) (coverRefinement p u)) 1
def targetMap := HomologicalComplex.homologyMap (Integral.QuotientCechPullback.IntegralQuotientCechPullback.map ℤ_[p] u I
  (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂) (opens p u)
  (Cover.IntrinsicPadicGeometricCover.targetIndex p u) (Cover.IntrinsicPadicGeometricCover.le_preimage p u)) 1

def projectionIso := IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X₁ (opens p u) I
def iso := IntrinsicPadicGeometricQuotientHOneCoordinates.openIso p u n ≪≫ projectionIso p u n

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source_projection : IntrinsicPadicGeometricQuotientHOneCoordinates.sourceOpenMap p u n ≫
    (projectionIso p u n).hom =
      (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X₁ ((G).obj ∘ V₁) I).hom ≫ sourceMap p u n :=
  Integral.QuotientCechRefinement.IntegralQuotientCechRefinement.homology ℤ_[p] X₁ I ((G).obj ∘ V₁) (opens p u) (coverRefinement p u)

theorem source : IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n ≫ (iso p u n).hom =
    (Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X₁ n).hom ≫ sourceMap p u n :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (IntrinsicPadicGeometricQuotientHOneCoordinates.source p u n) (source_projection p u n)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_projection : IntrinsicPadicGeometricQuotientHOneCoordinates.targetOpenMap p u n ≫
    (projectionIso p u n).hom =
      (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X₂
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂) I).hom ≫ targetMap p u n :=
  (congrArg (fun a => HomologicalComplex.homologyMap a 1 ≫ (projectionIso p u n).hom)
    (QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates.target_pullback_coordinates p u n)).trans
      (Integral.QuotientCechPullback.IntegralQuotientCechPullback.homology ℤ_[p] u I
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂) (opens p u)
        (Cover.IntrinsicPadicGeometricCover.targetIndex p u) (Cover.IntrinsicPadicGeometricCover.le_preimage p u))

theorem target : (IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n ≫
    IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n) ≫ (iso p u n).hom =
      (Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X₂ n).hom ≫ targetMap p u n :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    ((Category.assoc _ _ _).trans (IntrinsicPadicGeometricQuotientHOneCoordinates.target p u n))
    (target_projection p u n)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates

end

end OAI
