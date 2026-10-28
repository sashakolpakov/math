import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechPullback

/-! # Quotient Open Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates

noncomputable section

/-! The original native p-adic quotient coordinates give the
actual source refinement and geometric pullback on open Cech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens ℤ_[p] u
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left
local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "V₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁
local notation "V₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂

local instance source_preserves (q : ℕ) (t : Fin (q + 1) → Cover.IntrinsicPadicGeometricCover.Index p u) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens ℤ_[p] u) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens ℤ_[p] u) (fun _ _ => rfl) (U ∘ t)
local instance source_composite_preserves (q : ℕ) (t : Fin (q + 1) → Cover.IntrinsicPadicGeometricCover.Index p u) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (Affine.MapPairs.AffineMapPairs.source u.left ⋙ Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (Affine.MapPairs.AffineMapPairs.source u.left ⋙ Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left) (fun _ _ => rfl) (U ∘ t)

def sourceIso := IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.totalIso ℤ_[p] X₁ S U I

def sourceRefinement := CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map ((G).obj ∘ V₁) ((S).obj ∘ U)
  (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G ((Affine.MapPairs.AffineMapPairs.source u.left).obj ∘ U) V₁
    (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex ℤ_[p] X₁ I)

def targetPullback := Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal.directMap ℤ_[p] u I U V₂
  (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)

theorem source_component (q : ℕ) : (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n).f q ≫
    (sourceIso p u n).hom.f q = (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₁ n).hom.f q ≫
      (sourceRefinement p u n).f q :=
  congrArg (fun a => a.f q) (IndexedOrdinaryComplexHom.IndexedOrdinaryQuotientReindex.total ℤ_[p] X₁
    (Affine.MapPairs.AffineMapPairs.source u.left) G U V₁ I (Cover.IntrinsicPadicGeometricCoverRefinements.source p u))

theorem target_component (q : ℕ) : (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n).f q ≫
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n).f q ≫ (sourceIso p u n).hom.f q =
      (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X₂ n).hom.f q ≫ (targetPullback p u n).f q :=
  (congrArg (fun a => a ≫ (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n).f q ≫
    (sourceIso p u n).hom.f q)
      (Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal.refinement_component ℤ_[p] u I U V₂
        (Cover.IntrinsicPadicGeometricCoverRefinements.target p u) q)).trans
    ((congrArg (fun a => (Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal.refinement ℤ_[p] u I U V₂
      (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)).f q ≫ a ≫ (sourceIso p u n).hom.f q)
        (Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal.geometric_component ℤ_[p] u I U q)).trans
      (congrArg (fun a => a.f q) (Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal.total ℤ_[p] u I U V₂
        (Cover.IntrinsicPadicGeometricCoverRefinements.target p u))))

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_pullback_coordinates : targetPullback p u n =
    Integral.QuotientCechPullback.IntegralQuotientCechPullback.fullMap ℤ_[p] u I
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂)
      (fun i => (Cover.IntrinsicPadicGeometricCover.opens p u i).val)
      (Cover.IntrinsicPadicGeometricCover.targetIndex p u) (Cover.IntrinsicPadicGeometricCover.le_preimage p u) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientOpenCoordinates.IntrinsicPadicGeometricQuotientOpenCoordinates
