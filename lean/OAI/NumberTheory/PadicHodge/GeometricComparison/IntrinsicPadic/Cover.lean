import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineMapRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution

/-! # Cover -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover

/-! An actual finite cover by compatible affine pairs simultaneously
refines the source coordinate cover and inverse images of the target cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  (u : X₁ ⟶ X₂)

local instance sourceCompact : CompactSpace X₁.left :=
  QuasiCompact.compactSpace_of_compactSpace X₁.hom

def refinement := Finite.AffineMapRefinement.FiniteAffineMapRefinement.ofCompact u.left
  (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂)
  (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₁)
  (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₂)
  (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₁)

abbrev Index := (refinement p u).Index

def sourceIndex (i : IntrinsicPadicGeometricCover.Index p u) : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₁ :=
  ((refinement p u).index i).2

def targetIndex (i : IntrinsicPadicGeometricCover.Index p u) : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₂ :=
  ((refinement p u).index i).1

def opens (i : IntrinsicPadicGeometricCover.Index p u) : X₁.left.affineOpens :=
  ⟨(refinement p u).opens i, (refinement p u).affine i⟩

theorem le_source (i : IntrinsicPadicGeometricCover.Index p u) : (IntrinsicPadicGeometricCover.opens p u i).val ≤
    Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₁ (sourceIndex p u i) :=
  Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_target u.left _ _
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₂)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₁) i

theorem le_preimage (i : IntrinsicPadicGeometricCover.Index p u) : (IntrinsicPadicGeometricCover.opens p u i).val ≤
    u.left ⁻¹ᵁ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X₂ (targetIndex p u i) :=
  Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_source u.left _ _
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₂)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X₁) i

def pairs (i : IntrinsicPadicGeometricCover.Index p u) : Affine.MapPairs.AffineMapPairs.Charts u.left :=
  ⟨(IntrinsicPadicGeometricCover.opens p u i, CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂ (targetIndex p u i)), le_preimage p u i⟩

theorem cover : (⨆ i, (IntrinsicPadicGeometricCover.opens p u i).val) = ⊤ := (refinement p u).cover

theorem pairs_source (i : IntrinsicPadicGeometricCover.Index p u) : (Affine.MapPairs.AffineMapPairs.source u.left).obj (pairs p u i) = IntrinsicPadicGeometricCover.opens p u i := rfl
theorem pairs_target (i : IntrinsicPadicGeometricCover.Index p u) : (Affine.MapPairs.AffineMapPairs.target u.left).obj (pairs p u i) =
    CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂ (targetIndex p u i) := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCoverRefinements

/-! Both projections of the common affine-pair cover give actual
refinement morphisms into the original chosen coordinate covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  (u : X₁ ⟶ X₂)

def source : FormalCoproduct.mk (IntrinsicPadicGeometricCover.Index p u)
    ((Affine.MapPairs.AffineMapPairs.source u.left).obj ∘ IntrinsicPadicGeometricCover.pairs p u) ⟶
      FormalCoproduct.mk (Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₁) (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) where
  f := IntrinsicPadicGeometricCover.sourceIndex p u
  φ i := homOfLE (IntrinsicPadicGeometricCover.le_source p u i)

def target : FormalCoproduct.mk (IntrinsicPadicGeometricCover.Index p u)
    ((Affine.MapPairs.AffineMapPairs.target u.left).obj ∘ IntrinsicPadicGeometricCover.pairs p u) ⟶
      FormalCoproduct.mk (Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₂) (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) where
  f := IntrinsicPadicGeometricCover.targetIndex p u
  φ _ := 𝟙 _

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCoverRefinements

end

end OAI
