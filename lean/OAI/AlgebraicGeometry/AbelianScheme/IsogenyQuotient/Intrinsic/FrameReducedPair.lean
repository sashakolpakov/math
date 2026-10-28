import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCechClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed

/-! # Frame Reduced Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameReducedPair.Construction

noncomputable section

/-! The intrinsic reduced pair coefficients of actual frames compute
their original native Cech cochain and infinitesimal Picard class.
The finite-intersection comparison follows from original restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffineHom (pullback.diagonal (terminal.from (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {M : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Modules} {I : Type}
    (s : I → AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (hs : ∀ i, IsAffineOpen (s i).domain)

def nativeReducedFramePair (i j : I) :
    Γ(X.left, AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun a => (s a).domain) i ⊓
      AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun a => (s a).domain) j) :=
  (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X ((s i).domain ⊓ (s j).domain) ((hs i).inf (hs j))
    ((s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right).val).snd

variable [LocallyOfFiniteType X.hom] [IsReduced X.left]

theorem nativeReducedFramePair_cochain :
    AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X.left (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun a => (s a).domain))
      (nativeReducedFramePair X s hs) = FrameCechClass.Construction.nativeFrameCechCochain X s hs := by
  rw [FrameCechClass.Construction.nativeFrameCechCochain_eq]
  funext a
  let U := fun i => (s i).domain
  let W := U (a 0) ⊓ U (a 1)
  let V := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a
  let h : V ≤ W := le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
  let q := (s (a 0)).transition (s (a 1)) W inf_le_left inf_le_right
  have hu := congrArg Units.val
    (AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame.transition_restrict (s (a 0)) (s (a 1)) h inf_le_left inf_le_right)
  have hc := AbelianModuli.ReferenceFamily.DualOpen.SectionRestriction.dualOpenSectionCoefficientEquiv_restrict X h ((hs (a 0)).inf (hs (a 1)))
    (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualCechIntersection_affine X U hs a) q.val
  have ht := AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport_restrict
    (rfl : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W =
      AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X U (a 0) ⊓ AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X U (a 1))
    (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechIntersection X U a) ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h)
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X U) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X U) a 1))
    (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X W ((hs (a 0)).inf (hs (a 1))) q.val).snd
  change X.left.presheaf.map _
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X W ((hs (a 0)).inf (hs (a 1))) q.val).snd =
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechIntersection X U a)
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X V (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualCechIntersection_affine X U hs a)
        ((s (a 0)).transition (s (a 1)) V
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).val).snd
  rw [← hu]
  simp only [Units.coe_map]
  erw [hc]
  exact ht.symm

theorem dualLinePullbackDifferenceClass_eq_reducedPair
    {Y : Scheme.{0}} (f g : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    [IsAffineHom g] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) {J : Type}
    (t : J → AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf) (ha : ∀ j, IsAffineOpen (t j).domain)
    (hc : iSup (fun j => (t j).domain) = ⊤) :
    ∃ (hcover : iSup (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain)) = ⊤)
      (hclosed : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf).obj
        (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain)) 1
        (AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X.left (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain))
          (nativeReducedFramePair X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
            (fun j => (ha j).preimage g))) = 0),
      AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceClass X f g h L =
        DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain))
          (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf) hcover 0
          (AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X.left (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain))
            (nativeReducedFramePair X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
              (fun j => (ha j).preimage g))) hclosed := by
  obtain ⟨hcover, hclosed, he⟩ := FrameCechClass.Construction.dualLinePullbackDifferenceClass_eq_nativeFrameCech X f g h L t ha hc
  have hpair : AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X.left
      (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain))
      (nativeReducedFramePair X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
        (fun j => (ha j).preimage g)) =
      FrameCechClass.Construction.nativeFrameCechCochain X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
        (fun j => (ha j).preimage g) :=
    nativeReducedFramePair_cochain X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
      (fun j => (ha j).preimage g)
  refine ⟨hcover, ?_, ?_⟩
  · exact (congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf).obj
      (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain)) 1) hpair).trans hclosed
  · simpa only [hpair] using he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameReducedPair.Construction
