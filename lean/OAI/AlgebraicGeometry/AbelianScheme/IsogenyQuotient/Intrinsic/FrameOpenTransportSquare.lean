import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransport

/-! # Frame Open Transport Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransportSquare.Construction

noncomputable section

/-! Transport native frame coefficients through a commuting square of open equalities. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem nativeFrameOpenCoefficient_transport_square
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Modules}
    (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) {U V : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens}
    (h : U = V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain)
    (hs' : V ≤ s.domain) (ht' : V ≤ t.domain)
    {Z W : X.left.Opens}
    (hUZ : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U = Z)
    (hZW : Z = W)
    (hVW : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V = W) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hVW
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X V hV (s.transition t V hs' ht').val).snd =
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hZW
      (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hUZ
        (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU (s.transition t U hs ht).val).snd) := by
  have hc := FrameOpenTransport.Construction.nativeFrameOpenCoefficient_transport X s t h hU hV hs ht hs' ht'
  refine (congrArg (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hVW) hc.symm).trans ?_
  exact (FrameOpenTransport.Construction.regularSectionTransport_trans
    (congrArg (fun O => (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ O) h)
    hVW _).trans (FrameOpenTransport.Construction.regularSectionTransport_trans hUZ hZW _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransportSquare.Construction
