import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationFrameCoefficients
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.ConcreteFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence

/-! # Frame Open Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransport.Construction

noncomputable section

/-! Original frame coefficients respect literal equalities of their
open domains. The transported translation-frame unit is the actual
transition unit on the native chart, with no compatibility premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence

theorem regularSectionTransport_trans {X : Scheme.{0}} {U V W : X.Opens}
    (h : U = V) (k : V = W) (s : Γ(X, U)) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport k (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport h s) = AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (h.trans k) s := by
  subst V
  subst W
  rfl

theorem nativeFrameOpenCoefficient_transport
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Modules}
    (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) {U V : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens}
    (h : U = V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain) (hs' : V ≤ s.domain) (ht' : V ≤ t.domain) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (congrArg (fun W => (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W) h)
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU (s.transition t U hs ht).val).snd =
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X V hV (s.transition t V hs' ht').val).snd := by
  subst V
  rfl

private theorem translatedFrameTransition_on_open
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle G.left)
    (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf) (v : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints G 1)
    (W : G.left.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain)
    (V : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens)
    (hV : (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ W = V)
    (hsV : V ≤ (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ s.domain)
    (htV : V ≤ (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ t.domain) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hV).toMonoidHom
      (TranslationFrameCoefficients.Construction.translatedFrameTransition G L s t v W hs ht) =
    (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
      (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L s).transition
    (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
      (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L t)
      V hsV htV :=
  FixedFiber.ConcreteFrames.Construction.localLineFrame_transition_transport _ _ hV
    ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono hs)
    ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono ht) hsV htV

theorem translatedFrameTransition_on_chart
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle G.left)
    (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf) (v : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints G 1)
    (B : CommAlgCat ℂ) (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (hs : i.left.opensRange ≤ s.domain) (ht : i.left.opensRange ≤ t.domain) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).symm).toMonoidHom
      (TranslationFrameCoefficients.Construction.translatedFrameTransition G L s t v i.left.opensRange hs ht) =
      (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L s).transition
      (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L t)
        (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
        ((AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).le.trans
          ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono hs))
        ((AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).le.trans
          ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono ht)) :=
  translatedFrameTransition_on_open G L s t v i.left.opensRange hs ht
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
    (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).symm
    ((AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).le.trans
      ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono hs))
    ((AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).le.trans
      ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono ht))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransport.Construction
