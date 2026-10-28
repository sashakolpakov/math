import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoOpenChow

/-! # Chow Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: rational-section Chow classes under actual isomorphisms of the underlying schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionChowClass_transport (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (h : f = g) (d : ℕ) :
    DimensionChow.BundleCycles.dimensionChowTransport h d (L.rationalSectionChowClass f d) = L.rationalSectionChowClass g d := by
  subst g
  rfl

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.iso_pushforward_chowClass (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (e : X ≅ Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    Closed.ChowPushforward.BundleCycles.closedChowPushforward e.hom f d ((L.pullback e.hom).rationalSectionChowClass (e.hom ≫ f) d) =
      L.rationalSectionChowClass f d := by
  rw [L.pullback_open_chowClass e.hom f d hd, LineBundles.Scheme.IsoOpenChow.BundleCycles.schemeIso_closed_open_chow]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.iso_pushforwardOver_chowClass (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (e : X ≅ Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (h : e.hom ≫ f = g) (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    Closed.ChowOver.BundleCycles.closedChowPushforwardOver e.hom g f h d ((L.pullback e.hom).rationalSectionChowClass g d) =
      L.rationalSectionChowClass f d := by
  change Closed.ChowPushforward.BundleCycles.closedChowPushforward e.hom f d
    (DimensionChow.BundleCycles.dimensionChowTransport h.symm d ((L.pullback e.hom).rationalSectionChowClass g d)) = _
  rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionChowClass_transport, L.iso_pushforward_chowClass e f d hd]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
