import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableProjectiveTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineTransportNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverHomInduction

/-! # Ambient Transport Over Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientTransportOverNaturality

noncomputable section

/-! The native ambient transports on a stable intersection are
natural for every morphism of affine tests over the coefficient base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {f : Spec (.of C) ⟶ Spec (.of R)}

theorem rawStableNativeAmbientTransport_natural
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
    (g : Spec (.of A) ⟶ Spec (.of R)) (b : Over.mk g ⟶ Over.mk f) :
    Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n g (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k (b ≫ x)) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b =
      HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b ≫
        Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k x) := by
  refine Affine.OverHomInduction.affineOverHom_ring_induction f (fun g b =>
    Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n g (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k (b ≫ x)) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b =
      HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b ≫
        Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k x)) ?_ g b
  intro φ
  exact Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport_natural n f φ _ _ (StableProjectiveTransport.rawStableIntersectionProjectiveIso_natural R i j k x φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientTransportOverNaturality
