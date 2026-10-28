import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality

/-! # Transport Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

noncomputable section

/-!
# Actual changes of bilinear line fibers compose and commute with geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

variable {X : Scheme.{u}} {M N P M' N' P' M'' N'' P'' : X.Modules}

/-- Identity fiber comparisons preserve the actual bilinear operation. -/
theorem transport_refl (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    Transport.transport β (Iso.refl M) (Iso.refl N) (Iso.refl P) = β := by
  ext U x y
  rfl

/-- Successive changes of actual fibers compose in the bilinear operation. -/
theorem transport_trans (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P')
    (a' : M' ≅ M'') (b' : N' ≅ N'') (c' : P' ≅ P'') :
    Transport.transport (Transport.transport β a b c) a' b' c' = Transport.transport β (a ≪≫ a') (b ≪≫ b') (c ≪≫ c') := by
  ext U x y
  rfl

/-- Geometric pullback of a changed bilinear operation is the change of its actual pulled-back operation. -/
theorem pullback_transport {Y : Scheme.{u}} (f : Y ⟶ X)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (hM' : Line.Bundles.IsLine M') (hN' : Line.Bundles.IsLine N')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (a : M ≅ M') (b : N ≅ N') (c : P ≅ P') :
    BilinearPullback.pullback f hM' hN' (Transport.transport β a b c) =
      Transport.transport (BilinearPullback.pullback f hM hN β)
        ((Scheme.Modules.pullback f).mapIso a) ((Scheme.Modules.pullback f).mapIso b)
        ((Scheme.Modules.pullback f).mapIso c) := by
  unfold Transport.transport
  rw [BilinearPullback.pullback_postcomp,
    PullbackNaturality.pullback_precomp f hM hN hM' hN' a.inv b.inv]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition
