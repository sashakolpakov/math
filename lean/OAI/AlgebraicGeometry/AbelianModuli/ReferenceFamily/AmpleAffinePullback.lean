import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonvanishingPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Ample Affine Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleAffinePullback

noncomputable section

/-! The actual ample-section definition is preserved by affine pullback
when the source is quasi-compact. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}}

theorem ample_pullback_affine (f : X ⟶ Y) [IsAffineHom f] [CompactSpace X]
    (L : HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) : (L.pullback f).IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨n, hn, P, hP, s, hx, ha⟩ := hL.2 (f x)
  refine ⟨n, hn, P.pullback f, Tensor.PowerPullback.isTensorPower_pullback_positive f hn hP,
    HilbertConstruction.Ample.LineBundles.pullbackSection f s, ?_, ?_⟩
  · exact (congrArg (fun U : X.Opens => x ∈ U)
      (NonvanishingPullback.lineBundle_sectionNonvanishing_pullback f P s)).mpr hx
  · exact (congrArg IsAffineOpen
      (NonvanishingPullback.lineBundle_sectionNonvanishing_pullback f P s)).mpr (ha.preimage f)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleAffinePullback
