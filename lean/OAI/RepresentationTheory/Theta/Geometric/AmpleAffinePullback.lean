import OAI.RepresentationTheory.Theta.Geometric.LinePowerPullback
import OAI.RepresentationTheory.Theta.Geometric.LineSectionNonvanishingPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Ample Affine Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.AmpleAffinePullback

noncomputable section

/-! Ampleness of actual line bundles is preserved by affine pullback from
a quasi-compact source, using native powers and nonvanishing loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ample_pullback_of_affine {X Y : Scheme} [CompactSpace X]
    (f : X ⟶ Y) [IsAffineHom f] (L : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) :
    (L.pullback f).IsAmple := by
  apply (L.pullback f).isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 (f x)
  obtain ⟨e⟩ := LinePowerPullback.linePower_pullback_iso f L n
  let t := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ e.hom
  have ht : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = f ⁻¹ᵁ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ e).trans
      (LineSectionNonvanishingPullback.lineSectionNonvanishing_pullback f (L.tensorPower n) s)
  exact ⟨n, hn, t, ht.symm ▸ hx, ht.symm ▸ hs.preimage f⟩

end

end OAI.RepresentationTheory.Theta.Geometric.AmpleAffinePullback
