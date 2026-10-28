import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.BaseChangeUniversality
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Affine pullback preserves ampleness of actual algebraic line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : Line.Bundles.LineBundle Y}

theorem Line.Bundles.LineBundle.IsAmple.pullback_of_isAffineHom (hL : L.IsAmple) (f : X ⟶ Y)
    [IsAffineHom f] : (L.pullback f).IsAmple := by
  have hX : IsCompact (Set.univ : Set X) := by
    simpa only [Set.preimage_univ] using
      (QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ hL.1)
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨n, hn, P, hP, s, hx, hs⟩ := hL.2 (f x)
  refine ⟨n, hn, P.pullback f, hP.pullback_lineBundle f, Ample.LineBundles.pullbackSection f s, ?_, ?_⟩
  · change x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
    rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f P s]
    exact hx
  · change IsAffineOpen (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s))
    rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f P s]
    exact hs.preimage f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
