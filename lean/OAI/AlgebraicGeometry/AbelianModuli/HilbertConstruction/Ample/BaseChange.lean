import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness is invariant under change by a scheme isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : Line.Bundles.LineBundle Y}

/-- Pullback by an isomorphism preserves ampleness. -/
theorem Line.Bundles.LineBundle.IsAmple.pullback_of_isIso (hL : L.IsAmple) (f : X ⟶ Y) [IsIso f] :
    (L.pullback f).IsAmple := by
  refine ⟨f.homeomorph.isCompact_preimage.mpr hL.1, fun x => ?_⟩
  obtain ⟨n, hn, P, hP, s, hxs, hs⟩ := hL.2 (f x)
  refine ⟨n, hn, P.pullback f, hP.pullback_of_isOpenImmersion f,
    Ample.LineBundles.pullbackSection f s, ?_, ?_⟩
  · change x ∈ @Ample.LineBundles.sectionNonvanishing X ((Scheme.Modules.pullback f).obj P.sheaf)
      (Ample.LineBundles.pullbackSection f s)
    rw [Section.Nonvanishing.sectionNonvanishing_pullback]
    exact hxs
  · change IsAffineOpen (@Ample.LineBundles.sectionNonvanishing X ((Scheme.Modules.pullback f).obj P.sheaf)
      (Ample.LineBundles.pullbackSection f s))
    rw [Section.Nonvanishing.sectionNonvanishing_pullback]
    exact hs.preimage f

/-- Pullback by an isomorphism also reflects ampleness. -/
theorem Line.Bundles.LineBundle.isAmple_pullback_iff_of_isIso (f : X ⟶ Y) [IsIso f] :
    (L.pullback f).IsAmple ↔ L.IsAmple := by
  constructor
  · intro h
    exact (h.pullback_of_isIso (inv f)).of_iso
      ((Scheme.Modules.pullbackComp (inv f) f).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app L.sheaf ≪≫
          (Scheme.Modules.pullbackId Y).app L.sheaf)
  · intro h
    exact h.pullback_of_isIso f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
