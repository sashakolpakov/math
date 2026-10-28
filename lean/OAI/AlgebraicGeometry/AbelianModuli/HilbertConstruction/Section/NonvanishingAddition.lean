import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Nonvanishing Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Nonvanishing of a sum of line-bundle sections is contained in the union of their nonvanishing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Section.NonvanishingAddition.pullbackSection_add {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f (s + t) = Ample.LineBundles.pullbackSection f s + Ample.LineBundles.pullbackSection f t := by
  simp only [Ample.LineBundles.pullbackSection, Functor.map_add, Preadditive.comp_add]

theorem Section.NonvanishingAddition.sectionNonvanishing_add_le_of_frame {X : Scheme.{u}} {M : X.Modules}
    (a s t : Line.Bundles.structureModule X ⟶ M) [IsIso a] :
    Ample.LineBundles.sectionNonvanishing (s + t) ≤ Ample.LineBundles.sectionNonvanishing s ⊔ Ample.LineBundles.sectionNonvanishing t := by
  rw [Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate a (s + t), Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate a s,
    Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate a t]
  have h : Frame.Coordinates.frameCoordinate a (s + t) = Frame.Coordinates.frameCoordinate a s + Frame.Coordinates.frameCoordinate a t := by
    simp only [Frame.Coordinates.frameCoordinate, Frame.Coordinates.frameCoordinateEnd, Preadditive.add_comp, map_add]
  rw [h]
  exact X.basicOpen_add_le _ _

theorem Line.Bundles.LineBundle.sectionNonvanishing_add_le {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s t : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing (s + t) ≤ Ample.LineBundles.sectionNonvanishing s ⊔ Ample.LineBundles.sectionNonvanishing t := by
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
  let y : U.toScheme := ⟨x, hxU⟩
  have h := Section.NonvanishingAddition.sectionNonvanishing_add_le_of_frame e.inv (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t)
  rw [← Section.NonvanishingAddition.pullbackSection_add, Section.Nonvanishing.sectionNonvanishing_pullback, Section.Nonvanishing.sectionNonvanishing_pullback,
    Section.Nonvanishing.sectionNonvanishing_pullback] at h
  exact h (show y ∈ U.ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (s + t) from hx)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
