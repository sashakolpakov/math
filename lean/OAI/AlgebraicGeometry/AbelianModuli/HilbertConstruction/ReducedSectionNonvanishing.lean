import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality
import Mathlib.AlgebraicGeometry.Properties

/-! # Reduced Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a reduced scheme, a line-bundle section vanishes if and only if its nonvanishing open is empty. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}} [IsReduced X] (L : Line.Bundles.LineBundle X)

theorem Line.Bundles.LineBundle.sectionNonvanishing_eq_bot_iff (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing s = ⊥ ↔ s = 0 := by
  constructor
  · intro hs
    choose U hU e using L.locallyTrivial
    apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover U (fun x => ⟨x, hU x⟩) s 0
    intro x
    let E := (e x).some
    let t := Ample.LineBundles.pullbackSection (U x).ι s
    have ht : Ample.LineBundles.sectionNonvanishing t = ⊥ := by
      rw [Section.Nonvanishing.sectionNonvanishing_pullback, hs]
      rfl
    have hc : Frame.Coordinates.frameCoordinate E.inv t = 0 :=
      eq_zero_of_basicOpen_eq_bot _
        ((Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate E.inv t).symm.trans ht)
    have he : Frame.Coordinates.frameCoordinateEnd E.inv t = 0 :=
      (Global.Sections.structureModuleEndValue_injective _)
        (hc.trans (map_zero (Frame.Coordinates.structureModuleEndValue _)).symm)
    have hz : t = 0 := by
      rw [← Frame.Coordinates.frameCoordinateEnd_frame E.inv t, he, zero_comp]
    apply (cancel_epi (Line.Bundles.structureModulePullbackIso (U x).ι).inv).mp
    change Ample.LineBundles.pullbackSection (U x).ι s = Ample.LineBundles.pullbackSection (U x).ι 0
    rw [ZeroSections.pullbackSection_zero]
    exact hz
  · rintro rfl
    exact L.sectionNonvanishing_zero

theorem Line.Bundles.LineBundle.exists_nonvanishing_of_ne_zero (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    ∃ x : X, x ∈ Ample.LineBundles.sectionNonvanishing s := by
  classical
  by_contra h
  apply hs
  apply (L.sectionNonvanishing_eq_bot_iff s).mp
  apply le_bot_iff.mp
  intro x hx
  exact False.elim (h ⟨x, hx⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
