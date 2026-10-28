import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison

/-! # Coordinate Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoordinateValues

noncomputable section

/-!
Relate coordinates of pulled-back sections to their ordinary sheaf-section
values on an image open. This converts local ratio equalities to the section
equalities used in overlap gluing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A section's value is its coordinate times the value of the frame. -/
theorem frameCoordinate_value {M : X.Modules} (e t : Line.Bundles.structureModule X ⟶ M) [IsIso e] :
    t.app ⊤ (1 : Γ(X, ⊤)) = Frame.Coordinates.frameCoordinate e t • e.app ⊤ (1 : Γ(X, ⊤)) := by
  let c := Frame.Coordinates.frameCoordinate e t
  have h := congrArg (fun a : Line.Bundles.structureModule X ⟶ M => a.app ⊤ (1 : Γ(X, ⊤)))
    (Frame.Coordinates.frameCoordinateEnd_frame e t)
  change e.app ⊤ c = t.app ⊤ (1 : Γ(X, ⊤)) at h
  have he := e.app_smul c (1 : Γ(X, ⊤))
  change e.app ⊤ (show Γ(X, ⊤) from c * 1) = c • e.app ⊤ (1 : Γ(X, ⊤)) at he
  rw [mul_one] at he
  exact h.symm.trans he

theorem restrictSection_isIso_iff (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) : IsIso (Section.SectionRestriction.restrictSection f s) ↔ IsIso (Ample.LineBundles.pullbackSection f s) := by
  have hD : Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s) = Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) :=
    (Section.SectionRestriction.sectionNonvanishing_restrictSection f s).trans (Section.Nonvanishing.sectionNonvanishing_pullback f s).symm
  exact (Section.Frames.isIso_iff_sectionNonvanishing_eq_top (Section.SectionRestriction.restrictSection f s)).trans
    ((congrArg (fun U : X.Opens => U = ⊤) hD).to_iff.trans
      (Section.Frames.isIso_iff_sectionNonvanishing_eq_top (Ample.LineBundles.pullbackSection f s)).symm)

/-- Restriction and canonical pullback give the same ratio wherever the
denominator becomes a frame, even if it is not a global frame originally. -/
theorem frameCoordinate_restrictSection (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ M) [hs : IsIso (Ample.LineBundles.pullbackSection f s)] :
    letI := (restrictSection_isIso_iff f s).mpr hs
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) =
      Frame.Coordinates.frameCoordinate (Section.SectionRestriction.restrictSection f s) (Section.SectionRestriction.restrictSection f t) :=
  @Frame.Comparison.frameCoordinate_functorComparison X Y (Scheme.Modules.restrictFunctor f) (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback f) (Scheme.Modules.restrictUnitIso f)
    (Line.Bundles.structureModulePullbackIso f) M s t ((restrictSection_isIso_iff f s).mpr hs) hs

/-- A local coordinate equality becomes an ordinary equality of section
values on the image open, with scalars transported by the open-immersion ring isomorphism. -/
theorem local_frameCoordinate_value (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ M) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    t.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)) =
      (f.appIso ⊤).inv (Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t)) •
        s.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)) := by
  let s₀ := Section.SectionRestriction.restrictSection f s
  let t₀ := Section.SectionRestriction.restrictSection f t
  have : IsIso s₀ := (restrictSection_isIso_iff f s).mpr inferInstance
  have hv := frameCoordinate_value s₀ t₀
  change t₀.app ⊤ (1 : Γ(X, ⊤)) = (f.appIso ⊤).inv (Frame.Coordinates.frameCoordinate s₀ t₀) •
    (show Γ(M, f ''ᵁ ⊤) from s₀.app ⊤ (1 : Γ(X, ⊤))) at hv
  have hval := congrArg
    (fun z : Γ(M, f ''ᵁ ⊤) => (f.appIso ⊤).inv (Frame.Coordinates.frameCoordinate s₀ t₀) • z)
    (Section.SectionRestriction.restrictSection_app_one f s ⊤)
  have hcoord := congrArg (fun c : Γ(X, ⊤) =>
    (f.appIso ⊤).inv c • s.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)))
      (frameCoordinate_restrictSection f s t).symm
  exact (Section.SectionRestriction.restrictSection_app_one f t ⊤).symm.trans (hv.trans (hval.trans hcoord))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoordinateValues
