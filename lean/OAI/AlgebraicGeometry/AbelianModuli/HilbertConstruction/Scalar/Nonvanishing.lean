import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

noncomputable section

/-! The local-frame nonvanishing open agrees with the usual basic open of its regular coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A global regular function is invertible precisely when its basic open is the whole scheme. -/
theorem global_isUnit_iff_basicOpen_eq_top (r : Γ(X, ⊤)) : IsUnit r ↔ X.basicOpen r = ⊤ := by
  constructor
  · exact X.basicOpen_of_isUnit
  · intro hr
    apply X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤ r
    intro x _
    exact (X.mem_basicOpen_top r x).mp (hr.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial))

/-- A scalar section is a frame on an open precisely when its restricted function is a unit. -/
theorem scalar_pullbackSection_isIso_iff (f : X ⟶ Y) [IsOpenImmersion f]
    (a : End (Line.Bundles.structureModule Y)) :
    IsIso (Ample.LineBundles.pullbackSection f a) ↔ IsUnit (f.appTop (Frame.Coordinates.structureModuleEndValue Y a)) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y) ≪≫
    Line.Bundles.structureModulePullbackIso f
  let b : End (Line.Bundles.structureModule X) := e.inv ≫ (Scheme.Modules.restrictFunctor f).map a ≫ e.hom
  have hb : IsIso b ↔ IsIso ((Scheme.Modules.restrictFunctor f).map a) := by
    simp only [b, isIso_comp_left_iff, isIso_comp_right_iff]
  have hv : Frame.Coordinates.structureModuleEndValue X b = f.appTop (Frame.Coordinates.structureModuleEndValue Y a) :=
    RestrictionScalars.structureModuleEndValue_restrict f a e
  exact (Section.Nonvanishing.isIso_pullbackSection_iff f a).trans
    ((Power.Nonvanishing.isIso_restrict_map_iff f a).symm.trans
      (hb.symm.trans ((Global.Sections.structureModuleEnd_isIso_iff b).trans (congrArg IsUnit hv).to_iff)))

/-- The nonvanishing open of a scalar sheaf map is the basic open of its global function. -/
theorem sectionNonvanishing_scalar (a : End (Line.Bundles.structureModule X)) :
    Ample.LineBundles.sectionNonvanishing a = X.basicOpen (Frame.Coordinates.structureModuleEndValue X a) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    change X.Opens at U
    have hu : IsUnit (U.ι.appTop (Frame.Coordinates.structureModuleEndValue X a)) :=
      (scalar_pullbackSection_isIso_iff U.ι a).mp hU
    have hpre : U.ι ⁻¹ᵁ X.basicOpen (Frame.Coordinates.structureModuleEndValue X a) = ⊤ :=
      (U.ι.preimage_basicOpen_top _).trans (U.toScheme.basicOpen_of_isUnit hu)
    exact (show (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (Frame.Coordinates.structureModuleEndValue X a) from
      hpre.symm ▸ trivial)
  · let U : X.Opens := X.basicOpen (Frame.Coordinates.structureModuleEndValue X a)
    have hpre : U.ι ⁻¹ᵁ U = ⊤ := by
      ext x
      exact iff_true_intro x.property
    have hu : IsUnit (U.ι.appTop (Frame.Coordinates.structureModuleEndValue X a)) :=
      (global_isUnit_iff_basicOpen_eq_top _).mpr ((U.ι.preimage_basicOpen_top _).symm.trans hpre)
    apply le_sSup
    exact (scalar_pullbackSection_isIso_iff U.ι a).mpr hu

/-- In a global frame, the nonvanishing open of a section is the basic open of its coordinate. -/
theorem sectionNonvanishing_frameCoordinate {L : X.Modules} (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] :
    Ample.LineBundles.sectionNonvanishing t = X.basicOpen (Frame.Coordinates.frameCoordinate s t) := by
  have he : Ample.LineBundles.sectionNonvanishing t = Ample.LineBundles.sectionNonvanishing (Frame.Coordinates.frameCoordinateEnd s t) :=
    (congrArg (fun z : Line.Bundles.structureModule X ⟶ L => Ample.LineBundles.sectionNonvanishing z)
      (Frame.Coordinates.frameCoordinateEnd_frame s t).symm).trans
        (Ample.Powers.sectionNonvanishing_comp_iso (Frame.Coordinates.frameCoordinateEnd s t) (asIso s))
  exact he.trans (sectionNonvanishing_scalar (Frame.Coordinates.frameCoordinateEnd s t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
