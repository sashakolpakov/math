import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates

/-! # Affine Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineExtension

noncomputable section

/-!
Extend a regular function on a section's nonvanishing open to a section of a
positive tensor power when the original line bundle is globally framed on an
affine scheme. The equality is expressed using actual pulled-back sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- Multiplying a frame by a scalar endomorphism gives exactly that scalar coordinate. -/
theorem frameCoordinate_scalar_frame (e : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (a : End (Line.Bundles.structureModule X)) : Frame.Coordinates.frameCoordinate e (a ≫ e) = Frame.Coordinates.structureModuleEndValue X a := by
  change Frame.Coordinates.structureModuleEndValue X ((a ≫ e) ≫ inv e) = Frame.Coordinates.structureModuleEndValue X a
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- On an affine scheme with a global frame, every function on `D(s)` is the
ratio of a global section of a positive power to the same power of `s`. -/
theorem framed_affine_section_extension [IsAffine X]
    (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n) (t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n),
      letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n))
        (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t) = r := by
  obtain ⟨n, hn, b, hb⟩ := AffineLocalization.framed_nonvanishing_clear_denominator e s r
  let a : End (Line.Bundles.structureModule X) := (Global.Sections.structureModuleEndRingEquiv X).symm b
  let t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n := a ≫ TensorPower.Maps.tensorPowerSection e n
  let D := Ample.LineBundles.sectionNonvanishing s
  let ep := Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n)
  let sp := Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection s n)
  let tp := Ample.LineBundles.pullbackSection D.ι t
  have hep : IsIso ep := inferInstanceAs
    (IsIso (Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n)))
  have hsp : IsIso sp := Power.Nonvanishing.tensorPowerSection_pullback_isIso D.ι s n
  have hnum : Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e n) t = b :=
    (frameCoordinate_scalar_frame (TensorPower.Maps.tensorPowerSection e n) a).trans
      ((Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply b)
  have hnumD : Frame.Coordinates.frameCoordinate ep tp = D.ι.appTop b :=
    (Frame.FrameRestriction.frameCoordinate_pullback D.ι (TensorPower.Maps.tensorPowerSection e n) t).trans (congrArg D.ι.appTop hnum)
  have hden : Frame.Coordinates.frameCoordinate ep sp = (D.ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ n :=
    Power.FrameCoordinates.frameCoordinate_tensorPowerSection_pullback D.ι e s n
  have hu : IsUnit (Frame.Coordinates.frameCoordinate ep sp) := Frame.Coordinates.frameCoordinate_isUnit ep sp
  refine ⟨n, hn, t, ?_⟩
  change Frame.Coordinates.frameCoordinate sp tp = r
  apply hu.mul_left_cancel
  exact (Frame.Coordinates.frameCoordinate_change ep sp tp).symm.trans
    (hnumD.trans (hb.trans (congrArg (fun q => q * r) hden).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineExtension
