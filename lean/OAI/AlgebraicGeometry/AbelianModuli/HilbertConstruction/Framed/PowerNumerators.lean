import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineExtension

/-! # Power Numerators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PowerNumerators

noncomputable section

/-!
Explicit numerators in framed tensor powers and extension in every sufficiently
large degree. These formulas allow a finite collection of affine charts to use
one common tensor power.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- The section with coordinate `b` in the frame induced on the nth tensor power. -/
def framedPowerNumerator (e : Line.Bundles.structureModule X ⟶ L) (n : ℕ) (b : Γ(X, ⊤)) :
    Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n :=
  (Global.Sections.structureModuleEndRingEquiv X).symm b ≫ TensorPower.Maps.tensorPowerSection e n

theorem framedPowerNumerator_coordinate (e : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (n : ℕ) (b : Γ(X, ⊤)) :
    Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e n) (framedPowerNumerator e n b) = b :=
  (AffineExtension.frameCoordinate_scalar_frame (TensorPower.Maps.tensorPowerSection e n) ((Global.Sections.structureModuleEndRingEquiv X).symm b)).trans
    ((Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply b)

/-- Clearing the coordinate denominator suffices for the explicit numerator
section to have the desired ratio on `D(s)`. -/
theorem framedPowerNumerator_extends (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (n : ℕ) (b : Γ(X, ⊤)) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hb : (Ample.LineBundles.sectionNonvanishing s).ι.appTop b =
      ((Ample.LineBundles.sectionNonvanishing s).ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ n * r) :
    letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n))
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (framedPowerNumerator e n b)) = r := by
  let D := Ample.LineBundles.sectionNonvanishing s
  let ep := Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n)
  let sp := Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection s n)
  let tp := Ample.LineBundles.pullbackSection D.ι (framedPowerNumerator e n b)
  have : IsIso ep := inferInstanceAs (IsIso (Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n)))
  have : IsIso sp := Power.Nonvanishing.tensorPowerSection_pullback_isIso D.ι s n
  have hnum : Frame.Coordinates.frameCoordinate ep tp = D.ι.appTop b :=
    (Frame.FrameRestriction.frameCoordinate_pullback D.ι (TensorPower.Maps.tensorPowerSection e n) (framedPowerNumerator e n b)).trans
      (congrArg D.ι.appTop (framedPowerNumerator_coordinate e n b))
  have hden : Frame.Coordinates.frameCoordinate ep sp = (D.ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ n :=
    Power.FrameCoordinates.frameCoordinate_tensorPowerSection_pullback D.ι e s n
  change Frame.Coordinates.frameCoordinate sp tp = r
  apply (Frame.Coordinates.frameCoordinate_isUnit ep sp).mul_left_cancel
  exact (Frame.Coordinates.frameCoordinate_change ep sp tp).symm.trans
    (hnum.trans (hb.trans (congrArg (fun q => q * r) hden).symm))

/-- One numerator gives numerators in every larger degree, by multiplying its
coefficient by the corresponding power of the denominator coordinate. -/
theorem framedPowerNumerator_increase (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    {n m : ℕ} (b : Γ(X, ⊤)) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hb : (Ample.LineBundles.sectionNonvanishing s).ι.appTop b =
      ((Ample.LineBundles.sectionNonvanishing s).ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ n * r)
    (hnm : n ≤ m) :
    (Ample.LineBundles.sectionNonvanishing s).ι.appTop ((Frame.Coordinates.frameCoordinate e s) ^ (m - n) * b) =
      ((Ample.LineBundles.sectionNonvanishing s).ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ m * r := by
  let a := (Ample.LineBundles.sectionNonvanishing s).ι.appTop.hom
  change a ((Frame.Coordinates.frameCoordinate e s) ^ (m - n) * b) = a (Frame.Coordinates.frameCoordinate e s) ^ m * r
  rw [map_mul, map_pow]
  have hb' : a b = a (Frame.Coordinates.frameCoordinate e s) ^ n * r := hb
  rw [hb', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]

/-- Affine framed section extension works in every sufficiently large degree. -/
theorem framed_affine_section_extension_eventually [IsAffine X]
    (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n), ∀ m : ℕ, n ≤ m →
      ∃ t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L m,
        letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s m
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s m))
          (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t) = r := by
  obtain ⟨n, hn, b, hb⟩ := AffineLocalization.framed_nonvanishing_clear_denominator e s r
  refine ⟨n, hn, fun m hnm => ⟨framedPowerNumerator e m ((Frame.Coordinates.frameCoordinate e s) ^ (m - n) * b), ?_⟩⟩
  exact framedPowerNumerator_extends e s m _ r (framedPowerNumerator_increase e s b r hb hnm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PowerNumerators
