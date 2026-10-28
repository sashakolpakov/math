import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineLocalization

noncomputable section

/-!
Regular functions on the nonvanishing open of a section in an affine global
frame have denominators given by powers of that section's coordinate.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsAffine X] {L : X.Modules}

/-- In a global line-bundle frame, the ring of the section's nonvanishing open
is the localization at its coordinate. -/
theorem framed_nonvanishing_localization (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e] :
    letI := (Ample.LineBundles.sectionNonvanishing s).ι.appTop.hom.toAlgebra
    IsLocalization.Away (Frame.Coordinates.frameCoordinate e s) Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) := by
  rw [Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate e s]
  exact Γ_restrict_isLocalization X (Frame.Coordinates.frameCoordinate e s)

/-- A function on a section's nonvanishing open has a global numerator after
multiplication by a positive power of the denominator coordinate. -/
theorem framed_nonvanishing_clear_denominator (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n) (b : Γ(X, ⊤)),
      (Ample.LineBundles.sectionNonvanishing s).ι.appTop b =
        ((Ample.LineBundles.sectionNonvanishing s).ι.appTop (Frame.Coordinates.frameCoordinate e s)) ^ n * r := by
  let c := Frame.Coordinates.frameCoordinate e s
  let a := (Ample.LineBundles.sectionNonvanishing s).ι.appTop.hom
  let := a.toAlgebra
  have : IsLocalization.Away c Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) :=
    framed_nonvanishing_localization e s
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers c) r
  have hb' : a b = a c ^ n * r := by
    change r * a (c ^ n) = a b at hb
    exact hb.symm.trans (by rw [map_pow, mul_comm])
  refine ⟨n + 1, Nat.zero_lt_succ n, c * b, ?_⟩
  change a (c * b) = a c ^ (n + 1) * r
  rw [map_mul, hb', pow_succ']
  exact (mul_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineLocalization
