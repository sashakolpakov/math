import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Smooth Fiber Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberAlgebra

noncomputable section

/-! Smoothness of the actual scheme fiber gives smoothness of its explicit residue-field tensor algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem algebraFiber_smooth_of_specFiber
    {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    (p : PrimeSpectrum C)
    [Smooth ((Spec.map (CommRingCat.ofHom (algebraMap C A))).fiberToSpecResidueField p)] :
    Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
  have : MorphismProperty.IsStableUnderBaseChange (@Smooth.{u}) := smooth_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@Smooth.{u}) := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h := (MorphismProperty.arrow_mk_iso_iff (P := @Smooth.{u})
    (Spec.fiberToSpecResidueFieldIso C A p)).mp
      (inferInstanceAs (Smooth ((Spec.map (CommRingCat.ofHom (algebraMap C A))).fiberToSpecResidueField p)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberAlgebra
