import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Smooth

/-! # Localized Center Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCenterSmoothness.Construction

noncomputable section

/-! Smoothness of a closed center from actual ambient principal neighborhoods. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- Smoothness descends from actual localized ambient quotient rings when
their defining principal opens cover the closed center. -/
theorem smooth_quotient_of_localized_quotients (I : Ideal R) (s : Set R)
    (hs : Ideal.span ((Ideal.Quotient.mk I) '' s) = ⊤)
    (hlocal : ∀ r ∈ s, Algebra.Smooth k
      (Localization.Away r ⧸ I.map (algebraMap R (Localization.Away r)))) :
    Algebra.Smooth k (R ⧸ I) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget.ofIsLocalization
    RingHom.Smooth.propertyIsLocal.respectsIso (algebraMap k (R ⧸ I))
    ((Ideal.Quotient.mk I) '' s) hs
  rintro ⟨_, r, hr, rfl⟩
  let Q := R ⧸ I
  let A := Localization.Away r
  let B := A ⧸ I.map (algebraMap R A)
  have hpow : Algebra.algebraMapSubmonoid Q (Submonoid.powers r) =
      Submonoid.powers (Ideal.Quotient.mk I r) := Submonoid.map_powers _ _
  let : IsLocalization.Away (Ideal.Quotient.mk I r) B := by
    change IsLocalization (Submonoid.powers (Ideal.Quotient.mk I r)) B
    rw [← hpow]
    infer_instance
  let : IsScalarTower k Q B := Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  refine ⟨B, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← IsScalarTower.algebraMap_eq k Q B, RingHom.smooth_algebraMap]
  exact hlocal r hr

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCenterSmoothness.Construction
