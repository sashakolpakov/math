import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ModuleFlatness
import Mathlib.RingTheory.RingHom.Flat

/-! # Ring Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.RingFlatness

noncomputable section

/-! Flatness of the canonical coefficient-quotient ring map with a prescribed target ideal. -/

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A))

def map : R ⧸ I →+* A ⧸ J :=
  Ideal.quotientMap J (algebraMap R A) (by rw [hJ]; exact Ideal.le_comap_map)

theorem map_mk (r : R) : RingFlatness.map R A I J hJ (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk J (algebraMap R A r) := rfl

theorem flat [Module.Flat R A] : (RingFlatness.map R A I J hJ).Flat := by
  subst J
  change (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A))).Flat
  exact RingHom.flat_algebraMap_iff.mpr (ModuleFlatness.flat R A I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.RingFlatness
