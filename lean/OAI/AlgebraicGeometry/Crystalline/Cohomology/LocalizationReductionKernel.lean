import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Localization Reduction Kernel -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationReductionKernel.LocalizationReduction

noncomputable section

/-!
# Localization of an actual reduction map

Localizing a surjective reduction at a coefficient and its residue remains
surjective. Its kernel is the actual extension of the original reduction
kernel. These are the ring-theoretic conditions for principal-open
restrictions of crystalline thickenings.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] (r : R →+* A) (s : R)

local notation "RS" => Localization.Away s
local notation "AS" => Localization.Away (r s)

def map : RS →+* AS := IsLocalization.Away.map RS AS r s

theorem map_algebraMap (x : R) :
    LocalizationReduction.map R A r s (algebraMap R RS x) = algebraMap A AS (r x) := by
  simp only [LocalizationReduction.map, IsLocalization.Away.map, IsLocalization.map_eq]

theorem kernel : RingHom.ker (LocalizationReduction.map R A r s) = (RingHom.ker r).map (algebraMap R RS) :=
  IsLocalization.ker_map (S := RS) AS r (Submonoid.map_powers r s)

theorem surjective (hr : Function.Surjective r) : Function.Surjective (LocalizationReduction.map R A r s) := by
  apply (IsLocalization.Away.map_surjective_iff RS AS r s).mpr
  intro a
  obtain ⟨b, rfl⟩ := hr a
  exact ⟨b, 0, by rw [pow_zero, one_mul]⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationReductionKernel.LocalizationReduction
