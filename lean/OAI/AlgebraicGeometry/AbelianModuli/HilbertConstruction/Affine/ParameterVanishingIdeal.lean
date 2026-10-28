import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-! # Parameter Vanishing Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterVanishingIdeal

noncomputable section

/-! The ideal of an actual subset of an affine parameter scheme is contained in the kernel of every field-valued point lying in that subset. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {T : Scheme.{u}} [IsAffine T]

def affineParameterVanishingIdeal (Z : Set T) : Ideal Γ(T, ⊤) :=
  PrimeSpectrum.vanishingIdeal (T.isoSpec.hom '' Z)

theorem affineParameterVanishingIdeal_le_pointIdeal
    (Z : Set T) (y : T) (hy : y ∈ Z) :
    affineParameterVanishingIdeal Z ≤ (T.isoSpec.hom y).asIdeal := by
  intro r hr
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr (T.isoSpec.hom y) ⟨y, hy, rfl⟩

theorem affineCoordinateMap_closedPoint_ideal
    {B : Type u} [Field B] (φ : Γ(T, ⊤) →+* B) :
    (T.isoSpec.hom (QuotientCoefficientMap.affineCoordinateMap φ (IsLocalRing.closedPoint B))).asIdeal = RingHom.ker φ := by
  have h : QuotientCoefficientMap.affineCoordinateMap φ ≫ T.isoSpec.hom = Spec.map (CommRingCat.ofHom φ) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => Spec.map (CommRingCat.ofHom φ) ≫ k) T.isoSpec.inv_hom_id).trans
        (Category.comp_id _))
  have hp := congrArg (fun f : Spec (.of B) ⟶ Spec Γ(T, ⊤) =>
    (f (IsLocalRing.closedPoint B)).asIdeal) h
  change (T.isoSpec.hom (QuotientCoefficientMap.affineCoordinateMap φ (IsLocalRing.closedPoint B))).asIdeal =
    Ideal.comap φ (IsLocalRing.maximalIdeal B) at hp
  rw [IsLocalRing.maximalIdeal_eq_bot] at hp
  exact hp

theorem affineParameterVanishingIdeal_le_kernel_of_point_mem
    (Z : Set T) {B : Type u} [Field B] (φ : Γ(T, ⊤) →+* B)
    (h : QuotientCoefficientMap.affineCoordinateMap φ (IsLocalRing.closedPoint B) ∈ Z) :
    affineParameterVanishingIdeal Z ≤ RingHom.ker φ := by
  have hi := affineParameterVanishingIdeal_le_pointIdeal Z
    (QuotientCoefficientMap.affineCoordinateMap φ (IsLocalRing.closedPoint B)) h
  rwa [affineCoordinateMap_closedPoint_ideal] at hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterVanishingIdeal
