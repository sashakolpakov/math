import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianIdealSheafColon
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Colon Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ColonRestriction.Construction

noncomputable section

/-! Ideal quotients commute with actual open restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_comap_colon_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Surjective g) (J K : Ideal S) :
    (J.colon (K : Set S)).comap g = (J.comap g).colon (K.comap g : Set R) := by
  ext x
  simp only [Ideal.mem_comap, Submodule.mem_colon, smul_eq_mul, map_mul]
  constructor
  · intro h y hy
    exact h (g y) hy
  · intro h y hy
    obtain ⟨a, rfl⟩ := hg y
    exact h a hy

theorem ideal_comap_pow_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Bijective g) (I : Ideal S) (n : ℕ) :
    (I ^ n).comap g = (I.comap g) ^ n := by
  let e := RingEquiv.ofBijective g hg
  change (I ^ n).comap e = (I.comap e) ^ n
  rw [← Ideal.map_symm e, Ideal.map_pow, Ideal.map_symm e]

universe u

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The native quotient ideal sheaf commutes with pullback along an open
immersion, including the actual affine restriction identifications. -/
theorem noetherianIdealSheafColon_comap_open (J K : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap g =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap g) (K.comap g) := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal, NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact ideal_comap_colon_of_surjective (g.appIso U).inv.hom
    (g.appIso U).symm.commRingCatIsoToRingEquiv.surjective _ _

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- Powers of ideal sheaves commute with actual open pullback. -/
theorem idealSheaf_comap_pow_open (I : Y.IdealSheafData) (g : X ⟶ Y) [IsOpenImmersion g] (n : ℕ) :
    (I ^ n).comap g = (I.comap g) ^ n := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change ((I.ideal ⟨g ''ᵁ U, U.2.image_of_isOpenImmersion g⟩) ^ n).comap (g.appIso U).inv.hom =
    ((I.comap g).ideal U) ^ n
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact ideal_comap_pow_of_bijective (g.appIso U).inv.hom
    (g.appIso U).symm.commRingCatIsoToRingEquiv.bijective _ n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ColonRestriction.Construction
