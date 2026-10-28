import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FamilyIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientOpenFrame

/-! # Coordinate Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateIdeal.Construction

noncomputable section

/-! Exact ideals for quotient-coordinate centers on actual ambient neighborhoods. -/

universe u

theorem coordinateFamilyIdeal_map
    {R S ι : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : ι → R) (C : Finset ι) :
    (Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal g C).map f = Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (fun i => f (g i)) C := by
  rw [Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal, Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal, Ideal.map_span, ← Set.image_comp]
  rfl

theorem coordinateFamilyIdeal_with_normal
    {R ι : Type u} [CommRing R] [DecidableEq ι] (g : ι → R) (z : R) (C : Finset ι) :
    Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z) (insert none (C.image some)) =
      Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal g C ⊔ Ideal.span {z} := by
  rw [Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
  change Ideal.span {z} ⊔ Ideal.span _ = _
  rw [sup_comm]
  congr 1
  apply congrArg Ideal.span
  ext r
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨some i, Finset.mem_image_of_mem some hi, rfl⟩

theorem quotient_preimage_coordinate_family
    {R Q ι : Type u} [CommRing R] [CommRing Q] [DecidableEq ι]
    (q : R →+* Q) (hq : Function.Surjective q) (z : R)
    (hker : RingHom.ker q = Ideal.span {z}) (g : ι → R) (C : Finset ι) :
    (Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (fun i => q (g i)) C).comap q =
      Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z) (insert none (C.image some)) := by
  rw [← coordinateFamilyIdeal_map q g C, Ideal.comap_map_of_surjective q hq,
    ← RingHom.ker_eq_comap_bot, hker, coordinateFamilyIdeal_with_normal]

theorem quotient_center_map_of_kernel_square
    {R S Q : Type*} [CommRing R] [CommRing S] [CommRing Q]
    (q : R →+* Q) (q' : S →+* Q) (f : R →+* S)
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hcomm : q'.comp f = q) (hker : RingHom.ker q' = (RingHom.ker q).map f)
    (K : Ideal Q) : (K.comap q).map f = K.comap q' := by
  let I := (K.comap q).map f
  have hm : I.map q' = K := by
    change ((K.comap q).map f).map q' = K
    rw [Ideal.map_map, hcomm, Ideal.map_comap_of_surjective q hq]
  have hk : RingHom.ker q' ≤ I := by
    rw [hker]
    exact Ideal.map_mono (Ideal.comap_mono bot_le)
  have h := Ideal.comap_map_of_surjective q' hq' I
  rw [hm, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hk] at h
  exact h.symm

theorem quotient_center_map_of_surjective_kernel_square
    {R S Q T : Type*} [CommRing R] [CommRing S] [CommRing Q] [CommRing T]
    (q : R →+* Q) (q' : S →+* T) (f : R →+* S) (a : Q →+* T)
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hcomm : q'.comp f = a.comp q) (hker : RingHom.ker q' = (RingHom.ker q).map f)
    (K : Ideal Q) : (K.comap q).map f = (K.map a).comap q' := by
  let I := (K.comap q).map f
  have hm : I.map q' = K.map a := by
    change ((K.comap q).map f).map q' = K.map a
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective q hq]
  have hk : RingHom.ker q' ≤ I := by
    rw [hker]
    exact Ideal.map_mono (Ideal.comap_mono bot_le)
  have h := Ideal.comap_map_of_surjective q' hq' I
  rw [hm, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hk] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateIdeal.Construction
