import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientOpenFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FamilyIdeal

/-! # Dual Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.DualFrame.Construction

noncomputable section

/-! Actual common-coordinate charts from a finite dual frame, including unit boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem mixed_boundary_chart_of_dual_frame
    {k : Type u} [CommRing k] (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {β : Type v}
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (C : Finset ι) (w a : β → R) (ha : ∀ j, IsUnit (a j))
    (e : β → Option ι) (he : ∀ i j s, e i = some s → e j = some s → i = j)
    (hw : ∀ j, w j = a j * match e j with | none => 1 | some i => g i)
    (F : Finset β) (hF : ∀ j, j ∈ F ↔ ∃ i ∈ C, e j = some i)
    (p : PrimeSpectrum R) :
    Nonempty (CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R (Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal g C) w F p) := by
  classical
  obtain ⟨t, ht, n, φ, hφ, hφk, hX⟩ := AdaptedEtaleFrame.Construction.exists_adapted_etale_frame D g hD p.asIdeal
  let S := Localization.Away t
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  obtain ⟨P, hP⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime t p ht
  let B : Etale.BoundaryModel.Construction.EtaleBoundaryModel k S β (fun j => f (w j)) :=
    { indices := Fin n ⊕ ι
      finite := inferInstance
      decidableEq := inferInstance
      map := φ
      etale := hφ
      ground := hφk
      coordinate := fun j => (e j).map Sum.inr
      distinct := by
        intro i j s hi hj
        cases hi' : e i with
        | none => simp [hi'] at hi
        | some l =>
          cases hj' : e j with
          | none => simp [hj'] at hj
          | some m =>
            simp only [hi', Option.map_some] at hi
            simp only [hj', Option.map_some] at hj
            have hlm : l = m := Sum.inr_injective
              ((Option.some.inj hi).trans (Option.some.inj hj).symm)
            exact he i j l hi' (hj'.trans (congrArg some hlm.symm))
      multiplier := fun j => f (a j)
      multiplierUnit := fun j => (ha j).map f.toRingHom
      equation := by
        intro j
        rw [hw, map_mul]
        cases hj : e j with
        | none => simp
        | some i => simp only [Option.map_some]; rw [hX]; rfl }
  refine ⟨{ chart :=
              { carrier := .of S
                algebra := inferInstance
                map := f
                isOpenImmersion := IsOpenImmersion.of_isLocalization t
                point := P
                point_over := hP
                model := B }
            coordinates := C.image Sum.inr
            center_eq := Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal_map_eq_coordinate_center g C f.toRingHom φ hX
            divided_iff := ?_ }⟩
  intro j
  rw [hF]
  change (∃ i ∈ C, e j = some i) ↔
    ∃ s ∈ C.image (Sum.inr : ι → Fin n ⊕ ι), (e j).map Sum.inr = some s
  constructor
  · rintro ⟨i, hi, hei⟩
    exact ⟨Sum.inr i, Finset.mem_image_of_mem Sum.inr hi, by rw [hei]; rfl⟩
  · rintro ⟨s, hs, hes⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨i, hi, ?_⟩
    cases hj : e j with
    | none => simp [hj] at hes
    | some l =>
        simp only [hj, Option.map_some] at hes
        exact congrArg some (Sum.inr_injective (Option.some.inj hes))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.DualFrame.Construction
