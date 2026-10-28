import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface

/-! # Coordinate Hypersurface Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateHypersurfaceMap.Construction

noncomputable section

/-! Explicit étale coordinates on actual coordinate hypersurface quotients. -/

open _root_.MvPolynomial

universe u

variable {σ R S : Type u} [CommRing R] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ R) S] [Algebra.Etale (MvPolynomial σ R) S]

/-- Coordinates on the actual extended coordinate-center quotient. -/
def etaleSubsetCenterMap (C : Finset σ) : MvPolynomial {j : σ // j ∉ C} R →+*
    (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) :=
  (algebraMap (MvPolynomial σ R ⧸ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)
    (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))).comp
      (Smooth.SubsetCenter.Construction.subsetCoordinateCenterAlgEquiv C).symm.toRingHom

theorem etaleSubsetCenterMap_etale (C : Finset σ) :
    (etaleSubsetCenterMap (R := R) (S := S) C).Etale := by
  let : Algebra.Etale (MvPolynomial σ R ⧸ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)
      (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) :=
    Coordinate.Hypersurface.Construction.etale_quotient_of_etale (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)
  exact RingHom.Etale.stableUnderComposition
    (Smooth.SubsetCenter.Construction.subsetCoordinateCenterAlgEquiv (R := R) C).symm.toRingHom _
    (RingHom.Etale.of_bijective (Smooth.SubsetCenter.Construction.subsetCoordinateCenterAlgEquiv (R := R) C).symm.bijective)
    (RingHom.etale_algebraMap.mpr inferInstance)

omit [Algebra.Etale (MvPolynomial σ R) S] in
theorem etaleSubsetCenterMap_C (C : Finset σ) (r : R) :
    etaleSubsetCenterMap (S := S) C (MvPolynomial.C r) =
      Ideal.Quotient.mk ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
        (algebraMap (MvPolynomial σ R) S (MvPolynomial.C r)) := by
  change algebraMap (MvPolynomial σ R ⧸ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) _
    (Smooth.SubsetCenter.Construction.polynomialToSubsetCenter C (MvPolynomial.C r)) = _
  rw [Smooth.SubsetCenter.Construction.polynomialToSubsetCenter_C]
  rfl

omit [DecidableEq σ] [Algebra.Etale (MvPolynomial σ R) S] in
/-- The singleton center is the actual principal coordinate hypersurface. -/
theorem singleton_coordinate_extended_ideal (h : σ) :
    (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal {h}).map (algebraMap (MvPolynomial σ R) S) =
      Ideal.span {algebraMap (MvPolynomial σ R) S (X h)} := by
  simp only [SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Finset.coe_singleton, Set.image_singleton,
    Ideal.map_span, Set.image_singleton]

/-- Étale coordinates on `S/(X_h)`, retaining the original coefficient map. -/
theorem etaleCoordinateHypersurface_exists_coordinates (h : σ) :
    ∃ φ : MvPolynomial {j : σ // j ∉ ({h} : Finset σ)} R →+*
        (S ⧸ Ideal.span {algebraMap (MvPolynomial σ R) S (X h)}),
      φ.Etale ∧ ∀ r : R, φ (MvPolynomial.C r) =
        Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ R) S (X h)})
          (algebraMap (MvPolynomial σ R) S (MvPolynomial.C r)) := by
  let e := Ideal.quotEquivOfEq (singleton_coordinate_extended_ideal (R := R) (S := S) h)
  refine ⟨e.toRingHom.comp (etaleSubsetCenterMap {h}), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition (etaleSubsetCenterMap {h}) e.toRingHom
      (etaleSubsetCenterMap_etale {h}) (RingHom.Etale.of_bijective e.bijective)
  · intro r
    rw [RingHom.comp_apply, etaleSubsetCenterMap_C]
    rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateHypersurfaceMap.Construction
