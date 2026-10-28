import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCopy
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearPartial

/-! # Sheared Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearedCoordinates.Construction

noncomputable section

/-! Realize the coordinate shear as a separate étale presentation of the same ring. -/

universe u

variable {σ k R : Type u} [Field k] [CommRing R]
  [Algebra k R] [Algebra (MvPolynomial σ k) R]
  [Algebra.Etale (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [DecidableEq σ]

/-- Construct an isomorphic ambient chart whose `j`th coordinate is the old
`j`th coordinate minus the fixed `i`th coordinate, retaining every other one. -/
theorem exists_etale_sheared_coordinates (i j : σ) (hij : i ≠ j) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S)
      (_ : Algebra (MvPolynomial σ k) S),
      IsScalarTower k (MvPolynomial σ k) S ∧ Algebra.Etale (MvPolynomial σ k) S ∧
      ∃ e : R ≃ₐ[k] S, ∀ a : σ, algebraMap (MvPolynomial σ k) S (MvPolynomial.X a) =
        e (if a = j then algebraMap (MvPolynomial σ k) R (MvPolynomial.X j) -
          algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
          else algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) := by
  let α := IsScalarTower.toAlgHom k (MvPolynomial σ k) R
  let β := α.comp (Coordinate.Shear.Construction.coordinateShear (k := k) i j hij).toAlgHom
  have hα : α.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hβ : β.toRingHom.Etale := by
    have he : β.toRingHom = α.toRingHom.comp (Coordinate.Shear.Construction.coordinateShear (k := k) i j hij).toRingHom := by
      apply RingHom.ext
      intro p
      rfl
    rw [he]
    exact RingHom.Etale.stableUnderComposition (Coordinate.Shear.Construction.coordinateShear (k := k) i j hij).toRingHom
      α.toRingHom (RingHom.Etale.of_bijective (Coordinate.Shear.Construction.coordinateShear (k := k) i j hij).bijective) hα
  obtain ⟨S, instS, instkS, instPS, htor, hS, e, he⟩ :=
    CoordinateCopy.Construction.exists_isomorphic_etale_coordinate_copy β hβ
  refine ⟨S, instS, instkS, instPS, htor, hS, e, ?_⟩
  intro a
  rw [he]
  change e (α (Coordinate.Shear.Construction.coordinateShear (k := k) i j hij (MvPolynomial.X a))) = _
  rw [Coordinate.Shear.Construction.coordinateShear_X]
  split_ifs
  · rw [map_sub]
    rfl
  · rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearedCoordinates.Construction
