import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame

/-! # Coordinate Center Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateCenterChart.Construction

noncomputable section

/-! Coordinate charts retaining the exact center and all selected boundary equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem subsetCoordinateIdeal_map_embedded_family {σ θ k A : Type u}
    [CommRing k] [CommRing A] [Fintype θ] [DecidableEq σ]
    (e : θ ↪ σ) (φ : MvPolynomial σ k →+* A) :
    (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (Finset.univ.image e)).map φ =
      Ideal.span (Set.range (fun j => φ (MvPolynomial.X (e j)))) := by
  rw [SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨MvPolynomial.X (e j), ⟨e j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, rfl⟩, rfl⟩

/-- A full actual étale coordinate chart in which the center is a
specified coordinate subset and each prescribed boundary equation is
one of those coordinates, with the original point and field map retained. -/
structure BoundaryCoordinateCenterOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {n : ℕ} (w : Fin n → R)
    (p : PrimeSpectrum R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  point : PrimeSpectrum carrier
  point_over : PrimeSpectrum.comap map.toRingHom point = p
  indices : Type u
  finite : Fintype indices
  decidableEq : DecidableEq indices
  coordinateMap : MvPolynomial indices k →+* carrier
  coordinateEtale : coordinateMap.Etale
  coordinateGround : ∀ c : k, coordinateMap (MvPolynomial.C c) = algebraMap k carrier c
  centerIndices : Finset indices
  centerIdeal : I.map map.toRingHom = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal centerIndices).map coordinateMap
  boundaryIndex : Fin n ↪ indices
  boundary_in_center : ∀ j, boundaryIndex j ∈ centerIndices
  boundaryCoordinates : ∀ j, coordinateMap (MvPolynomial.X (boundaryIndex j)) = map (w j)

attribute [instance] BoundaryCoordinateCenterOpenChart.algebra BoundaryCoordinateCenterOpenChart.isOpenImmersion
  BoundaryCoordinateCenterOpenChart.finite BoundaryCoordinateCenterOpenChart.decidableEq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateCenterChart.Construction
