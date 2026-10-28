import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateCenterChart

/-! # Center Chart Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compose pointed coordinate-center charts with their original base opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k : Type u} [CommRing k] {R S : CommRingCat.{u}} [Algebra k R] [Algebra k S]

def Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart.comp (f : R →ₐ[k] S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (I : Ideal R) {n : ℕ} (w : Fin n → R) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f.toRingHom q = p)
    (C : Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k S (I.map f.toRingHom) (fun j => f (w j)) q) :
    Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R I w p := by
  refine { carrier := C.carrier
           algebra := C.algebra
           map := C.map.comp f
           isOpenImmersion := ?_
           point := C.point
           point_over := ?_
           indices := C.indices
           finite := C.finite
           decidableEq := C.decidableEq
           coordinateMap := C.coordinateMap
           coordinateEtale := C.coordinateEtale
           coordinateGround := C.coordinateGround
           centerIndices := C.centerIndices
           centerIdeal := ?_
           boundaryIndex := C.boundaryIndex
           boundary_in_center := C.boundary_in_center
           boundaryCoordinates := C.boundaryCoordinates }
  · change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom C.map.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change C.point.asIdeal.comap (C.map.toRingHom.comp f.toRingHom) = p.asIdeal
    have hC : C.point.asIdeal.comap C.map.toRingHom = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal C.point_over
    have hq' : q.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [← Ideal.comap_comap, hC, hq']
  · change I.map (C.map.toRingHom.comp f.toRingHom) = _
    rw [← Ideal.map_map]
    exact C.centerIdeal

end

end OAI.AlgebraicGeometry.Resolution.Blowups
