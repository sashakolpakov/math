import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts

/-! # Center Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary

noncomputable section

/-! Compose actual common-coordinate center charts with an original affine open map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {k : Type u} [CommRing k] {R S : CommRingCat.{u}} [Algebra k R] [Algebra k S]
  {ι : Type v}

def CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.comp (I : Ideal R) (w : ι → R) (F : Finset ι)
    (f : R →ₐ[k] S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    {q : PrimeSpectrum S}
    (C : CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k S (I.map f.toRingHom) (fun j => f (w j)) F q)
    (p : PrimeSpectrum R) (hq : PrimeSpectrum.comap f.toRingHom q = p) :
    CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p := by
  let B : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p :=
    { carrier := C.chart.carrier
      algebra := C.chart.algebra
      map := C.chart.map.comp f
      isOpenImmersion := by
        change IsOpenImmersion (Spec.map
          (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom C.chart.map.toRingHom))
        rw [Spec.map_comp]
        infer_instance
      point := C.chart.point
      point_over := by
        apply PrimeSpectrum.ext
        change C.chart.point.asIdeal.comap (C.chart.map.toRingHom.comp f.toRingHom) = p.asIdeal
        have hC : C.chart.point.asIdeal.comap C.chart.map.toRingHom = q.asIdeal :=
          congrArg PrimeSpectrum.asIdeal C.chart.point_over
        have hp : q.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
        rw [← Ideal.comap_comap, hC, hp]
      model := C.chart.model }
  refine { chart := B
           coordinates := C.coordinates
           center_eq := ?_
           divided_iff := C.divided_iff }
  change I.map (C.chart.map.toRingHom.comp f.toRingHom) = _
  rw [← Ideal.map_map]
  exact C.center_eq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary
