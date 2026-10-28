import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart

/-! # Coefficient Open Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

/-! Compose pointed coefficient neighborhoods with their original boundary open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {k : Type u} [CommRing k] {R S : CommRingCat.{u}} [Algebra k R] [Algebra k S]
  {ι : Type v} (w : ι → R) (J : Ideal R) (n : ℕ)

def CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart.comp (f : R →ₐ[k] S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    {q : PrimeSpectrum S}
    (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k S (fun j => f (w j)) (J.map f.toRingHom) n q)
    (p : PrimeSpectrum R) (hq : PrimeSpectrum.comap f.toRingHom q = p) :
    CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p := by
  refine
    { carrier := C.carrier
      algebra := C.algebra
      map := C.map.comp f
      isOpenImmersion := ?_
      point := C.point
      point_over := ?_
      normal := C.normal
      normal_mem := ?_
      normal_mem_point := C.normal_mem_point
      derivative := C.derivative
      derivative_normal := C.derivative_normal
      derivative_tangent := C.derivative_tangent
      ambientModel := C.ambientModel
      coefficientModel := C.coefficientModel }
  · change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom C.map.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change C.point.asIdeal.comap (C.map.toRingHom.comp f.toRingHom) = p.asIdeal
    have hC : C.point.asIdeal.comap C.map.toRingHom = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal C.point_over
    have hp : q.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [← Ideal.comap_comap, hC, hp]
  · change C.normal ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (J.map (C.map.toRingHom.comp f.toRingHom)) n
    rw [← Ideal.map_map]
    exact C.normal_mem

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
