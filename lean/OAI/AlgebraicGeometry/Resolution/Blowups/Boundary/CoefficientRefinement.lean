import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart

/-! # Coefficient Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

/-! Refine an actual coefficient neighborhood without losing its normal derivative or original point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {w : ι → R} {J : Ideal R} {n : ℕ} {p : PrimeSpectrum R}

def CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart.refine (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p)
    (B : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k C.carrier (fun j => C.map (w j)) C.point)
    (hcoeff : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (B.carrier ⧸ Ideal.span {B.map C.normal}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {B.map C.normal}) (B.map (C.map (w j))))) :
    CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p := by
  let : Algebra.Smooth k C.carrier := C.ambientModel.smooth
  have hf : B.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom B.map.toRingHom)))
  let : Algebra C.carrier B.carrier := B.map.toRingHom.toAlgebra
  let : IsScalarTower k C.carrier B.carrier :=
    IsScalarTower.of_algebraMap_eq (fun c => (B.map.commutes c).symm)
  let : Algebra.Etale C.carrier B.carrier := RingHom.etale_algebraMap.mp hf
  let g := B.map.comp C.map
  have hBI : B.point.asIdeal.comap B.map.toRingHom = C.point.asIdeal :=
    congrArg PrimeSpectrum.asIdeal B.point_over
  have hCI : C.point.asIdeal.comap C.map.toRingHom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  refine
    { carrier := B.carrier
      algebra := B.algebra
      map := g
      isOpenImmersion := ?_
      point := B.point
      point_over := ?_
      normal := B.map C.normal
      normal_mem := ?_
      normal_mem_point := ?_
      derivative := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := B.carrier) C.derivative
      derivative_normal := ?_
      derivative_tangent := ?_
      ambientModel := B.model
      coefficientModel := hcoeff }
  · change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom C.map.toRingHom ≫ CommRingCat.ofHom B.map.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change B.point.asIdeal.comap (B.map.toRingHom.comp C.map.toRingHom) = p.asIdeal
    rw [← Ideal.comap_comap, hBI, hCI]
  · have h := Ideal.mem_map_of_mem B.map.toRingHom C.normal_mem
    rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k B.map hf (J.map C.map.toRingHom) n] at h
    change B.map C.normal ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (J.map (B.map.toRingHom.comp C.map.toRingHom)) n
    rw [← Ideal.map_map]
    exact h
  · change C.normal ∈ B.point.asIdeal.comap B.map.toRingHom
    rw [hBI]
    exact C.normal_mem_point
  · change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := B.carrier) C.derivative
      (algebraMap C.carrier B.carrier C.normal) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, C.derivative_normal, map_one]
  · exact Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := B.carrier) k
      (fun j => C.map (w j)) ⟨C.derivative, C.derivative_tangent⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
