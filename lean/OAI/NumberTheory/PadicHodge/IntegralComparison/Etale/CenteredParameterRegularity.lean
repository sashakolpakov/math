import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateSectionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate

/-! # Centered Parameter Regularity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterRegularity

noncomputable section

/-! Centering the genuine étale coordinates preserves their regular
sequence over an arbitrary coefficient ring. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations

universe u
variable {R A σ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype σ] [Algebra (MvPolynomial σ R) A]
  [IsScalarTower R (MvPolynomial σ R) A] [Algebra.Etale (MvPolynomial σ R) A]
  (ε : A →ₐ[R] R)

omit [Fintype σ] [Algebra.Etale (MvPolynomial σ R) A] in
theorem parameter_eq (j : σ) :
    CoordinateSectionKernel.parameter ε j = AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ j -
      algebraMap R A (CoordinateSectionKernel.point ε j) := by
  rw [CoordinateSectionKernel.parameter, map_sub]
  change AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ j - algebraMap (MvPolynomial σ R) A
    (algebraMap R (MvPolynomial σ R) (CoordinateSectionKernel.point ε j)) = _
  rw [← IsScalarTower.algebraMap_apply]

omit [Fintype σ] in
theorem derivative [DecidableEq σ] (i j : σ) :
    AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i (CoordinateSectionKernel.parameter ε j) =
      if j = i then 1 else 0 := by
  rw [parameter_eq, map_sub, Derivation.map_algebraMap, sub_zero, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation_coordinate]

theorem regular {m : ℕ} (e : Fin m ≃ σ) :
    RingTheory.Sequence.IsWeaklyRegular A
      (List.ofFn (fun i => CoordinateSectionKernel.parameter ε (e i))) := by
  classical
  let : Algebra.Smooth R (MvPolynomial σ R) := {}
  let : Algebra.Smooth R A := Algebra.Smooth.comp R (MvPolynomial σ R) A
  apply IntegralComparison.Smooth.RegularSequence.CoordinateRegularity.family_isWeaklyRegular
    (fun i => CoordinateSectionKernel.parameter ε (e i))
    (fun i => AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ (e i))
  intro i j
  simpa only [e.injective.eq_iff, eq_comm] using derivative ε (e i) (e j)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterRegularity
