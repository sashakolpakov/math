import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Lattice Volumes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeVolumes.CM

noncomputable section

/-! Rationally scaled integral lattices and their duals have reciprocal
volumes for the constructed finite Haar measure. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem scale_preimage_integral (q : ℚ) (hq : q ≠ 0) :
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q ⁻¹' (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q⁻¹ (inv_ne_zero hq) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff, inv_inv]

omit [Fintype I] in
theorem scale_preimage_lattice (q : ℚ) (hq : q ≠ 0) :
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q ⁻¹' (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff,
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_mul, inv_mul_cancel₀ hq, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_one]

theorem reciprocal_volumes (q : ℚ) (hq : q ≠ 0) :
    (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) *
      (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q⁻¹ (inv_ne_zero hq) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 := by
  let μ := Constructed.FiniteMeasure.CM.measure I
  let ν := μ.map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q)
  let : ν.IsAddHaarMeasure :=
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleEquiv q hq).isAddHaarMeasure_map μ
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q⁻¹)
  let c := Measure.addHaarScalarFactor ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hi : ν.real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      μ.real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q⁻¹ (inv_ne_zero hq) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    change (μ.map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))).toReal = _
    rw [Measure.map_apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q).measurable
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.measurableSet, scale_preimage_integral q hq]
    rfl
  have hl : ν.real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 := by
    change (μ.map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))).toReal = _
    rw [Measure.map_apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q).measurable
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_measurableSet q hq), scale_preimage_lattice q hq]
    exact Constructed.FiniteMeasure.CM.integral_real_volume I
  rw [hν, measureReal_nnreal_smul_apply, Constructed.FiniteMeasure.CM.integral_real_volume I, mul_one] at hi
  rw [hν, measureReal_nnreal_smul_apply] at hl
  rw [← hi, mul_comm]
  exact hl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeVolumes.CM
