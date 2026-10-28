import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Nat Volume -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume.CM

noncomputable section

/-! Exact volumes of the actual normalized integral finite lattices,
without a Weil-data input. -/

open scoped Classical ENNReal
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
variable (I : Type*) [Fintype I]

theorem finiteLattice_nat_volume (n : ℕ) (hn : 0 < n) :
    (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (n : ℚ) (by exact_mod_cast hn.ne') : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      ((n : ℝ) ^ Fintype.card I)⁻¹ := by
  let : NeZero n := ⟨hn.ne'⟩
  let L := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (n : ℚ) (by exact_mod_cast hn.ne')
  have hcoset (r : I → ZMod n) : (Constructed.FiniteMeasure.CM.measure I) {x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | x - RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r ∈ L} =
      (Constructed.FiniteMeasure.CM.measure I) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    simpa only [sub_eq_add_neg, Set.preimage, SetLike.mem_coe] using
      measure_preimage_add_right (Constructed.FiniteMeasure.CM.measure I) (-RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
  have hmeasure : (Constructed.FiniteMeasure.CM.measure I) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      (n : ℝ≥0∞) ^ Fintype.card I * (Constructed.FiniteMeasure.CM.measure I) (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_residue_partition n hn]
    rw [measure_iUnion (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residue_cosets_disjoint n hn)
      (fun r => (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_measurableSet (n : ℚ) (by exact_mod_cast hn.ne')).preimage
        (measurable_id.sub measurable_const))]
    change (∑' r : I → ZMod n, (Constructed.FiniteMeasure.CM.measure I) {x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | x - RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.residuePoint r ∈ L}) = _
    simp only [hcoset, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  have hreal := congrArg ENNReal.toReal hmeasure
  change (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = _ at hreal
  rw [Constructed.FiniteMeasure.CM.integral_real_volume I] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  have hnreal : (n : ℝ) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  apply (mul_left_cancel₀ hnreal)
  rw [mul_inv_cancel₀ hnreal]
  exact hreal.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume.CM
