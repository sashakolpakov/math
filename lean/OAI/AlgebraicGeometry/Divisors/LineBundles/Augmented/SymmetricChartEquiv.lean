import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne

/-! # Symmetric Chart Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv.BundleCycles

noncomputable section

/-! The distinguished chart of the actual augmented symmetric Proj is
canonically the affine symmetric algebra of the module. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricChart_homogeneous (n : ℕ) (a : SymmetricAlgebra R (R × M))
    (ha : a ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) n) :
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M a) =
      Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a
        (by simpa only [smul_eq_mul, mul_one] using ha) := by
  change a ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ n at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Graded.ChartAddition.BundleCycles.gradedAway_mk_algebraMap (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M)
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)).symm
  | add a b n ha hb iha ihb =>
    rw [map_add, map_add, iha, ihb]
    exact (Graded.ChartAddition.BundleCycles.gradedAway_mk_add (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a b _ _).symm
  | mem_mul m hm n a ha ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, map_mul, ih]
    have hv : SymmetricAlgebra.ι R (R × M) v ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
      change SymmetricAlgebra.ι R (R × M) v ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ (1 • 1)
      simpa only [one_smul, pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) v
    rw [SymmetricChartDegreeOne.BundleCycles.augmentedSymmetricChart_degreeOne R M v hv]
    have h := Graded.ChartMultiplication.BundleCycles.gradedAway_mk_mul (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 n (SymmetricAlgebra.ι R (R × M) v) a hv
      (by simpa only [smul_eq_mul, mul_one, Symmetric.Grading.BundleCycles.symmetricGrading] using ha)
    exact h.trans (by
      apply HomogeneousLocalization.val_injective
      rw [Away.val_mk, Away.val_mk]
      exact congrArg (Localization.mk (SymmetricAlgebra.ι R (R × M) v * a))
        (Subtype.ext (congrArg (fun k => SymmetricChart.BundleCycles.augmentedSymmetricVariable R M ^ k) (Nat.add_comm 1 n))))

theorem augmentedSymmetricDehomogenization_rightInverse :
    Function.RightInverse (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) z
  rw [SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk]
  exact augmentedSymmetricChart_homogeneous R M n a
    (by simpa only [smul_eq_mul, mul_one] using ha)

def augmentedSymmetricChartEquiv : SymmetricChart.BundleCycles.augmentedSymmetricChart R M ≃ₐ[R] SymmetricAlgebra R M :=
  { SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenizationAlg R M with
    invFun := SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M
    left_inv := augmentedSymmetricDehomogenization_rightInverse R M
    right_inv := SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenization_leftInverse R M }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv.BundleCycles
