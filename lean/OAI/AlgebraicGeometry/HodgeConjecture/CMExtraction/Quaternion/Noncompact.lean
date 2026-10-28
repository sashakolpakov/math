import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup
import OAI.NumberTheory.Quaternion.Arithmetic.SplitGroup
import Mathlib.Topology.Algebra.Group.Basic

/-! # Noncompact -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Noncompact

noncomputable section

/-! A quaternion norm-one group split at a noncompact topological
field has a continuous surjection onto that field, so its local matrix
point group is noncompact. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {F K : Type} [Field F] [Field K] [CharZero K]
  [TopologicalSpace K] [IsTopologicalRing K]
  (a b : F) (ρ : F →+* K) (x y : K)

def splitQuaternionEntry (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) : K :=
  let M := NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b) ρ g
  ρ a * M 1 0 - ρ a * y * M 2 0 - ρ a * x * M 3 0

omit [CharZero K] in
theorem splitQuaternionEntry_continuous : Continuous (splitQuaternionEntry a b ρ x y) := by
  have hc : Continuous (fun g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ =>
      NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b) ρ g) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((continuous_const.mul ((continuous_apply 0).comp ((continuous_apply 1).comp hc))).sub
    (continuous_const.mul ((continuous_apply 0).comp ((continuous_apply 2).comp hc)))).sub
      (continuous_const.mul ((continuous_apply 0).comp ((continuous_apply 3).comp hc)))

omit [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] in
theorem splitQuaternionEntry_normOne (h : x ^ 2 - ρ a * y ^ 2 = ρ b)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm (ρ a) (ρ b)).ker) :
    splitQuaternionEntry a b ρ x y (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a b ρ q) =
      NumberTheory.Quaternion.Arithmetic.SplitMatrices.quaternionSplittingMap (ρ a) (ρ b) x y h q.val.val 0 1 := by
  simp [splitQuaternionEntry, NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv_matrix,
    NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet.quaternionRegularMatrix_apply, NumberTheory.Quaternion.Arithmetic.SplitMatrices.quaternionSplittingMap_apply]
  ring

omit [TopologicalSpace K] [IsTopologicalRing K] in
theorem splitQuaternionEntry_surjective (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - ρ a * y ^ 2 = ρ b) : Function.Surjective (splitQuaternionEntry a b ρ x y) := by
  intro t
  obtain ⟨q, hq⟩ := (NumberTheory.Quaternion.Arithmetic.SplitGroup.quaternionNormOneSpecialLinearEquiv (ρ a) (ρ b) x y
    ((map_ne_zero ρ).mpr ha) ((map_ne_zero ρ).mpr hb) h).surjective
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)
  refine ⟨NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a b ρ q, ?_⟩
  rw [splitQuaternionEntry_normOne a b ρ x y h]
  have he := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => M 0 1) hq
  have he' : NumberTheory.Quaternion.Arithmetic.SplitMatrices.quaternionSplittingMap (ρ a) (ρ b) x y h q.val.val 0 1 =
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) 0 1 := he
  simpa [Matrix.SpecialLinearGroup.transvection_coe] using he'

theorem quaternionPoints_noncompact_of_split [NoncompactSpace K]
    (ha : a ≠ 0) (hb : b ≠ 0) (h : x ^ 2 - ρ a * y ^ 2 = ρ b) :
    ¬ CompactSpace ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) := by
  intro hc
  let := hc
  let : CompactSpace K := (splitQuaternionEntry_surjective a b ρ x y ha hb h).compactSpace
    (splitQuaternionEntry_continuous a b ρ x y)
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace K)) inferInstance

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Noncompact
