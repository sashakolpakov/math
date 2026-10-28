import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Noncompact
import Mathlib.Analysis.Real.Sqrt

/-! # Real Split -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.RealSplit

noncomputable section

/-! A positive second quaternion coefficient at a real completion
supplies the noncompact factor required by strong approximation. -/

open scoped Classical

variable {F K : Type} [Field F] [Field K] [CharZero K]
  [TopologicalSpace K] [IsTopologicalRing K]

theorem quaternionPoints_noncompact_of_positive_real
    (a b : F) (ρ : F →+* K) (e : K ≃+* ℝ) (he : Continuous e)
    (ha : a ≠ 0) (hb : b ≠ 0) (hpos : 0 < e (ρ b)) :
    ¬ CompactSpace ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) := by
  have hK : ¬ CompactSpace K := by
    intro h
    let := h
    have hc : CompactSpace ℝ := e.surjective.compactSpace he
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) hc
  let : NoncompactSpace K := not_compactSpace_iff.mp hK
  have hs : (e.symm (Real.sqrt (e (ρ b)))) ^ 2 - ρ a * (0 : K) ^ 2 = ρ b := by
    apply e.injective
    simp [Real.sq_sqrt hpos.le]
  exact Noncompact.quaternionPoints_noncompact_of_split a b ρ _ 0 ha hb hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.RealSplit
