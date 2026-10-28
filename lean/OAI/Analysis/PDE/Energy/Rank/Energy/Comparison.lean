import OAI.Analysis.PDE.Energy.Rank.Energy.Formula
import OAI.Analysis.PDE.Energy.Rank.Energy.Properties
import OAI.Analysis.PDE.Energy.Rank.Energy.RankSign
import OAI.LinearAlgebra.MixedDiscriminant.GreenNonnegative

/-! The rank-dependent energy comparison, with the mixed positivity, rank
truncation, sign, and integration by parts all derived from the actual data. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.LinearAlgebra.MixedDiscriminant
open scoped MatrixOrder ComplexOrder

/-- General background-rank energy comparison on a bounded domain. -/
theorem rank_energy_comparison {n s r : ℕ} (hn : 2 ≤ n) (hr : r < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hD : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosDef)
    (hback : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hrank : ∀ x ∈ S, OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))
    {Λ : ℝ} (hΛ : 0 < Λ) :
    let X := determinantMass e S (fun y => B y+u y) u / Λ
    let E := (determinantMass e S (fun y => B y+u y) u + determinantSegmentEnergy e S B u) / Λ
    ((n : ℝ)-r)/((n : ℝ)+1)*X ≤ E ∧ E ≤ (n : ℝ)/((n : ℝ)+1)*X := by
  have hneg := correction_nonpos_of_background_rank hr e hS hb
    (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) hz hD hback hrank
  have hD' : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef :=
    fun x hx => (hD x hx).posSemidef
  apply rank_energy_comparison_of_mixed_moments hr e hS.measurableSet hb hB hu
  · intro j hj
    exact mixedHessianMass_nonneg e hS.measurableSet
      (fun x hx => hneg x (subset_closure hx)) hback hD' j
  · exact fun j hj => OAI.LinearAlgebra.MixedDiscriminant.mixedHessianMass_succ_le_bounded (by omega) e hS hb hnull hB hu hz hD' hback j hj
  · exact fun j hrj hjn => mixedHessianMass_eq_zero_of_rank e hS.measurableSet hback hD' hrank hrj hjn
  · exact hΛ

end OAI.Analysis.PDE.Energy
