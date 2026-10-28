import OAI.Analysis.PDE.Nonlinear.Segment
import OAI.Analysis.PDE.Nonlinear.MatrixPositive
import OAI.LinearAlgebra.Moore.Concavity
import OAI.Analysis.PDE.Dirichlet.EllipticData

/-! The genuine segment linearization is strictly elliptic between positive Hessians. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

local instance segmentPositiveCoordinateComplete (n : ℕ) : CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℝ (Fin n × Fin 4)))
local instance segmentPositiveEndomorphismComplete (n : ℕ) :
    CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  ContinuousLinearMap.instCompleteSpace

theorem segmentOperator_pairing {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :
    inner ℝ v (segmentOperator A B w) =
      ∫ t in (0 : ℝ)..1, inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A)) w) := by
  let L : (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) w)
  change L (∫ t in (0 : ℝ)..1, OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A))) = ∫ t in (0 : ℝ)..1, L _
  exact (L.intervalIntegral_comp_comm ((continuous_segment_integrand A B).intervalIntegrable 0 1)).symm

theorem segmentOperator_isSymmetric {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (segmentOperator A B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (segmentOperator A B v) w = inner ℝ v (segmentOperator A B w)
  rw [real_inner_comm, segmentOperator_pairing, segmentOperator_pairing]
  apply intervalIntegral.integral_congr
  intro t _
  have hs := OAI.Analysis.PDE.Dirichlet.detRealOperator_isSymmetric (A + t • (B - A)) v w
  change inner ℝ (OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A)) v) w =
    inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A)) w) at hs
  simpa only [real_inner_comm (OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A)) v) w] using hs

theorem segment_complexify_posDef {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (OAI.LinearAlgebra.Moore.complexify (A + t • (B - A))).PosDef := by
  have hh := OAI.LinearAlgebra.Moore.convex_complexify_posDef n hA hB (sub_nonneg.mpr ht.2) ht.1
    (show (1 - t) + t = 1 by ring)
  have he : (1 - t) • A + t • B = A + t • (B - A) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rwa [he] at hh

theorem segmentOperator_quadratic_pos {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosDef)
    (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hv : v ≠ 0) : 0 < inner ℝ v (segmentOperator A B v) := by
  rw [segmentOperator_pairing]
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A)) v) := by
    have hp := segment_complexify_posDef A B hA hB ht
    rw [OAI.Analysis.PDE.Dirichlet.detRealOperator_symbol_eq_log _ hp]
    exact mul_pos (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef _ hp) (OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol_pos _ hp v hv)
  apply intervalIntegral.integral_pos zero_lt_one
  · exact ((continuous_const.inner ((continuous_segment_integrand A B).clm_apply continuous_const))).continuousOn
  · intro t ht
    exact (hpos t ⟨ht.1.le, ht.2⟩).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, hpos 0 ⟨le_rfl, zero_le_one⟩⟩

theorem segmentOperator_coordinate_posDef {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosDef) :
    (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (segmentOperator A B)).PosDef := by
  apply operatorCoordinateMatrix_posDef _ (segmentOperator_isSymmetric A B)
  intro v hv
  rw [real_inner_comm]
  exact segmentOperator_quadratic_pos A B hA hB v hv

end OAI.Analysis.PDE.Nonlinear
