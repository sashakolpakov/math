import OAI.Analysis.PDE.Dirichlet.Moore.RealOperator
import OAI.LinearAlgebra.Moore.Variation

/-! The actual averaged linearization of the Moore determinant. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise ContDiff
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

local instance segmentCoordinateComplete (n : ℕ) : CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℝ (Fin n × Fin 4)))

local instance segmentEndomorphismComplete (n : ℕ) :
    CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  ContinuousLinearMap.instCompleteSpace

def segmentOperator {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 :=
  ∫ t in (0 : ℝ)..1, OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A))

theorem continuous_segment_integrand {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Continuous (fun t : ℝ => OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A))) := by
  have hc : Continuous (fun t : ℝ => (A + t • (B - A) : Fin n → Fin n → Quaternion ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 0).continuous.comp hc

theorem segmentOperator_trace {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hG : G.toLinearMap.IsSymmetric) :
    OAI.Analysis.PDE.Elliptic.traceRight G (segmentOperator A B) =
      ∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDifferential n (A + t • (B - A))
        (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix G)) := by
  let L := (OAI.Analysis.PDE.Elliptic.traceRight G).toContinuousLinearMap
  have hi : IntervalIntegrable (fun t : ℝ => OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A))) volume 0 1 :=
    (continuous_segment_integrand A B).intervalIntegrable 0 1
  change L (∫ t in (0 : ℝ)..1, OAI.Analysis.PDE.Dirichlet.detRealOperator (A + t • (B - A))) = _
  rw [← L.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro t _
  exact OAI.Analysis.PDE.Elliptic.symmetricTraceDual_represents _ _ G hG

theorem segmentOperator_determinant_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hG : G.toLinearMap.IsSymmetric)
    (hH : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix G) = B - A) :
    OAI.Analysis.PDE.Elliptic.traceRight G (segmentOperator A B) = OAI.LinearAlgebra.Moore.mooreDet n B - OAI.LinearAlgebra.Moore.mooreDet n A := by
  rw [segmentOperator_trace A B G hG, hH]
  have h := OAI.LinearAlgebra.Moore.integral_mooreDifferential_affine A (B - A) 0 1
  have he : A + (B - A) = B := by abel
  simpa only [one_smul, zero_smul, add_zero, he] using h

theorem segmentOperator_scaled_determinant_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (c : ℝ)
    (G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hG : G.toLinearMap.IsSymmetric)
    (hH : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix G) = c • (B - A)) :
    OAI.Analysis.PDE.Elliptic.traceRight G (segmentOperator A B) = c * (OAI.LinearAlgebra.Moore.mooreDet n B - OAI.LinearAlgebra.Moore.mooreDet n A) := by
  rw [segmentOperator_trace A B G hG, hH]
  simp_rw [OAI.LinearAlgebra.Moore.mooreDifferential_smul]
  rw [intervalIntegral.integral_const_mul]
  have h := OAI.LinearAlgebra.Moore.integral_mooreDifferential_affine A (B - A) 0 1
  have he : A + (B - A) = B := by abel
  have hi : (∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDifferential n (A + t • (B - A)) (B - A)) =
      OAI.LinearAlgebra.Moore.mooreDet n B - OAI.LinearAlgebra.Moore.mooreDet n A := by
    simpa only [one_smul, zero_smul, add_zero, he] using h
  rw [hi]

end OAI.Analysis.PDE.Nonlinear
