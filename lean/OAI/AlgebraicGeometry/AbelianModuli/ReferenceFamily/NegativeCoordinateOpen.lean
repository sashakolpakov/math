import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Negative Coordinate Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeCoordinateOpen

noncomputable section

/-! An open set in the original affine negative-line coordinates pulls
back to an actual open set of vectors with nonzero last coordinate.
The pullback contains every nonzero scalar multiple of each of its points.
-/

open _root_.Topology

theorem negativeLineCoordinate_continuousAt
    (v : Fin 3 → ℂ) (hv : v 2 ≠ 0) : ContinuousAt NegativeLine.negativeLineCoordinate v := by
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun x : Fin 3 → ℂ => x i.castSucc / x 2) v
  exact (continuous_apply i.castSucc).continuousAt.div (continuous_apply 2).continuousAt hv

def negativeCoordinateOpenPreimage
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) : Set (Fin 3 → ℂ) :=
  {v | (e.symm v) 2 ≠ 0 ∧ NegativeLine.negativeLineCoordinate (e.symm v) ∈ U}

theorem negativeCoordinateOpenPreimage_isOpen
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hU : IsOpen U) :
    IsOpen (negativeCoordinateOpenPreimage e U) := by
  have he : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  have hlast : IsOpen {v : Fin 3 → ℂ | (e.symm v) 2 ≠ 0} :=
    (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage ((continuous_apply 2).comp he)
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  have hc : ContinuousAt (fun x => NegativeLine.negativeLineCoordinate (e.symm x)) v :=
    (negativeLineCoordinate_continuousAt (e.symm v) hv.1).comp he.continuousAt
  exact Filter.inter_mem (hlast.mem_nhds hv.1) (hc.preimage_mem_nhds (hU.mem_nhds hv.2))

theorem negativeCoordinateOpenPreimage_smul
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (v : Fin 3 → ℂ) (hv : v ∈ negativeCoordinateOpenPreimage e U)
    (a : ℂ) (ha : a ≠ 0) : a • v ∈ negativeCoordinateOpenPreimage e U := by
  change (e.symm (a • v)) 2 ≠ 0 ∧ NegativeLine.negativeLineCoordinate (e.symm (a • v)) ∈ U
  rw [map_smul]
  constructor
  · change a * (e.symm v) 2 ≠ 0
    exact mul_ne_zero ha hv.1
  · rw [NegativeLine.negativeLineCoordinate_smul a ha]
    exact hv.2

theorem lineActionVia_eq_on_vector_representative
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (v : Fin 3 → ℂ)
    (hv : (e.symm v) 2 ≠ 0) (hz : NegativeLine.negativeLineCoordinate (e.symm v) = z) :
    P.lineActionVia e g z =
      NegativeLine.negativeLineCoordinate (e.symm (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) v)) := by
  have he : e (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = ((e.symm v) 2)⁻¹ • v := by
    rw [← hz, NegativeLine.negativeLineCoordinate_vector (e.symm v) hv, map_smul, e.apply_symm_apply]
  change NegativeLine.negativeLineCoordinate (e.symm
    (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)))) = _
  rw [he, map_smul, map_smul, NegativeLine.negativeLineCoordinate_smul _ (inv_ne_zero hv)]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeCoordinateOpen
