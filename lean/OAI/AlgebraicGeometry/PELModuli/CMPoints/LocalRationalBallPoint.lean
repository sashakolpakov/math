import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalBallPoint

/-! # Local Rational Ball Point -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalRationalBallPoint

noncomputable section

/-! Every nonempty open part of the ball contains a coefficient-field
line, including after a specified complex Hermitian change of coordinates.
This is a density statement inside the actual period domain. -/

open scoped Classical _root_.Topology

theorem normalizedBallChart_continuousAt (w : Geometry.ComplexBall.PrescribedSignsB.Vec) (hw : w 2 ≠ 0) :
    ContinuousAt RationalBallPoint.normalizedBallChart w := by
  apply continuousAt_pi.mpr
  intro i
  exact (continuous_apply i.castSucc).continuousAt.div (continuous_apply 2).continuousAt hw

theorem normalizedBallChart_lineVector (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    RationalBallPoint.normalizedBallChart (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = z := by
  ext i
  fin_cases i <;> simp [RationalBallPoint.normalizedBallChart, Geometry.ComplexBall.PrescribedSignsB.lineVector]

theorem exists_rational_ball_line_in_open
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hU : IsOpen U) (hUd : U ⊆ P.domain) (hUn : U.Nonempty) :
    ∃ (z : P.Domain) (v : Fin 3 → E) (a : ℂ),
      z.val ∈ U ∧ v ≠ 0 ∧ a ≠ 0 ∧
      e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) = a • (fun i => P.μ (v i)) ∧
      (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (fun i => P.μ (v i))
        (fun i => P.μ (v i))).re < 0 := by
  obtain ⟨z₀, hz₀⟩ := hUn
  let w₀ := e (Geometry.ComplexBall.PrescribedSignsB.lineVector z₀)
  let norm : Geometry.ComplexBall.PrescribedSignsB.Vec → Geometry.ComplexBall.PrescribedSignsB.BallChart := fun w => RationalBallPoint.normalizedBallChart (e.symm w)
  have hlast : (e.symm w₀) 2 ≠ 0 := by
    simp [w₀, Geometry.ComplexBall.PrescribedSignsB.lineVector]
  have hnorm : ContinuousAt norm w₀ :=
    (normalizedBallChart_continuousAt (e.symm w₀) hlast).comp
      e.symm.toContinuousLinearEquiv.continuous.continuousAt
  have hz : norm w₀ ∈ U := by
    simpa [norm, w₀, normalizedBallChart_lineVector] using hz₀
  have hneg : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H w₀ w₀).re < 0 := by
    rw [he]
    exact hUd hz₀
  have hc : Continuous (fun w : Geometry.ComplexBall.PrescribedSignsB.Vec => (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H w w).re) := by
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian
    fun_prop
  have hn : {w : Geometry.ComplexBall.PrescribedSignsB.Vec | norm w ∈ U ∧
      (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H w w).re < 0} ∈ 𝓝 w₀ :=
    Filter.inter_mem (hnorm.preimage_mem_nhds (hU.mem_nhds hz))
      ((isOpen_lt hc continuous_const).mem_nhds hneg)
  obtain ⟨V, hV, hVo, hwV⟩ := mem_nhds_iff.mp hn
  have hd : DenseRange (fun v : Fin 3 → E => fun i => P.μ (v i)) :=
    DenseRange.piMap (fun _ => RationalNegativeLine.cmEmbedding_denseRange (P.embeddings P.distinguished))
  obtain ⟨v, hv⟩ := hd.exists_mem_open hVo ⟨w₀, hwV⟩
  obtain ⟨hvU, hvneg⟩ := hV hv
  let w : Geometry.ComplexBall.PrescribedSignsB.Vec := e.symm (fun i => P.μ (v i))
  have hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) w w).re < 0 := by
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hvneg
  have hw2 := RationalBallPoint.negative_vector_last_ne_zero P w hw
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian] at hvneg
  refine ⟨⟨RationalBallPoint.normalizedBallChart w, hUd hvU⟩, v, (w 2)⁻¹, hvU, hv0,
    inv_ne_zero hw2, ?_, hvneg⟩
  rw [RationalBallPoint.lineVector_normalizedBallChart w hw2, map_smul]
  exact congrArg ((w 2)⁻¹ • ·) (e.apply_symm_apply _)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalRationalBallPoint
