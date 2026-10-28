import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates

/-! # Zero Period -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ZeroPeriod

noncomputable section

/-! The zero point of the reference ball has exactly the three
constructed CM summands. This identifies an explicit CM period inside
the prescribed analytic family, before any algebraic moduli comparison. -/

open scoped Classical

theorem mem_zero_line (x : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    x ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)} ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [Geometry.ComplexBall.PrescribedSignsB.lineVector]
  · rintro ⟨h0, h1⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 2, ?_⟩
    ext j
    fin_cases j <;> simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, h0, h1]

theorem diagonal_pairing_zero_line {E : Type} [Field E] [Algebra ℚ E]
    {s : ℕ} (σ : Fin s → E →ₐ[ℚ] ℂ) (b : E) (i : Fin s) (y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) i (Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)) y = σ i b * y 2 := by
  simp [Geometry.ComplexBall.PrescribedSignsB.localB, Geometry.ComplexBall.PrescribedSignsB.lineVector, Fin.sum_univ_succ, Matrix.diagonal]

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem zero_mem_period_domain : (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart) ∈ P.domain := by
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
    (Geometry.ComplexBall.PrescribedSignsB.lineVector 0) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector 0))).re < 0
  rw [diagonal_pairing_zero_line]
  simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ] using hP.2.2.2.1

include hP in
theorem zero_signCondition_iff_prescribed (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    PeriodCoordinates.coordinateSignCondition P u ↔
      Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]))
        P.distinguished P.compactSigns 0 u := by
  unfold PeriodCoordinates.coordinateSignCondition Geometry.ComplexBall.PrescribedSignsB.Prescribed
  apply forall_congr'
  intro i
  by_cases hi : i = P.distinguished
  · simp [hi, PeriodCoordinates.coordinateFirstSign, mem_zero_line, diagonal_pairing_zero_line,
      hP.2.2.1, Fin.forall_fin_succ, and_assoc]
  · cases hd : P.compactSigns i <;>
      simp [hi, hd, PeriodCoordinates.coordinateFirstSign, funext_iff, Fin.forall_fin_succ]

theorem coordinateCMHodge_matches_zero_period (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (PeriodCoordinates.coordinateCMHodge P hP).holomorphic ↔ PeriodCoordinates.cmPeriodCoordinates P hP x ∈ P.periodFamily 0 := by
  rw [PeriodCoordinates.coordinateCMHodge_holomorphic, zero_signCondition_iff_prescribed P hP]
  exact ((hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (zero_mem_period_domain P hP)).1 _).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ZeroPeriod
