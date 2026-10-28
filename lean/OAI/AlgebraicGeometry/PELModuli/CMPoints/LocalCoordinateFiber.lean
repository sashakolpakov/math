import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalHolomorphicFiber
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateRealization

/-! # Local Coordinate Fiber -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalCoordinateFiber

noncomputable section

/-! The local holomorphic comparison produces the three specified
coordinate CM types on the actual fiber, retaining the realization. -/

open Set _root_.Module
open scoped Classical

theorem exists_coordinate_CM_fiber_of_local_holomorphic_comparison
    {E F : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (U : Set F) (hU : IsOpen U) (hne : U.Nonempty)
    (hdim : finrank ℂ F = finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (period : F → Geometry.ComplexBall.PrescribedSignsB.BallChart) (hhol : DifferentiableOn ℂ period U)
    (hcountable : ∀ z, {q : F | q ∈ U ∧ period q = z}.Countable)
    (hdomain : ∀ q ∈ U, period q ∈ P.domain)
    (V : U → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E)) (R : ∀ q, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (V q))
    (hperiod : ∀ (q : U) x, x ∈ (V q).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (PeriodCoordinates.cmPeriodCoordinates P hP x)) :
    ∃ q : U, CoordinateRealization.HasCoordinateCMRealization P hP (R q).abelianVariety := by
  obtain ⟨O, hO, hOn, hOU⟩ :=
    CountableHolomorphicImage.exists_open_subset_image_of_countable_fibers hU hne hhol hdim hcountable
  have hOd : O ⊆ P.domain := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hOU hz
    exact hdomain q hq
  obtain ⟨z, b, hzO, hb⟩ := LocalPeriods.exists_CM_period_in_open P hP H hH e he O hO hOd hOn
  obtain ⟨q, hq, hqz⟩ := hOU hzO
  have hc : ∀ x, x ∈ (V ⟨q, hq⟩).holomorphic ↔ x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic := by
    intro x
    rw [hperiod]
    simpa only [hqz] using (hb x).symm
  exact ⟨⟨q, hq⟩, CoordinateRealization.coordinateRealizationOfBasisPeriod P hP b (V ⟨q, hq⟩) (R ⟨q, hq⟩) hc, rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalCoordinateFiber
