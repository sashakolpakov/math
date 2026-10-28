import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization

/-! # Local Holomorphic Fiber -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalHolomorphicFiber

noncomputable section

/-! A local holomorphic coefficient-period comparison with countable
fibers suffices to produce an actual CM fiber. The period map only needs
to be defined on a nonempty open patch, and no global anisotropy is used. -/

open Set _root_.Module
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem exists_CM_fiber_of_local_holomorphic_period_comparison
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
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
    (V : U → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E))
    (R : ∀ q, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (V q))
    (hperiod : ∀ (q : U) x, x ∈ (V q).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (PeriodCoordinates.cmPeriodCoordinates P hP x)) :
    ∃ q : U, (R q).abelianVariety.HasCMH1 := by
  obtain ⟨O, hO, hOn, hOU⟩ :=
    CountableHolomorphicImage.exists_open_subset_image_of_countable_fibers hU hne hhol hdim hcountable
  have hOd : O ⊆ P.domain := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hOU hz
    exact hdomain q hq
  obtain ⟨z, b, hzO, hb⟩ := LocalPeriods.exists_CM_period_in_open P hP H hH e he O hO hOd hOn
  obtain ⟨q, hq, hqz⟩ := hOU hzO
  refine ⟨⟨q, hq⟩, PeriodRealization.realization_hasCMH1_of_basis_period P hP b (V ⟨q, hq⟩) (R ⟨q, hq⟩) ?_⟩
  intro x
  rw [hperiod]
  simpa only [hqz] using (hb x).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalHolomorphicFiber
