import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodOnBall
import OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport

/-! # Period Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization

noncomputable section

/-! A genuine universal period comparison transfers the constructed
CM period to the actual abelian fiber. The comparison is displayed as
a hypothesis of this bridge; it is not supplied by the base-space
uniformization or postulated as a CM-point existence statement. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem realization_hasCMH1_of_basis_period
    (b : Basis (Fin 3) E (Fin 3 → E))
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E)) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (hH : ∀ x, x ∈ H.holomorphic ↔ x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic) :
    R.abelianVariety.HasCMH1 := by
  have hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (BasisHodge.basisCMHodge P hP b) H (LinearMap.id) := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using (hH x).mpr hx
  have hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap H (BasisHodge.basisCMHodge P hP b) (LinearMap.id) := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using (hH x).mp hx
  exact BasisHodge.basisCMRealization_hasCMH1 P hP b
    (TypeTransport.hodgeRealizationAlongEquiv (LinearEquiv.refl ℚ _) hf hi R)

theorem exists_CM_fiber_of_universal_period_comparison
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (V : P.Domain → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E))
    (R : ∀ z, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (V z))
    (hperiod : ∀ z x, x ∈ (V z).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (PeriodCoordinates.cmPeriodCoordinates P hP x)) :
    ∃ z : P.Domain, (R z).abelianVariety.HasCMH1 := by
  obtain ⟨z, b, hb⟩ := PeriodOnBall.exists_CM_period_on_ball P hP H hH hani e he
  exact ⟨z, realization_hasCMH1_of_basis_period P hP b (V z) (R z)
    (fun x => (hperiod z x).trans (hb x).symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization
