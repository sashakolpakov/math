import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalBallPoint

/-! # Period On Ball -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodOnBall

noncomputable section

/-! Every supplied rational Hermitian ball contains a constructed
period whose rational Hodge structure has an explicit CM decomposition. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

omit [NumberField E] [NumberField.IsCMField E] in
theorem componentPrescribed_smul (H : Matrix (Fin 3) (Fin 3) E)
    (a : ℂ) (ha : a ≠ 0) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    ClosedCoefficientPeriods.componentPrescribed P H (a • v) u ↔ ClosedCoefficientPeriods.componentPrescribed P H v u := by
  have hs : Submodule.span ℂ {a • v} = Submodule.span ℂ {v} := by
    simpa only [Set.smul_set_singleton] using
      Submodule.span_smul_eq_of_isUnit ({v} : Set Geometry.ComplexBall.PrescribedSignsB.Vec) a (isUnit_iff_ne_zero.mpr ha)
  unfold ClosedCoefficientPeriods.componentPrescribed
  apply forall_congr'
  intro i
  by_cases hi : i = P.distinguished
  · simp only [hi, ite_true, hs]
    rw [← Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, mul_eq_zero, or_iff_right ha]
  · simp [hi]

theorem exists_CM_period_on_ball (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) :
    ∃ (z : P.Domain) (b : Basis (Fin 3) E (Fin 3 → E)),
      ∀ x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E),
        x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic ↔
          ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  obtain ⟨z, b, a, ha, heq, hb⟩ := RationalBallPoint.exists_rational_ball_orthogonal_basis P hP H hH hani e he
  let b' := b.reindex (Equiv.swap 0 2)
  have hlast : b' 2 = b 0 := by
    simp only [b', Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  have ho : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b' i) (b' j) = 0) := by
    intro i j hij
    simp only [b', Basis.reindex_apply]
    exact hb ((Equiv.swap (0 : Fin 3) 2).symm.injective.ne hij)
  refine ⟨z, b', fun x => ?_⟩
  rw [heq, componentPrescribed_smul P H a ha,
    ClosedCoefficientPeriods.basisCMHodge_component_period P hP H hani b' ho, hlast]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodOnBall
