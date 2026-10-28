import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses
import OAI.RepresentationTheory.Weil.Local.NormSquareClasses
import OAI.RepresentationTheory.Weil.Local.CompactGroupIndex

/-! # Square Comparison -/

namespace OAI.RepresentationTheory.Weil.Local.SquareComparison.Construction

noncomputable section

/-! The field units and norm-one group have identical local square-class quotients. -/

open Set _root_.Metric

variable {k : Type*} [NormedField k] [IsUltrametricDist k] [CharZero k]

def principalNormSquareQuotientEquiv
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : (SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r))
    (hT : (SquareBall.Construction.normOneSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r)) :
    (PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1 ⧸
      QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)) ≃
    (NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1 ⧸ QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1)) := by
  let e := (PrincipalSquareClasses.Construction.principalUnitChart (k := k) r hr hr1).symm.trans (NormSmallSubgroup.Construction.normSmallChart h r hr hr1)
  have he (a : PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1) :
      QuadraticNormAt.Construction.quadraticNormCoordinate (e a).val = a.val.val - 1 := by
    change QuadraticNormAt.Construction.quadraticNormCoordinate (QuadraticNormAt.Construction.quadraticNormChart h (a.val.val - 1)) = a.val.val - 1
    exact QuadraticNormAt.Construction.quadraticNormCoordinate_chart h _
  refine Quotient.congr e fun a b => ?_
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
    PrincipalSquareClasses.Construction.principalUnit_mem_squares_iff r hr hr1 hP, NormSquareClasses.Construction.normSmall_mem_squares_iff h r hr hr1 hT,
    PrincipalSquareClasses.Construction.principalUnit_inverse_mul_norm, NormSquareClasses.Construction.normSmall_inverse_mul_norm, he, he]

theorem principalNorm_square_index_eq
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : (SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r))
    (hT : (SquareBall.Construction.normOneSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r)) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)).index =
      (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1)).index :=
  Nat.card_congr (principalNormSquareQuotientEquiv h r hr hr1 hP hT)

theorem exists_principalNorm_square_index_eq
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] [IsUltrametricDist k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) :
    ∃ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1), r ≤ ‖(2 : k)‖ ∧
      (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)).index =
        (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1)).index := by
  obtain ⟨r, hr, hrb, hi⟩ := SquareBall.Construction.exists_common_square_ball_radius (k := k)
  have hr1 := hrb.trans (min_le_left _ _)
  exact ⟨r, hr, hr1, hrb.trans (min_le_right _ _),
    principalNorm_square_index_eq h r hr hr1 (hi r hr le_rfl).1 (hi r hr le_rfl).2⟩

end

end OAI.RepresentationTheory.Weil.Local.SquareComparison.Construction
