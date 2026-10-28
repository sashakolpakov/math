import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareClasses
import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses
import OAI.RepresentationTheory.Weil.Local.CompactGroupIndex

/-! # Quadratic Local Square Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalSquareComparison

noncomputable section

/-! The small norm-one and principal-unit square quotients have the same
cardinality for every nonsquare quadratic coefficient. -/

open Set _root_.Metric
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations.Small
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareClasses OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations

variable {k : Type*} [NormedField k] [IsUltrametricDist k] [CharZero k]

def principalNormSquareQuotientEquiv
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (hP : (Weil.Local.SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r))
    (hT : QuadraticNormOperations.normSquareCoordinate d '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r)) :
    (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1 ⧸
      Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)) ≃
    (QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr ⧸
      Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr)) := by
  let e := (Weil.Local.PrincipalSquareClasses.Construction.principalUnitChart (k := k) r hr hr1).symm.trans (QuadraticNormOperations.Small.normSmallChart d hns r hr hr1 hdr)
  have he (a : Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1) :
      QuadraticNormChart.normCoordinate d (e a).val = a.val.val - 1 := by
    change QuadraticNormChart.normCoordinate d (QuadraticNormChart.normChart d hns (a.val.val - 1)) = a.val.val - 1
    exact QuadraticNormChart.normCoordinate_chart d hns _
  refine Quotient.congr e fun a b => ?_
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
    Weil.Local.PrincipalSquareClasses.Construction.principalUnit_mem_squares_iff r hr hr1 hP,
    QuadraticNormSquareClasses.normSmall_mem_squares_iff d hns r hr hr1 hdr hT,
    Weil.Local.PrincipalSquareClasses.Construction.principalUnit_inverse_mul_norm, QuadraticNormSquareClasses.normSmall_inverse_mul_norm, he, he]

theorem principalNorm_square_index_eq
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (hP : (Weil.Local.SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r))
    (hT : QuadraticNormOperations.normSquareCoordinate d '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r)) :
    (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)).index =
      (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr)).index :=
  Nat.card_congr (principalNormSquareQuotientEquiv d hns r hr hr1 hdr hP hT)

theorem exists_principalNorm_square_index_eq
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] [IsUltrametricDist k]
    (d : k) (hns : ¬ IsSquare d) :
    ∃ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1), r ≤ ‖(2 : k)‖ ∧
      (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1)).index =
        (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr)).index := by
  obtain ⟨r, hr, hr1, hr2, hdr, hP, hT⟩ :=
    QuadraticSquareBall.exists_common_square_ball_radius d
  exact ⟨r, hr, hr1, hdr, hr2, principalNorm_square_index_eq d hns r hr hr1 hdr hP hT⟩

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalSquareComparison
