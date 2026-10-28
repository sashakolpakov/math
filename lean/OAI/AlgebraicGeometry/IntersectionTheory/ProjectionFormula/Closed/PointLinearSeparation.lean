import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale

/-! # Point Linear Separation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointLinearSeparation

noncomputable section

/-! Distinct closed projective points are separated by degree-one forms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem vectors {n : ℕ} (v w : Fin (n + 1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv (IsLocalRing.closedPoint ℂ) ≠
      Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint w hw (IsLocalRing.closedPoint ℂ)) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1, MvPolynomial.eval v a.val = 0 ∧
      MvPolynomial.eval w a.val ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hj : ∃ j, v i * w j - v j * w i ≠ 0 := by
    by_contra h
    push Not at h
    have hwi : w i ≠ 0 := by
      intro hwi
      apply hw
      funext j
      have he := h j
      simp only [hwi, mul_zero, sub_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hi
    have he : w = (w i / v i) • v := by
      funext j
      change w j = w i / v i * v j
      rw [div_mul_eq_mul_div, eq_div_iff hi]
      exact (mul_comm _ _).trans ((sub_eq_zero.mp (h j)).trans (mul_comm _ _))
    have hc : w i / v i ≠ 0 := div_ne_zero hwi hi
    have hn : (w i / v i) • v ≠ 0 := he ▸ hw
    apply hne
    simpa only [← he] using (Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_smul_apply v hv _ hc hn
      (IsLocalRing.closedPoint ℂ)).symm
  obtain ⟨j, hj⟩ := hj
  refine ⟨⟨MvPolynomial.C (v i) * MvPolynomial.X j -
    MvPolynomial.C (v j) * MvPolynomial.X i,
    (MvPolynomial.isHomogeneous_C_mul_X (v i) j).sub
      (MvPolynomial.isHomogeneous_C_mul_X (v j) i)⟩, ?_, ?_⟩
  · simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  · simpa only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] using hj

theorem points (n : ℕ) (x y : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hx : IsClosed ({x} : Set _))
    (hy : IsClosed ({y} : Set _)) (hne : x ≠ y) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1,
      a.val ∈ x.asHomogeneousIdeal ∧ a.val ∉ y.asHomogeneousIdeal := by
  obtain ⟨v, hv, hev⟩ := Foundations.Scheme.ProjectivePointSurjective.projectiveVectorPoint_surjective
    (pointOfClosedPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x hx)
    (pointOfClosedPoint_comp (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x hx)
  obtain ⟨w, hw, hew⟩ := Foundations.Scheme.ProjectivePointSurjective.projectiveVectorPoint_surjective
    (pointOfClosedPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) y hy)
    (pointOfClosedPoint_comp (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) y hy)
  have hvx : Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv (IsLocalRing.closedPoint ℂ) = x := by
    rw [hev, pointOfClosedPoint_apply]
  have hwy : Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint w hw (IsLocalRing.closedPoint ℂ) = y := by
    rw [hew, pointOfClosedPoint_apply]
  obtain ⟨a, ha, hb⟩ := vectors v w hv hw (by simpa only [hvx, hwy] using hne)
  refine ⟨a, ?_, ?_⟩
  · rw [← hvx, Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff v hv a.val 1 a.property]
    exact ha
  · rw [← hwy, Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff w hw a.val 1 a.property]
    exact hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointLinearSeparation
