import OAI.RepresentationTheory.Theta.Geometric.AnalyticCountableSelection
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodEq
import OAI.RepresentationTheory.Theta.Geometric.Period.DomainTopology

/-! # Rational Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A rational SU transformation trivial on the original ball is scalar,
and its scalar has cube one because the original determinant is one. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rational_period_kernel_scalar (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (h : ∀ x : D.domain, D.periodMap g x.val = x.val) :
    g.val.val = Matrix.scalar (Fin 3) (g.val.val 2 2) := by
  let μ := D.pel.reference.μ
  let M := (Matrix.SpecialLinearGroup.map μ g.val).val
  have hm : M = Matrix.scalar (Fin 3) (M 2 2) := by
    apply AnalyticCountableSelection.scalar_matrix_of_projective_open M D.domain.isOpen
      (show (D.domain : Set LinearTheta.BallCoordinates).Nonempty from
        ⟨(D.domainOrigin hg).val, (D.domainOrigin hg).property⟩)
    intro z hz i
    have he : Period.Ne.periodRow D.pel.reference.b μ g i.castSucc z /
        Period.Ne.periodRow D.pel.reference.b μ g 2 z = z i :=
      (congrFun (Period.Ne.rationalPeriodPerm_eq_fractional D.pel.reference.b μ g z hz) i).symm.trans
        (congrFun (h ⟨z, hz⟩) i)
    have H := (div_eq_iff (Period.Ne.periodRow_last_ne_zero D.pel.reference.b μ g ⟨z, hz⟩)).mp he
    exact sub_eq_zero.mpr H
  ext i j
  apply μ.injective
  have H := congrFun (congrFun hm i) j
  have hM (k l : Fin 3) : M k l = μ (g.val.val k l) := rfl
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hM] using H
  · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, hM, map_zero] using H

theorem Data.ActiveHeckeThetaData.rational_period_kernel_cube (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (h : ∀ x : D.domain, D.periodMap g x.val = x.val) :
    (g.val.val 2 2) ^ 3 = 1 := by
  have he := g.val.property
  rw [D.rational_period_kernel_scalar hg g h] at he
  simpa only [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using he

end

end OAI.RepresentationTheory.Theta.Geometric
