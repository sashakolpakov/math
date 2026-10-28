import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming

/-! # Chart Polynomial Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartPolynomialExtension

noncomputable section

/-! The genuine homogeneous localization map is a polynomial
extension in exactly the complementary affine coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Dehomogenization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j) (i : Fin (m + 1))

def extra := RenamePolynomialExtension.complement (Dehomogenization.omitted j hj i)

instance finite_extra : Finite (extra j hj i) :=
  inferInstanceAs (Finite {a : {b : Fin (n + 1) // b ≠ j i} // a ∉ Set.range (Dehomogenization.omitted j hj i)})

theorem chart_equiv_map (p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) :
    Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n (j i) (HomogeneousChartRenaming.chartMap j i p) =
      MvPolynomial.rename (Dehomogenization.omitted j hj i) (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i p) := by
  obtain ⟨q, rfl⟩ := (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i).symm.surjective p
  rw [RingEquiv.apply_symm_apply]
  have he := RingHom.congr_fun (HomogeneousChartRenaming.polynomial_comp j i hj) q
  exact (congrArg (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n (j i)) he).trans
    ((Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n (j i)).apply_symm_apply _)

def equivalence : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i) ≃+* MvPolynomial (extra j hj i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) :=
  (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n (j i)).trans
    ((RenamePolynomialExtension.equivalence (Dehomogenization.omitted j hj i) (Dehomogenization.omitted_injective j hj i) ℂ).toRingEquiv.trans
      (MvPolynomial.mapEquiv (extra j hj i) (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i).symm))

theorem commutes (p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) :
    equivalence j hj i (HomogeneousChartRenaming.chartMap j i p) = MvPolynomial.C p := by
  change MvPolynomial.map (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i).symm.toRingHom
    (RenamePolynomialExtension.equivalence (Dehomogenization.omitted j hj i) (Dehomogenization.omitted_injective j hj i) ℂ
      (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n (j i) (HomogeneousChartRenaming.chartMap j i p))) = _
  rw [chart_equiv_map j hj i p, RenamePolynomialExtension.equivalence_rename, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C ((Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i).symm_apply_apply p)

def algebraEquiv :
    letI : Algebra (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i)) := (HomogeneousChartRenaming.chartMap j i).toAlgebra
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i) ≃ₐ[Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i] MvPolynomial (extra j hj i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) :=
  letI : Algebra (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i)) := (HomogeneousChartRenaming.chartMap j i).toAlgebra
  { equivalence j hj i with commutes' := commutes j hj i }

theorem card_extra : Nat.card (extra j hj i) + m = n := by
  let : Finite (RenamePolynomialExtension.complement (Dehomogenization.omitted j hj i)) := finite_extra j hj i
  let := Fintype.ofFinite (RenamePolynomialExtension.complement (Dehomogenization.omitted j hj i))
  have he := Fintype.card_congr (RenamePolynomialExtension.indices (Dehomogenization.omitted j hj i) (Dehomogenization.omitted_injective j hj i))
  rw [Fintype.card_sum, Foundations.Scheme.ProjectiveChart.projectiveChartCoordinate_card, Foundations.Scheme.ProjectiveChart.projectiveChartCoordinate_card] at he
  change Nat.card (RenamePolynomialExtension.complement (Dehomogenization.omitted j hj i)) + m = n
  simpa only [Nat.card_eq_fintype_card] using he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartPolynomialExtension
