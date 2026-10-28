import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RenamePolynomialExtension
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart

/-! # Dehomogenization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Dehomogenization

noncomputable section

/-! On normalized projective charts an injective homogeneous
coordinate renaming is the corresponding affine coordinate renaming. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j) (i : Fin (m + 1))

def omitted : {a : Fin (m + 1) // a ≠ i} → {b : Fin (n + 1) // b ≠ j i} :=
  fun a => ⟨j a.val, fun h => a.property (hj h)⟩

theorem omitted_injective : Function.Injective (omitted j hj i) := by
  intro a b hab
  apply Subtype.ext
  exact hj (congrArg Subtype.val hab)

theorem dehomogenize_rename :
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := ℂ) (j i)).comp (MvPolynomial.rename j).toRingHom =
      (MvPolynomial.rename (omitted j hj i)).toRingHom.comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := ℂ) i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro a
    by_cases ha : a = i
    · subst a
      simp
    · have hja : j a ≠ j i := fun h => ha (hj h)
      change Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := ℂ) (j i) (MvPolynomial.rename j (MvPolynomial.X a)) =
        MvPolynomial.rename (omitted j hj i) (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := ℂ) i (MvPolynomial.X a))
      rw [MvPolynomial.rename_X, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne (j i) (j a) hja,
        Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne i a ha, MvPolynomial.rename_X]
      rfl

theorem chart_extension :
    ∃ (ι : Type) (_ : Finite ι)
      (e : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n (j i) ≃ₐ[ℂ] MvPolynomial ι (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i)),
      ∀ p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i,
        e (MvPolynomial.rename (omitted j hj i) p) = MvPolynomial.C p := by
  refine ⟨RenamePolynomialExtension.complement (omitted j hj i),
    inferInstanceAs (Finite {a : {b : Fin (n + 1) // b ≠ j i} // a ∉ Set.range (omitted j hj i)}),
    RenamePolynomialExtension.equivalence (omitted j hj i) (omitted_injective j hj i) ℂ, ?_⟩
  exact RenamePolynomialExtension.equivalence_rename (omitted j hj i) (omitted_injective j hj i) ℂ

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Dehomogenization
