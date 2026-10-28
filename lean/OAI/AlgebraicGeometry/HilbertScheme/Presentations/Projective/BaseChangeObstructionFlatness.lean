import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartObstructionFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedTensorFlatnessEquiv
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ChartObstructionDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCharts

/-! # Base Change Obstruction Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChangeObstructionFlatness.GradedHilbert

noncomputable section

/-! Residue obstructions control actual flatness of base-changed projective
quotients. One finite coefficient algebra handles all their charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct _root_.MvPolynomial

universe u
variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A] {n : ℕ}

theorem projective_baseChange_flat_of_chart_injectivity
    [IsNoetherianRing A] [IsLocalRing A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n)) (m : Ideal B) [m.IsMaximal]
    (hm : m.map (algebraMap B A) ≠ ⊤)
    (hinj : ∀ i, Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A
      (A ⊗[B] ChartObstructionFlatness.GradedHilbert.projectiveCoordinateChart I i) (m.map (algebraMap B A)))) :
    Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))) := by
  apply ChartObstructionFlatness.GradedHilbert.projectiveQuotient_flat_of_chart_idealTensor (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)
    (m.map (algebraMap B A)) hm
  · intro i
    exact ReducedTensorFlatnessEquiv.extendedMaximalIdeal_quotient_flat_of_equiv A (ChartObstructionFlatness.GradedHilbert.projectiveCoordinateChart I i)
      (Affine.ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv (S := A) I i).toLinearEquiv m
  · intro i
    exact IdealTensor.RingExtension.idealTensorMultiplication_injective_of_equiv
      (Affine.ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv (S := A) I i).toLinearEquiv _ (hinj i)

theorem projective_flat_finite_coefficient_criterion [IsNoetherianRing B]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n))
    [Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))]
    (C : Subalgebra B A) [Algebra.FiniteType B C] (m : Ideal B) [m.IsMaximal] :
    ∃ E : Subalgebra B A, C ≤ E ∧ Algebra.FiniteType B E ∧
      ∀ (R : Type u) [CommRing R] [Algebra E R] [Algebra B R] [IsScalarTower B E R]
        [IsNoetherianRing R] [IsLocalRing R],
        m.map (algebraMap B R) ≠ ⊤ →
        Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I))) := by
  let S := fun i : Fin (n + 1) => ChartObstructionFlatness.GradedHilbert.projectiveCoordinateChart I i
  let : ∀ i, IsNoetherianRing (S i) := fun i => ChartObstructionFlatness.GradedHilbert.projectiveCoordinateChart_noetherian I i
  let : ∀ i, Module.Flat A (A ⊗[B] S i) := fun i => by
    have : Module.Flat A (ChartObstructionFlatness.GradedHilbert.projectiveCoordinateChart (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) i) :=
      Presentations.Flat.ProjectiveCharts.GradedHilbert.homogeneousChart_flat_of_projective_flat _ Nat.zero_lt_one
        ((Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).map_mem (isHomogeneous_X A i))
    exact Module.Flat.of_linearEquiv (Affine.ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv (S := A) I i).toLinearEquiv
  obtain ⟨E, hCE, hE, hinj⟩ := Finite.ChartObstructionDescent.finite_coefficient_chart_universal_injectivity S C m
    m.fg_of_isNoetherianRing
  refine ⟨E, hCE, hE, ?_⟩
  intro R _ _ _ _ _ _ hm
  exact projective_baseChange_flat_of_chart_injectivity I m hm (hinj R)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChangeObstructionFlatness.GradedHilbert
