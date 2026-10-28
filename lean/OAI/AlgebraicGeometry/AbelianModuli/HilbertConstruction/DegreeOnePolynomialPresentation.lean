import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveGradedProjectiveMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.Algebra.Algebra.Operations

/-! # Degree One Polynomial Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOnePolynomialPresentation

noncomputable section

/-! Degree-one algebra generators give a concrete surjective graded
polynomial map and hence a closed projective embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Pointwise Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] {n : ℕ}
variable (D : Fin (n + 1) → A) (hD : ∀ j, D j ∈ g 1)

include hD in
theorem degreeOnePolynomialEvaluation_mem (d : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map (MvPolynomial.aeval D).toLinearMap ≤ g d := by
  have h₁ : (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1).map
      (MvPolynomial.aeval D).toLinearMap ≤ g 1 := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, ⟨j, rfl⟩, rfl⟩
    change MvPolynomial.aeval D (MvPolynomial.X j) ∈ g 1
    rw [MvPolynomial.aeval_X]
    exact hD j
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow]
  induction d with
  | zero => exact Submodule.one_le.mpr (SetLike.GradedOne.one_mem : (1 : A) ∈ g 0)
  | succ d ih =>
    rw [pow_succ]
    apply le_trans (mul_le_mul' ih h₁)
    exact Submodule.mul_le.mpr (fun _ hx _ hy => SetLike.mul_mem_graded hx hy)

def degreeOnePolynomialPresentation : Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ g where
  __ := (MvPolynomial.aeval D).toRingHom
  map_mem hp := degreeOnePolynomialEvaluation_mem g D hD _ ⟨_, hp, rfl⟩

theorem degreeOnePolynomialPresentation_surjective (hgen : Algebra.adjoin R (Set.range D) = ⊤) :
    Function.Surjective (degreeOnePolynomialPresentation g D hD) := by
  intro a
  have ha : a ∈ (MvPolynomial.aeval (R := R) D).range := by
    rw [MvPolynomial.aeval_range, hgen]
    trivial
  exact ha

def degreeOneProjectiveEmbedding (hgen : Algebra.adjoin R (Set.range D) = ⊤) :
    Proj g ⟶ Proj (Projective.ProjectivePresentations.coordinateGrading R n) :=
  Proj.map (degreeOnePolynomialPresentation g D hD)
    (SurjectiveGradedProjectiveMap.surjectiveGradedMap_irrelevant _ _ _ (degreeOnePolynomialPresentation_surjective g D hD hgen))

theorem degreeOneProjectiveEmbedding_closed (hgen : Algebra.adjoin R (Set.range D) = ⊤) :
    IsClosedImmersion (degreeOneProjectiveEmbedding g D hD hgen) :=
  SurjectiveGradedProjectiveMap.surjectiveGradedMap_closed _ _ _ (degreeOnePolynomialPresentation_surjective g D hD hgen)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOnePolynomialPresentation
