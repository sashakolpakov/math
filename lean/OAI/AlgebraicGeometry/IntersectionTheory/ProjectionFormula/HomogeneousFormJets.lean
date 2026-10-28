import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedJetGeneration
import OAI.AlgebraicGeometry.Foundations.Scheme.PolynomialToProjectiveChart

/-! # Homogeneous Form Jets -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousFormJets

noncomputable section

/-! Linear homogeneous forms, normalized by a chart coordinate,
surject onto first-order data whenever the affine coordinates generate it. -/

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable (n : ℕ) (i : Fin (n + 1))

def dehomogenizeAlg : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n →ₐ[ℂ] Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i where
  __ := Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i
  commutes' c := by simp

variable {R : Type} [CommRing R] [Algebra ℂ R]
  (g : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] R) (ε : R →ₐ[ℂ] ℂ)

def form : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] R :=
  (g.comp (dehomogenizeAlg n i)).toLinearMap.comp (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1).subtype

def map : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] ℂ × (AugmentedCotangent.ideal ε).Cotangent :=
  (AugmentedCotangent.jet ε).comp (form n i g)

theorem form_self :
    form n i g ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩ = 1 := by
  change g (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X i)) = 1
  simp

theorem form_other (j : {j : Fin (n + 1) // j ≠ i}) :
    form n i g ⟨MvPolynomial.X j.val, MvPolynomial.isHomogeneous_X ℂ j.val⟩ = g (MvPolynomial.X j) := by
  change g (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X j.val)) = _
  simp [j.property]

theorem surjective_of_span
    (h : Submodule.span ℂ (insert (AugmentedCotangent.jet ε 1)
      (Set.range (fun j => AugmentedCotangent.jet ε (g (MvPolynomial.X j))))) = ⊤) :
    Function.Surjective (map n i g ε) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← h]
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl | ⟨j, rfl⟩
  · refine ⟨⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩, ?_⟩
    change AugmentedCotangent.jet ε (form n i g _) = AugmentedCotangent.jet ε 1
    rw [form_self]
  · refine ⟨⟨MvPolynomial.X j.val, MvPolynomial.isHomogeneous_X ℂ j.val⟩, ?_⟩
    change AugmentedCotangent.jet ε (form n i g _) = _
    rw [form_other]

theorem surjective_of_localization
    {A : Type} [CommRing A] [Algebra ℂ A] [Algebra A R] [IsScalarTower ℂ A R]
    (M : Submonoid A) [IsLocalization M R]
    (f : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] A) (hf : Function.Surjective f) :
    Function.Surjective (map n i ((IsScalarTower.toAlgHom ℂ A R).comp f) ε) := by
  let S := f '' Set.range (MvPolynomial.X : {j : Fin (n + 1) // j ≠ i} → Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)
  have hS : Algebra.adjoin ℂ S = ⊤ := by
    rw [show S = f '' Set.range MvPolynomial.X from rfl, ← AlgHom.map_adjoin,
      MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top f).mpr hf
  apply surjective_of_span
  have h := LocalizedJetGeneration.span ε M S hS
  convert h using 1
  congr 2
  ext v
  simp [S]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousFormJets
