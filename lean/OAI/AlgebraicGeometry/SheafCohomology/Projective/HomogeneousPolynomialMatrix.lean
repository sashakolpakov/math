import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules

/-! # Homogeneous Polynomial Matrix -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix

noncomputable section

/-! Polynomial matrices of prescribed degrees give homogeneous maps of weighted free modules. -/

open _root_.MvPolynomial DirectSum
universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ]
variable {ι κ : Type w} [Fintype ι]

def homogeneousMatrixColumn (d : ι → ℕ) (e : κ → ℕ)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) (k : κ) :
    ι →₀ MvPolynomial σ R :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i k).val)

theorem homogeneousMatrixColumn_homogeneous (d : ι → ℕ) (e : κ → ℕ)
    (hde : ∀ i k, d i ≤ e k)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) (k : κ) :
    homogeneousMatrixColumn d e a k ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)) (e k : ℤ) := by
  rw [HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading]
  intro i
  change (a i k).val ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R ((e k : ℤ) - (d i : ℤ))
  rw [← Int.natCast_sub (hde i k), HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
  exact (a i k).property

def homogeneousPolynomialMatrixMap (d : ι → ℕ) (e : κ → ℕ)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) :
    (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (ι →₀ MvPolynomial σ R) :=
  Finsupp.linearCombination (MvPolynomial σ R) (homogeneousMatrixColumn d e a)

theorem homogeneousPolynomialMatrixMap_homogeneous (d : ι → ℕ) (e : κ → ℕ)
    (hde : ∀ i k, d i ≤ e k)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) (n : ℤ)
    (x : κ →₀ MvPolynomial σ R) (hx : x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun k => (e k : ℤ)) n) :
    homogeneousPolynomialMatrixMap d e a x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)) n :=
  HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFree_linearCombination_homogeneous R (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)))
    (fun k => (e k : ℤ)) (homogeneousMatrixColumn d e a)
    (homogeneousMatrixColumn_homogeneous d e hde a) n x hx

theorem homogeneousPolynomialMatrixMap_range_isHomogeneous (d : ι → ℕ) (e : κ → ℕ)
    (hde : ∀ i k, d i ≤ e k)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) :
    (homogeneousPolynomialMatrixMap d e a).range.IsHomogeneous
      (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ))) := by
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(decompose (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun k => (e k : ℤ))) y n).val, ?_⟩
  exact HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.map_homogeneous_component (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun k => (e k : ℤ)))
    (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)))
    (homogeneousPolynomialMatrixMap d e a).toAddMonoidHom
    (homogeneousPolynomialMatrixMap_homogeneous d e hde a) n y

def weightedFreePolynomialModule {η : Type v} [Finite η] (d : η → ℤ) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R where
  Carrier := η →₀ MvPolynomial σ R
  grading := HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R d

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix
