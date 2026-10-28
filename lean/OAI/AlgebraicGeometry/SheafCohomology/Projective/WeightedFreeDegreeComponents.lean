import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix

/-! # Weighted Free Degree Components -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeDegreeComponents

noncomputable section

/-! Coordinates of a sufficiently high degree piece of a weighted free polynomial module. -/

open _root_.MvPolynomial
universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ]
variable {ι : Type w} [Fintype ι]

def weightedFreeDegreeComponents (d : ι → ℕ) (n : ℕ) (hd : ∀ i, d i ≤ n) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R (fun i => (d i : ℤ)) (n : ℤ) →ₗ[R]
      (∀ i, homogeneousSubmodule σ R (n - d i)) where
  toFun f i := ⟨f.val i, by
    have hi := (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading R (fun i => (d i : ℤ)) (n : ℤ) f.val).mp f.property i
    rwa [← Int.natCast_sub (hd i), HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat] at hi⟩
  map_add' f g := by ext i; rfl
  map_smul' r f := by ext i; rfl

def weightedFreeDegreeComponentsEquiv (d : ι → ℕ) (n : ℕ) (hd : ∀ i, d i ≤ n) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R (fun i => (d i : ℤ)) (n : ℤ) ≃ₗ[R]
      (∀ i, homogeneousSubmodule σ R (n - d i)) :=
  LinearEquiv.ofBijective (weightedFreeDegreeComponents d n hd) (by
    constructor
    · intro f g h
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      exact congrArg (fun a => (a i).val) h
    · intro f
      let x : ι →₀ MvPolynomial σ R := Finsupp.equivFunOnFinite.symm (fun i => (f i).val)
      have hx : x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)) (n : ℤ) := by
        rw [HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading]
        intro i
        change (f i).val ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R ((n : ℤ) - (d i : ℤ))
        rw [← Int.natCast_sub (hd i), HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
        exact (f i).property
      exact ⟨⟨x, hx⟩, rfl⟩)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeDegreeComponents
