import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeDegreeComponents

/-! # Weighted Free Component Values -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeComponentValues

noncomputable section

/-! Evaluation of weighted homogeneous-degree coordinates. -/

open _root_.MvPolynomial
universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ]
variable {ι : Type w} [Fintype ι]

theorem weightedFreeDegreeComponentsEquiv_apply_val (d : ι → ℕ) (n : ℕ)
    (hd : ∀ i, d i ≤ n)
    (x : HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R (fun i => (d i : ℤ)) (n : ℤ)) (i : ι) :
    (WeightedFreeDegreeComponents.weightedFreeDegreeComponentsEquiv d n hd x i).val = x.val i := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeComponentValues
