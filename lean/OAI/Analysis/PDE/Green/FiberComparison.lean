import OAI.Analysis.PDE.Green.FiberEnergy

/-! Positivity/comparability of the actual combined energy from the spatial
Dirichlet equation and periodic-cell Green's identity. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem setFiberCombinedEnergy_comparison_cell {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (lam : ℝ) (hlam : 0 < lam)
    (c : (Fin (n + 2) × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s)}
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hr : ContDiff ℝ 2 r)
    (hfiber : (fiberEmbedding (n + 2) s z) ⁻¹' S =
      (euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0})
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → Matrix (Fin (n + 3)) (Fin (n + 3)) (Quaternion ℝ)}
    (hA : Continuous A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hrne : ∀ y ∈ euclideanCoordinates c ⁻¹' Icc a b, r y = 0 → fderiv ℝ r y ≠ 0)
    (huz : ∀ y, r y = 0 → u (fiberEmbedding (n + 2) s z y) = 0)
    (hface : CompatibleCellFaces c a b r (fun p y => u (fiberEmbedding (n + 2) s z y) *
      realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
          (fun y => B (fiberEmbedding (n + 2) s z y) + u (fiberEmbedding (n + 2) s z y)) y)) p q)
        (fun y => u (fiberEmbedding (n + 2) s z y)) p y))
    (hu0 : ∀ y ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0},
      u (fiberEmbedding (n + 2) s z y) ≤ 0)
    (hpos : ∀ y ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
        (fun y => B (fiberEmbedding (n + 2) s z y) + u (fiberEmbedding (n + 2) s z y)) y)).PosSemidef)
    (hrank : ∀ y ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0},
      ∃ w : Fin (n + 2) → Quaternion ℝ,
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B (fiberEmbedding (n + 2) s z y)) y = OAI.Analysis.Calculus.Quaternion.outer w)
    (heq : ∀ y ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0},
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
        (fun y => B (fiberEmbedding (n + 2) s z y) + u (fiberEmbedding (n + 2) s z y)) y) =
          lam * (A (fiberEmbedding (n + 2) s z y) 0 0).re) :
    let X₀ := ∫ y in (fiberEmbedding (n + 2) s z) ⁻¹' S,
      (-u (fiberEmbedding (n + 2) s z y)) * (A (fiberEmbedding (n + 2) s z y) 0 0).re
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ setFiberCombinedEnergy e lam S A B u z ∧
      setFiberCombinedEnergy e lam S A B u z ≤ X₀ := by
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {y | r y < 0}) ⊆ _)
  have h := OAI.Analysis.PDE.Energy.normalized_determinant_energy_comparison_cell e c a b hab
    (contDiff_fiberSection hB z) (contDiff_fiberSection hu z) hr hrne huz hface hu0 hpos hrank
    hlam heq
  dsimp only at h ⊢
  rw [hfiber, setFiberCombinedEnergy_eq_spatial e lam z hb hfiber hA hB hu]
  exact h

end OAI.Analysis.PDE.Green
