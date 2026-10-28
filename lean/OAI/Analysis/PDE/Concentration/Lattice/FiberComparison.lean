import OAI.Analysis.PDE.Green.FiberEnergy
import OAI.Analysis.PDE.Concentration.Lattice.Comparison

/-! Positivity/comparability of the actual combined energy from the spatial
Dirichlet equation and periodic-cell Green's identity. -/

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Green Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem setFiberCombinedEnergy_comparison_lattice {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (lam : ℝ) (hlam : 0 < lam)
    (c : (Fin (n + 2) × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s)}
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hr : ContDiff ℝ 2 r)
    (hfiber : (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z) ⁻¹' S =
      (euclideanLatticeCell c L a b) ∩ {y | r y < 0})
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → Matrix (Fin (n + 3)) (Fin (n + 3)) (Quaternion ℝ)}
    (hA : Continuous A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hrne : ∀ y ∈ euclideanLatticeCell c L a b, r y = 0 → fderiv ℝ r y ≠ 0)
    (huz : ∀ y, r y = 0 → u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) = 0)
    (hface : CompatibleLatticeFaces c L a b r (fun p y => u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) *
      OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
          (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) y)) p q)
        (fun y => u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) p y))
    (hu0 : ∀ y ∈ (euclideanLatticeCell c L a b) ∩ {y | r y < 0},
      u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) ≤ 0)
    (hpos : ∀ y ∈ (euclideanLatticeCell c L a b) ∩ {y | r y < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
        (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) y)).PosSemidef)
    (hrank : ∀ y ∈ (euclideanLatticeCell c L a b) ∩ {y | r y < 0},
      ∃ w : Fin (n + 2) → Quaternion ℝ,
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) y = OAI.Analysis.Calculus.Quaternion.outer w)
    (heq : ∀ y ∈ (euclideanLatticeCell c L a b) ∩ {y | r y < 0},
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
        (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) y) =
          lam * (A (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) 0 0).re) :
    let X₀ := ∫ y in (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z) ⁻¹' S,
      (-u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) * (A (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) 0 0).re
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam S A B u z ∧
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam S A B u z ≤ X₀ := by
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : ((euclideanLatticeCell c L a b) ∩ {y | r y < 0}) ⊆ _)
  have h := normalized_determinant_energy_comparison_lattice e c L a b hab
    (OAI.Analysis.PDE.Green.contDiff_fiberSection hB z) (OAI.Analysis.PDE.Green.contDiff_fiberSection hu z) hr hrne huz hface hu0 hpos hrank
    hlam heq
  dsimp only at h ⊢
  rw [hfiber, OAI.Analysis.PDE.Green.setFiberCombinedEnergy_eq_spatial e lam z hb hfiber hA hB hu]
  exact h

end OAI.Analysis.PDE.Concentration
