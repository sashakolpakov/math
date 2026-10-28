import OAI.Analysis.PDE.Concentration.Physical.LatticeComparison

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Energy OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore OAI.Analysis.Calculus.Current
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder MatrixOrder

/-- Only integrability on the fiber, not global continuity of the current,
is needed to identify the actual combined energy. This applies to currents
which are smooth near the physical fibers but singular elsewhere. -/
theorem setFiberCombinedEnergy_eq_spatial_integrable {n s : ℕ}
    (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)} {V : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (hV : Bornology.IsBounded V)
    (hfiber : (OAI.Analysis.PDE.Green.fiberEmbedding n s z) ⁻¹' S = V)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hm : IntegrableOn (fun y => (-u (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) *
      (A (OAI.Analysis.PDE.Green.fiberEmbedding n s z y) 0 0).re) V) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam S A B u z =
      (∫ y in V, (-u (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) * (A (OAI.Analysis.PDE.Green.fiberEmbedding n s z y) 0 0).re) +
      OAI.Analysis.PDE.Energy.determinantSegmentEnergy e V
        (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) (fun y => u (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) / lam := by
  have hf : Continuous (OAI.Analysis.PDE.Green.fiberEmbedding n s z) :=
    (OAI.Analysis.PDE.Green.continuous_fiberEmbedding n s).comp (continuous_const.prodMk continuous_id)
  have he : IntegrableOn (fun y =>
      OAI.Analysis.PDE.Green.spatialPencilEnergyDensity e B u (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) V :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hV
      ((OAI.Analysis.PDE.Green.continuous_spatialPencilEnergyDensity e hB hu).comp hf)
  unfold OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.PDE.Green.combinedEnergyDensity
  rw [hfiber, integral_add hm (he.const_mul _), integral_const_mul,
    OAI.Analysis.PDE.Green.determinantSegmentEnergy_fiber_eq e V (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) z]
  ring

theorem setFiberCombinedEnergy_comparison_lattice_integrable {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (lam : ℝ) (hlam : 0 < lam)
    (c : (Fin (n + 2) × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s)}
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hr : ContDiff ℝ 2 r)
    (hfiber : (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z) ⁻¹' S =
      (euclideanLatticeCell c L a b) ∩ {y | r y < 0})
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → Matrix (Fin (n + 3)) (Fin (n + 3)) (Quaternion ℝ))
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hm : IntegrableOn (fun y => (-u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y)) *
      (A (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) s z y) 0 0).re) ((euclideanLatticeCell c L a b) ∩ {y | r y < 0}))
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
  rw [hfiber, setFiberCombinedEnergy_eq_spatial_integrable e lam z hb hfiber A hB hu hm]
  exact h

end OAI.Analysis.PDE.Concentration
