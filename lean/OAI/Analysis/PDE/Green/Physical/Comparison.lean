import OAI.Analysis.PDE.Green.Physical.CellGeometry
import OAI.Analysis.PDE.Green.FiberComparison

/-! The determinant-energy comparison on the source's actual moving physical
fibers. The periodic box and regular defining function are constructed, not
hypotheses of the comparison. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem cofactor_firstFlux_periodic_add {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hψ : ∀ x, ψ (x + w) = ψ x) (hu : ∀ x, u (x + w) = u x)
    (p : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    u (x + w) * realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
        (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ y)) p q)
        u p (x + w) =
      u x * realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
        (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ y)) p q)
        u p x := by
  simp only [realFlux, hu, quaternionHessian_periodic_add e ψ w hψ,
    fderiv_periodic_add u w hu]

theorem physical_combined_energy_comparison {n : ℕ}
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ) (hlam : 0 < lam)
    (a : ℝ) (ha : 0 < a) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖energyComplexTime z‖) (ht' : ‖energyComplexTime z‖ ≤ 4)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → Matrix (Fin (n + 3)) (Fin (n + 3)) (Quaternion ℝ)}
    (hA : Continuous A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hBperiod : ∀ j y, B (fiberEmbedding (n + 2) 3 z (y + OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0))) =
      B (fiberEmbedding (n + 2) 3 z y))
    (huperiod : ∀ j y, u (fiberEmbedding (n + 2) 3 z (y + OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0))) =
      u (fiberEmbedding (n + 2) 3 z y))
    (huz : ∀ y, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (energyComplexTime z)
        (physicalSpatialProjection (n + 1) y) = 0 → u (fiberEmbedding (n + 2) 3 z y) = 0)
    (hu0 : ∀ y ∈ physicalSpatialFiber (n + 1) a (energyComplexTime z),
      u (fiberEmbedding (n + 2) 3 z y) ≤ 0)
    (hpos : ∀ y ∈ physicalSpatialFiber (n + 1) a (energyComplexTime z),
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y =>
        B (fiberEmbedding (n + 2) 3 z y) + u (fiberEmbedding (n + 2) 3 z y)) y)).PosSemidef)
    (hrank : ∀ y ∈ physicalSpatialFiber (n + 1) a (energyComplexTime z),
      ∃ w : Fin (n + 2) → Quaternion ℝ,
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B (fiberEmbedding (n + 2) 3 z y)) y = OAI.Analysis.Calculus.Quaternion.outer w)
    (heq : ∀ y ∈ physicalSpatialFiber (n + 1) a (energyComplexTime z),
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y =>
        B (fiberEmbedding (n + 2) 3 z y) + u (fiberEmbedding (n + 2) 3 z y)) y) =
          lam * (A (fiberEmbedding (n + 2) 3 z y) 0 0).re) :
    let X₀ := ∫ y in physicalSpatialFiber (n + 1) a (energyComplexTime z),
      (-u (fiberEmbedding (n + 2) 3 z y)) * (A (fiberEmbedding (n + 2) 3 z y) 0 0).re
    let F := setFiberCombinedEnergy e lam (physicalEnergyCell (n + 1) a) A B u z
    0 ≤ F ∧ ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ F ∧ F ≤ X₀ := by
  let c : (Fin (n + 2) × Fin 3) ≃ Fin ((n * 3 + 5) + 1) :=
    finProdFinEquiv.trans (finCongr (by omega))
  obtain ⟨R, hR, hneg, hzero, hbound, hreg⟩ :=
    exists_physical_spatial_defining (n + 1) a (energyComplexTime z) ha ht ht'
  let r := fun y => R (physicalSpatialProjection (n + 1) y)
  let cp := physicalOptionCoordinates c
  let lo := physicalBoxLower cp
  let hi := physicalBoxUpper cp
  have hcell := physicalSpatialFiber_eq_cell c a (energyComplexTime z) ha ht ht' hneg
  have hfiber : (fiberEmbedding (n + 2) 3 z) ⁻¹' physicalEnergyCell (n + 1) a =
      (euclideanCoordinates c ⁻¹' Icc lo hi) ∩ {y | r y < 0} :=
    (physicalEnergyCell_fiber (n + 1) a z).trans hcell
  have hface : CompatibleCellFaces c lo hi r (fun p y => u (fiberEmbedding (n + 2) 3 z y) *
      realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
          (fun y => B (fiberEmbedding (n + 2) 3 z y) + u (fiberEmbedding (n + 2) 3 z y)) y)) p q)
        (fun y => u (fiberEmbedding (n + 2) 3 z y)) p y) := by
    apply physical_cell_compatible_faces c R hbound
    intro p j y
    exact cofactor_firstFlux_periodic_add e
      (fun y => B (fiberEmbedding (n + 2) 3 z y) + u (fiberEmbedding (n + 2) 3 z y))
      (fun y => u (fiberEmbedding (n + 2) 3 z y)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0))
      (fun x => by rw [hBperiod j x, huperiod j x]) (huperiod j) p y
  have h := setFiberCombinedEnergy_comparison_cell e lam hlam c lo hi
    (physicalBoxLower_le_upper cp) z
    ((hR.of_le (by norm_num)).comp (physicalSpatialProjection (n + 1)).contDiff) hfiber
    hA hB hu (fun y _ => hreg y)
    (fun y hy => huz y ((hzero _).mp hy)) hface
    (fun y hy => hu0 y (hcell.symm ▸ hy))
    (fun y hy => hpos y (hcell.symm ▸ hy))
    (fun y hy => hrank y (hcell.symm ▸ hy))
    (fun y hy => heq y (hcell.symm ▸ hy))
  dsimp only at h ⊢
  rw [physicalEnergyCell_fiber] at h
  refine ⟨?_, h⟩
  apply le_trans (mul_nonneg (by positivity) ?_) h.1
  have hS : MeasurableSet (physicalSpatialFiber (n + 1) a (energyComplexTime z)) :=
    (measurableSet_Icc.prod (isOpen_physical_fiber a (energyComplexTime z) ha ht).measurableSet).preimage
      (physicalSpatialEquiv (n + 1)).measurable
  apply setIntegral_nonneg hS
  intro y hy
  have hd := OAI.LinearAlgebra.Moore.mooreDet_nonneg_of_complexify_posSemidef _ (hpos y hy)
  rw [heq y hy] at hd
  exact mul_nonneg (neg_nonneg.mpr (hu0 y hy)) ((mul_nonneg_iff_of_pos_left hlam).mp hd)

end OAI.Analysis.PDE.Green
