import OAI.Analysis.PDE.Green.Physical.Faces
import OAI.Analysis.PDE.Green.Localized.Green

/-! The actual current and determinant Green fluxes have compatible artificial
box faces: periodic real faces cancel and all other active faces miss the fiber. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise

theorem time_test_zero_off_tsupport {n s : ℕ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s} (hx : timeProjection n s x ∉ tsupport η) :
    (fun y => η (timeProjection n s y)) =ᶠ[𝓝 x] (fun _ => 0) := by
  have hz : η =ᶠ[𝓝 (timeProjection n s x)] (fun _ => 0) := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  exact hz.comp_tendsto ((timeProjection n s).continuous.tendsto x)

theorem time_test_spatial_periodic {n s : ℕ} (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ)
    (j : Fin n) (k : Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    η (timeProjection n s (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, k))) = η (timeProjection n s x) := by
  rw [map_add, timeProjection_coordinate_succ, add_zero]

theorem physical_time_box_secondGreen_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) (L : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hL : ∀ z ∈ tsupport η, ∀ s, -L < z (0, s) ∧ z (0, s) < L)
    (hbound : ∀ x, timeProjection (d + 1) 3 x ∈ tsupport η →
      R (fullPhysicalProjection d x) ≤ 0 → ‖(fullPhysicalProjection d x).2‖ ≤ 28)
    (K : (Fin (d + 2) × Fin 3) → (Fin (d + 2) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hK : ∀ p q (j : Fin (d + 1)) x, K p q (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = K p q x)
    (hu : ∀ (j : Fin (d + 1)) x, u (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = u x) :
    CompatibleCellFaces c (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)
      (fun x => R (fullPhysicalProjection d x))
      (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector K u (fun x => η (timeProjection (d + 1) 3 x))) := by
  apply physical_time_box_compatible_faces c L R η hL hbound
  · intro p j x
    exact secondGreenFlux_periodic_add OAI.Analysis.PDE.Dirichlet.coordinateVector K u _ (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0))
      (fun p q => hK p q j) (hu j) (time_test_spatial_periodic η j 0) p x
  · intro x hx p
    exact (secondGreenFlux_eventually_zero OAI.Analysis.PDE.Dirichlet.coordinateVector K u _ x
      (time_test_zero_off_tsupport hx)).self_of_nhds p

theorem physical_time_box_cofactor_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) (L : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hL : ∀ z ∈ tsupport η, ∀ s, -L < z (0, s) ∧ z (0, s) < L)
    (hbound : ∀ x, timeProjection (d + 1) 3 x ∈ tsupport η →
      R (fullPhysicalProjection d x) ≤ 0 → ‖(fullPhysicalProjection d x).2‖ ≤ 28)
    (e : Fin 3 → Quaternion ℝ) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hB : ∀ (j : Fin (d + 1)) x, B (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = B x)
    (hu : ∀ (j : Fin (d + 1)) x, u (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = u x) (t : ℝ) :
    CompatibleCellFaces c (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)
      (fun x => R (fullPhysicalProjection d x))
      (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
        (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (d + 2)
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q)
        u (fun x => η (timeProjection (d + 1) 3 x))) := by
  apply physical_time_box_secondGreen_faces c L R η hL hbound _ u _ hu
  intro p q j x
  rw [quaternionHessian_periodic_add e (fun y => B y + t * u y)
    (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) (fun y => by rw [hB j y, hu j y])]

end OAI.Analysis.PDE.Green
