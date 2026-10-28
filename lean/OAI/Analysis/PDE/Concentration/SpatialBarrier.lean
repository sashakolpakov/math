import OAI.Analysis.PDE.Concentration.SpatialHessian
import OAI.Analysis.PDE.Concentration.DirichletComparison

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff Matrix ComplexOrder

theorem quaternionHessian_linear_combination_at {n s : ℕ} (slots : Fin s → Quaternion ℝ)
    {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (a b : ℝ) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => a * f y + b * g y) x =
      a • OAI.Analysis.PDE.Dirichlet.quaternionHessian slots f x + b • OAI.Analysis.PDE.Dirichlet.quaternionHessian slots g x := by
  obtain ⟨f', hf', hfeq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  obtain ⟨g', hg', hgeq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hg
  have heq : (fun y => a * f' y + b * g' y) =ᶠ[𝓝 x] (fun y => a * f y + b * g y) := by
    filter_upwards [hfeq, hgeq] with y hy hz
    rw [hy, hz]
  rw [← OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ slots heq]
  simp only [← smul_eq_mul]
  rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul slots (hf'.const_smul a) hg',
    OAI.Analysis.PDE.Dirichlet.quaternionHessian_smul slots hf', OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ slots hfeq,
    OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ slots hgeq]

theorem spatial_functions_contDiffAt (d : ℕ) (a : ℝ) (τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (hx : OAI.Analysis.PDE.Green.physicalSpatialProjection d x ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ) :
    ContDiffAt ℝ 2 (spatialDefiningFunction d a τ) x ∧
      ContDiffAt ℝ 2 (spatialBackgroundFunction d τ) x := by
  constructor
  · exact (((OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (1 / 10) a τ).of_le (by norm_num)).contDiffAt
      ((OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ).mem_nhds hx)).comp x (OAI.Analysis.PDE.Green.physicalSpatialProjection d).contDiff.contDiffAt
  · have hp := (OAI.Analysis.Calculus.Current.contDiffAt_phi_real _ hx.1).comp (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)
      (OAI.Analysis.Calculus.Current.contDiff_physicalEmbedding τ).contDiffAt
    exact ((hp.norm_sq ℂ).of_le (by norm_num)).comp x (OAI.Analysis.PDE.Green.physicalSpatialProjection d).contDiff.contDiffAt

/-- The determinant lower bound is realized by the actual scalar candidate
`lam * B + b * r` on the physical three-slot spatial domain. -/
theorem spatial_input_barrier_determinant (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → spatialDefiningFunction (n + 1) a τ x ≤ 0 →
      ∀ (b lam : ℝ), 0 < b → 0 ≤ lam →
      lam * (b * (c / a ^ 2)) ^ (n + 1) ≤ OAI.LinearAlgebra.Moore.mooreDet (n + 2)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => lam * spatialBackgroundFunction (n + 1) τ y +
          b * spatialDefiningFunction (n + 1) a τ y) x) := by
  obtain ⟨c, hc, hb⟩ := physical_input_barrier_determinant n
  refine ⟨c, hc, ?_⟩
  intro a τ x ha ht ht' hr b lam hbp hlam
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
    (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) x) ≤ 1
      from hr.trans (by norm_num))
  obtain ⟨hrc, hBc⟩ := spatial_functions_contDiffAt (n + 1) a τ x hreg
  rw [quaternionHessian_linear_combination_at OAI.Analysis.Calculus.Quaternion.threeSlots hBc hrc,
    quaternionHessian_spatialBackgroundFunction (n + 1) τ x hreg.1,
    quaternionHessian_spatialDefiningFunction (n + 1) a τ x hreg]
  exact hb a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) x) ha ht ht' hr b lam hbp hlam

theorem spatial_defining_matrix_posDef (d : ℕ) (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4 * a)
    (hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    (OAI.LinearAlgebra.Moore.complexify (spatialDefiningMatrix d a τ q)).PosDef := by
  obtain ⟨c, hc, hb⟩ := physical_defining_matrix_lower d
  have hs := spatial_defining_shift d a τ q (c / a ^ 2) (hb a τ q ha ht ht' hr)
  have hp := OAI.LinearAlgebra.Moore.complexify_add_pos_identity _ hs (show 0 < c / a ^ 2 by positivity)
  simpa only [sub_add_cancel] using hp

theorem spatial_input_barrier_posDef (d : ℕ) (a : ℝ) (τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4 * a)
    (hr : spatialDefiningFunction d a τ x ≤ 0) {b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun y => lam * spatialBackgroundFunction d τ y + b * spatialDefiningFunction d a τ y) x)).PosDef := by
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
    (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) ≤ 1
      from hr.trans (by norm_num))
  obtain ⟨hrc, hBc⟩ := spatial_functions_contDiffAt d a τ x hreg
  rw [quaternionHessian_linear_combination_at OAI.Analysis.Calculus.Quaternion.threeSlots hBc hrc,
    quaternionHessian_spatialBackgroundFunction d τ x hreg.1,
    quaternionHessian_spatialDefiningFunction d a τ x hreg]
  apply OAI.Analysis.PDE.Dirichlet.moore_barrier_matrix_posDef _ _ _ (spatial_defining_matrix_posDef d a τ _ ha ht ht' hr) hb
  obtain ⟨v, hv⟩ := spatial_background_outer d τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) hreg.1
  rw [hv, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact (OAI.LinearAlgebra.Moore.complexify_outer_posSemidef v).smul hlam

end OAI.Analysis.PDE.Concentration
