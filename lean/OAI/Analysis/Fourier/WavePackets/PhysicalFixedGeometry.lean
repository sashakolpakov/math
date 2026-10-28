import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet
import OAI.Analysis.PDE.Concentration.UniformBarrier
import OAI.Analysis.PDE.Concentration.BoundaryGeometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff ComplexOrder

/-- A spatially global smooth defining function, with the exact physical
sublevel sets and the exact germ along their closure. -/
theorem exists_smooth_physical_defining {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    ∃ r : (Option (Fin d) → ℂ) → ℝ, ContDiff ℝ ∞ r ∧
      (∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        r =ᶠ[𝓝 q] OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ) ∧
      (∀ q, r q < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ q, r q ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) := by
  exact OAI.Analysis.PDE.Green.exists_global_sublevel_extension (k := ⊤) (OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ)
    ((OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (d := d) (1 / 10) a τ).of_le (by simp))
    (show (0 : ℝ) ≤ 1 by norm_num)
    (OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a τ ha ht 1 le_rfl)
    (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht)

theorem physicalSpatialProjection_surjective (d : ℕ) :
    Function.Surjective (OAI.Analysis.PDE.Green.physicalSpatialProjection d) := by
  intro q
  exact ⟨OAI.Analysis.PDE.Green.physicalSpatialEmbedding d 0 q, OAI.Analysis.PDE.Green.physicalSpatialProjection_embedding d 0 q⟩

theorem spatialDefiningFunction_fderiv_ne_zero (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x = 0) :
    fderiv ℝ (OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ) x ≠ 0 := by
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
    (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) ≤ 1
      from hx.le.trans (by norm_num))
  have hf := ((OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (d := d) (1 / 10) a τ).contDiffAt
    ((OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ).mem_nhds hreg)).differentiableAt (by simp)
  apply OAI.Analysis.PDE.Green.fderiv_comp_surjective_ne_zero (OAI.Analysis.PDE.Green.physicalSpatialProjection d)
    (physicalSpatialProjection_surjective d) hf
  intro hz
  have hn := OAI.Analysis.Calculus.Current.physicalFiberDefining_fderiv_norm_lower a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)
    ha ht ht' hx.le (by
      change -(1 / 2 : ℝ) ≤ OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x
      rw [hx]
      norm_num)
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- All geometric hypotheses needed by the fixed-fiber periodic Dirichlet
theorem, established for the actual physical fiber and any real lattice. -/
theorem exists_physical_dirichlet_geometry {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4)
    (b : Basis (Fin (d + 1)) ℝ (Fin (d + 1) → ℝ)) :
    ∃ r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ,
      ContDiff ℝ ∞ r ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit d) b r ∧
      (∀ x, OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x ≤ 0 → r =ᶠ[𝓝 x] OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ) ∧
      (∀ x, r x < 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x < 0) ∧
      (∀ x, r x ≤ 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x ≤ 0) ∧
      (∀ x, r x = 0 → fderiv ℝ r x ≠ 0) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots r x)).PosDef) := by
  obtain ⟨r, hr, hg, hn, hl⟩ := exists_smooth_physical_defining (d := d) a τ ha ht
  let r' := r ∘ OAI.Analysis.PDE.Green.physicalSpatialProjection d
  have hg' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ x ≤ 0) :
      r' =ᶠ[𝓝 x] OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ :=
    (hg _ hx).comp_tendsto (OAI.Analysis.PDE.Green.physicalSpatialProjection d).continuous.continuousAt
  refine ⟨r', hr.comp (OAI.Analysis.PDE.Green.physicalSpatialProjection d).contDiff,
    OAI.Analysis.PDE.Concentration.transverse_latticePeriodic b r, hg', (fun x => hn _), (fun x => hl _), ?_, ?_⟩
  · intro x hx
    have hle := (hl _).mp hx.le
    have he := hg' x hle
    rw [he.fderiv_eq]
    apply spatialDefiningFunction_fderiv_ne_zero d a τ ha ht ht' x
    rw [← he.eq_of_nhds]
    exact hx
  · intro x hx
    have hle := (hl _).mp hx
    have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (hle.trans (show (0 : ℝ) ≤ 1 by norm_num))
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.threeSlots (hg' x hle),
      OAI.Analysis.PDE.Concentration.quaternionHessian_spatialDefiningFunction d a τ x hreg]
    exact OAI.Analysis.PDE.Concentration.spatial_defining_matrix_uniform_posDef d a τ _ ha ht ht' hle

end OAI.Analysis.Fourier.WavePackets
