import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierSmooth
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.KernelJets

/-! Uniform unit-scale bounds for the first three smoothing derivatives. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Schauder

local instance unitJetFirstGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance unitJetFirstSpace (m : ℕ) : NormedSpace ℝ ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance unitJetSecondGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance unitJetSecondSpace (m : ℕ) : NormedSpace ℝ ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance unitJetThirdGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance

theorem exists_regularizedTrace_unit_three_bound (m : ℕ) :
    ∃ C > 0, ∀ (h : EuclideanSpace ℝ (Fin m) → ℝ), Continuous h →
      ∀ W, 0 ≤ W → (∀ y, ‖y‖ ≤ 3 → |h y| ≤ W) →
      let S := fun p : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h p.1 p.2
      ‖fderiv ℝ S (1, 0)‖ ≤ C * W ∧
      ‖fderiv ℝ (fderiv ℝ S) (1, 0)‖ ≤ C * W ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ S)) (1, 0)‖ ≤ C * W := by
  let K := closedBall (0 : EuclideanSpace ℝ (Fin m)) 3
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  let ν : Measure K := (volume.restrict K).comap Subtype.val
  have hΩ : IsOpen {q : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) | q.1.1 ≠ 0} :=
    isOpen_ne.preimage continuous_fst.fst
  have hx : (1, (0 : EuclideanSpace ℝ (Fin m))) ∈ smoothingParameterSet m 3 := by
    constructor <;> norm_num
  obtain ⟨C, hC, hb⟩ := exists_weighted_kernel_three_bound (μ := ν)
    (isOpen_smoothingParameterSet m 3) hΩ (boundarySmoothingKernel m)
    (contDiffOn_boundarySmoothingKernel m) (fun t : K => (t : EuclideanSpace ℝ (Fin m)))
    continuous_subtype_val (fun p hp _ => hp.1) hx
  refine ⟨C, hC, ?_⟩
  intro h hh W hW hsup
  have hbounds := hb (fun t : K => h t) (hh.comp continuous_subtype_val) W hW
    (fun t => hsup t (mem_closedBall_zero_iff.mp t.property))
  have he : (fun p : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h p.1 p.2) =ᶠ[𝓝 (1, 0)]
      (fun p => ∫ t : K, h t • boundarySmoothingKernel m (p, t) ∂ν) := by
    filter_upwards [(isOpen_smoothingParameterSet m 3).mem_nhds hx] with p hp
    rw [regularizedTrace_eq_ball_kernel h hp]
    have hi := integral_subtype_comap (μ := volume.restrict K) hK.isClosed.measurableSet
      (fun y => boundarySmoothingKernel m (p, y) * h y)
    simpa only [ν, Measure.restrict_restrict hK.isClosed.measurableSet, inter_self,
      smul_eq_mul, mul_comm] using hi.symm
  dsimp only
  rw [he.fderiv_eq, he.fderiv.fderiv_eq, he.fderiv.fderiv.fderiv_eq]
  exact hbounds

end OAI.Analysis.PDE.Schauder
