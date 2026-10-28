import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierKernel

/-! Genuine joint smoothness of moving-scale regularization off scale zero. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Schauder

def smoothingParameterSet (m : ℕ) (R : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  {p | p.1 ≠ 0 ∧ |p.1| + ‖p.2‖ < R}

theorem isOpen_smoothingParameterSet (m : ℕ) (R : ℝ) : IsOpen (smoothingParameterSet m R) :=
  (isOpen_ne.preimage continuous_fst).inter
    (isOpen_lt (continuous_fst.abs.add continuous_snd.norm) continuous_const)

theorem regularizedTrace_eq_ball_kernel {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    {R : ℝ} {p : ℝ × EuclideanSpace ℝ (Fin m)} (hp : p ∈ smoothingParameterSet m R) :
    regularizedTrace h p.1 p.2 =
      ∫ y in closedBall (0 : EuclideanSpace ℝ (Fin m)) R, boundarySmoothingKernel m (p, y) * h y := by
  rw [regularizedTrace_kernel h hp.1]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hn : R < ‖y‖ := lt_of_not_ge (fun hn => hy (mem_closedBall_zero_iff.mpr hn))
  rw [boundarySmoothingKernel_eq_zero hp.1 p.2 y (hp.2.trans hn), zero_mul]

theorem contDiffOn_regularizedTrace_parameterSet {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : Continuous h) (R : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h p.1 p.2)
      (smoothingParameterSet m R) := by
  let K := closedBall (0 : EuclideanSpace ℝ (Fin m)) R
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  let ν : Measure K := (volume.restrict K).comap Subtype.val
  have hΩ : IsOpen {q : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) | q.1.1 ≠ 0} :=
    isOpen_ne.preimage (continuous_fst.fst)
  have hs := contDiffOn_weighted_kernel_integral (μ := ν)
    (isOpen_smoothingParameterSet m R) hΩ (boundarySmoothingKernel m)
    (contDiffOn_boundarySmoothingKernel m) (fun t : K => (t : EuclideanSpace ℝ (Fin m)))
    continuous_subtype_val (fun t : K => h t) (hh.comp continuous_subtype_val)
    (fun p hp _ => hp.1)
  apply hs.congr
  intro p hp
  rw [regularizedTrace_eq_ball_kernel h hp]
  have he := integral_subtype_comap (μ := volume.restrict K) hK.isClosed.measurableSet
    (fun y => boundarySmoothingKernel m (p, y) * h y)
  simpa only [ν, Measure.restrict_restrict hK.isClosed.measurableSet, inter_self,
    smul_eq_mul, mul_comm] using he.symm

theorem contDiffAt_regularizedTrace {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : Continuous h)
    (p : ℝ × EuclideanSpace ℝ (Fin m)) (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h q.1 q.2) p := by
  let R := |p.1| + ‖p.2‖ + 1
  have hmem : p ∈ smoothingParameterSet m R := ⟨hp, by dsimp [R]; linarith⟩
  exact (contDiffOn_regularizedTrace_parameterSet h hh R p hmem).contDiffAt
    ((isOpen_smoothingParameterSet m R).mem_nhds hmem)

end OAI.Analysis.PDE.Schauder
