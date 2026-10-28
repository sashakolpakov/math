import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Holomorphic Regularity At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt.Constructions.HolomorphicRegularity

noncomputable section

/-!
# RiemannProjectivity: continuous derivatives of holomorphic maps in finite dimensions

Restriction to affine complex lines turns continuity in the base point into
locally uniform convergence. The one-variable Cauchy theorem then gives
continuity of each directional derivative, hence of the full derivative.
This supplies the regularity needed for local inverse-function coordinates.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace W] in
theorem deriv_affineLine {f : V → W} {x : V} (hf : DifferentiableAt ℂ f x) (v : V) :
    deriv (fun z : ℂ => f (x + z • v)) 0 = fderiv ℂ f x v := by
  have h : HasDerivAt (fun z : ℂ => f (x + z • v)) (fderiv ℂ f x v) 0 := by
    have hfx : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa only [zero_smul, add_zero] using hf.hasFDerivAt
    convert! hfx.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x) using 1
    simp
  exact h.deriv

variable [FiniteDimensional ℂ V]

theorem continuousAt_directionalDerivative {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U) (v : V) :
    ContinuousAt (fun y => fderiv ℂ f y v) x := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  let A : V × ℂ → V := fun p => p.1 + p.2 • v
  have hA : Continuous A := continuous_fst.add (continuous_snd.smul continuous_const)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hU.preimage hA) (x, 0)
    (by simpa [A] using hx)
  have hδ : 0 < r / 2 := half_pos hr
  have hmem : ∀ y ∈ closedBall x (r / 2), ∀ z ∈ closedBall (0 : ℂ) (r / 2),
      y + z • v ∈ U := by
    intro y hy z hz
    apply hsub (a := (y, z))
    change dist (y, z) (x, 0) < r
    rw [Prod.dist_eq]
    exact max_lt ((mem_closedBall.mp hy).trans_lt (half_lt_self hr))
      ((mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  have hcont : ContinuousOn (fun p : V × ℂ => f (p.1 + p.2 • v))
      (closedBall x (r / 2) ×ˢ closedBall (0 : ℂ) (r / 2)) :=
    hf.continuousOn.comp hA.continuousOn (fun p hp => hmem p.1 hp.1 p.2 hp.2)
  have hlim : TendstoUniformlyOn (fun y z => f (y + z • v))
      (fun z => f (x + z • v)) (𝓝 x) (closedBall (0 : ℂ) (r / 2)) := by
    have h := ((isCompact_closedBall x (r / 2)).prod
      (isCompact_closedBall (0 : ℂ) (r / 2))).uniformContinuousOn_of_continuous hcont
    simpa only [nhdsWithin_eq_nhds.mpr (closedBall_mem_nhds _ hδ)] using
      h.tendstoUniformlyOn (F := fun y z => f (y + z • v)) (x := x)
        (mem_closedBall_self hδ.le)
  have hdiff : ∀ᶠ y in 𝓝 x,
      DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (ball 0 (r / 2)) := by
    filter_upwards [closedBall_mem_nhds x hδ] with y hy
    intro z hz
    have hfz : DifferentiableAt ℂ f (y + z • v) :=
      (hf _ (hmem y hy z (ball_subset_closedBall hz))).differentiableAt
        (hU.mem_nhds (hmem y hy z (ball_subset_closedBall hz)))
    exact (hfz.comp z (((differentiable_id.smul_const v).const_add y) z)).differentiableWithinAt
  have ht := ((hlim.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.deriv hdiff
    isOpen_ball).tendsto_at (mem_ball_self hδ)
  have hder : ∀ y ∈ closedBall x (r / 2),
      deriv (fun z : ℂ => f (y + z • v)) 0 = fderiv ℂ f y v := by
    intro y hy
    have hyU : y ∈ U := by simpa using hmem y hy 0 (mem_closedBall_self hδ.le)
    exact deriv_affineLine ((hf y hyU).differentiableAt (hU.mem_nhds hyU)) v
  rw [hder x (mem_closedBall_self hδ.le)] at ht
  exact ht.congr' (by
    filter_upwards [closedBall_mem_nhds x hδ] with y hy
    exact hder y hy)

/-- Complex differentiability on an open finite-dimensional domain implies C¹ regularity. -/
theorem contDiffAt_one_of_differentiableOn {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U) :
    ContDiffAt ℂ 1 f x := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fderiv ℂ f, U, hU.mem_nhds hx, ?_, ?_⟩
  · intro y hy
    exact (continuousAt_clm_apply.mpr fun v =>
      continuousAt_directionalDerivative hU hf hy v).continuousWithinAt
  · intro y hy
    exact ((hf y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt.Constructions.HolomorphicRegularity
