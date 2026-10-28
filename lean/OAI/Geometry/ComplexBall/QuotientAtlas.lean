import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall
import OAI.Geometry.ComplexBall.LocalLifts

/-! # Quotient Atlas -/

namespace OAI.Geometry.ComplexBall.QuotientAtlas.Arithmetic

noncomputable section

section

/-! Local branches of the ball quotient, in affine coordinates, are
holomorphic. Any two lifts differ locally by one fixed unitary matrix. -/

open scoped Classical ContDiff
open _root_.Topology Filter

def ballInclusion (b : ℂ) (hb : b.re < 0) : OpenPartialHomeomorph (ArithmeticQuotientBoostBall.Ball b) ArithmeticQuotientBoostBall.BallCoordinates :=
  (ArithmeticQuotientBoostBall.ballOpen b).openPartialHomeomorphSubtypeCoe ⟨ArithmeticQuotientBoostBall.ballOrigin b hb⟩

lemma ballInclusion_apply (b : ℂ) (hb : b.re < 0) (z : ArithmeticQuotientBoostBall.Ball b) :
    ballInclusion b hb z = z.val := rfl

lemma ballInclusion_source (b : ℂ) (hb : b.re < 0) :
    (ballInclusion b hb).source = Set.univ := rfl

lemma ballInclusion_target (b : ℂ) (hb : b.re < 0) :
    (ballInclusion b hb).target = (ArithmeticQuotientBoostBall.ballOpen b : Set ArithmeticQuotientBoostBall.BallCoordinates) :=
  (ArithmeticQuotientBoostBall.ballOpen b).openPartialHomeomorphSubtypeCoe_target _

lemma ballInclusion_symm_coe (b : ℂ) (hb : b.re < 0) (z : ArithmeticQuotientBoostBall.Ball b) :
    (ballInclusion b hb).symm z.val = z := (ballInclusion b hb).left_inv (Set.mem_univ z)

lemma ballInclusion_symm_val (b : ℂ) (hb : b.re < 0)
    {z : ArithmeticQuotientBoostBall.BallCoordinates} (hz : z ∈ ArithmeticQuotientBoostBall.ballOpen b) : ((ballInclusion b hb).symm z).val = z := by
  exact (ballInclusion b hb).right_inv (by rwa [ballInclusion_target])

lemma quotient_branch_contDiffAt (b : ℂ) (hb : b.re < 0)
    (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
    {Q : Type*} [TopologicalSpace Q] {f : ArithmeticQuotientBoostBall.Ball b → Q} (hf : IsQuotientCoveringMap f Γ)
    (e : OpenPartialHomeomorph Q (ArithmeticQuotientBoostBall.Ball b)) (he : ∀ y ∈ e.source, f (e y) = y)
    (z : ArithmeticQuotientBoostBall.Ball b) (hz : f z ∈ e.source) (n : ℕ∞ω) :
    ContDiffAt ℂ n (fun w : ArithmeticQuotientBoostBall.BallCoordinates => (e (f ((ballInclusion b hb).symm w))).val) z.val := by
  let τ := ballInclusion b hb
  have hτ : τ.symm z.val = z := ballInclusion_symm_coe b hb z
  have hτt : z.val ∈ τ.target := by rw [ballInclusion_target]; exact z.property
  have hu : ContinuousAt τ.symm z.val := τ.continuousAt_symm hτt
  have hfu : ContinuousAt (fun w => f (τ.symm w)) z.val := hf.continuous.continuousAt.comp hu
  have hsource : f (τ.symm z.val) ∈ e.source := by rw [hτ]; exact hz
  have hv : ContinuousAt (fun w => e (f (τ.symm w))) z.val :=
    ContinuousAt.comp (f := fun w : ArithmeticQuotientBoostBall.BallCoordinates => f (τ.symm w)) (g := e)
      (e.continuousAt hsource) hfu
  obtain ⟨γ, hγ⟩ := hf.apply_eq_iff_mem_orbit.mp (he (f z) hz)
  have hgu : ContinuousAt (fun w => γ • τ.symm w) z.val :=
    (continuous_const_smul γ).continuousAt.comp hu
  have hc : (fun w => f (e (f (τ.symm w)))) =ᶠ[𝓝 z.val] (fun w => f (γ • τ.symm w)) := by
    have hs : ∀ᶠ w in 𝓝 z.val, f (τ.symm w) ∈ e.source := hfu (e.open_source.mem_nhds hsource)
    filter_upwards [hs] with w hw
    rw [he _ hw, hf.map_smul]
  have hl : (fun w => e (f (τ.symm w))) =ᶠ[𝓝 z.val] (fun w => γ • τ.symm w) :=
    LocalLifts.ArithmeticQuotient.local_lifts_eventuallyEq hf.isCoveringMap.isLocalHomeomorph hv hgu
      (by rw [hτ]; exact hγ.symm) hc
  apply (ArithmeticQuotientBoostBall.contDiffAt_ballActionCoordinates b γ.val z n).congr_of_eventuallyEq
  have hs : ∀ᶠ w in 𝓝 z.val, w ∈ ArithmeticQuotientBoostBall.ballOpen b := (ArithmeticQuotientBoostBall.ballOpen b).isOpen.mem_nhds z.property
  filter_upwards [hl, hs] with w hw hwb
  change (e (f (τ.symm w))).val = ArithmeticQuotientBoostBall.ballActionCoordinates γ.val.val w
  rw [hw]
  change (γ.val • τ.symm w).val = _
  rw [ArithmeticQuotientBoostBall.ball_smul_coordinates]
  exact congrArg (ArithmeticQuotientBoostBall.ballActionCoordinates γ.val.val) (ballInclusion_symm_val b hb hwb)

end

/-! The actual complex atlas on the free properly discontinuous ball
quotient. Its chart changes are the holomorphic local branches just proved. -/

open scoped Classical _root_.Manifold ContDiff
open _root_.Topology

variable (b : ℂ) (hb : b.re < 0) (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
  [ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball b)]

abbrev BallQuotient := MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b)

def ballQuotientProjection : ArithmeticQuotientBoostBall.Ball b → BallQuotient b Γ := Quotient.mk _

lemma ballQuotientProjection_covering : IsQuotientCoveringMap (ballQuotientProjection b Γ) Γ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

def ballQuotientBranch (q : ArithmeticQuotientBoostBall.Ball b) : OpenPartialHomeomorph (BallQuotient b Γ) (ArithmeticQuotientBoostBall.Ball b) :=
  (ballQuotientProjection_covering b Γ).isCoveringMap.isLocalHomeomorph.localInverseAt q

def ballQuotientChart (q : ArithmeticQuotientBoostBall.Ball b) :
    OpenPartialHomeomorph (BallQuotient b Γ) ArithmeticQuotientBoostBall.BallCoordinates :=
  (ballQuotientBranch b Γ q).trans (ballInclusion b hb)

lemma ballQuotientChart_source (q : ArithmeticQuotientBoostBall.Ball b) :
    (ballQuotientChart b hb Γ q).source = (ballQuotientBranch b Γ q).source := by
  simp [ballQuotientChart, ballInclusion_source]

lemma ballQuotientChart_apply (q : ArithmeticQuotientBoostBall.Ball b) (y : BallQuotient b Γ) :
    ballQuotientChart b hb Γ q y = (ballQuotientBranch b Γ q y).val := rfl

lemma ballQuotientChart_symm_apply (q : ArithmeticQuotientBoostBall.Ball b) (z : ArithmeticQuotientBoostBall.BallCoordinates) :
    (ballQuotientChart b hb Γ q).symm z =
      ballQuotientProjection b Γ ((ballInclusion b hb).symm z) := by
  change (ballQuotientBranch b Γ q).symm ((ballInclusion b hb).symm z) = _
  exact congrFun ((ballQuotientProjection_covering b Γ).isCoveringMap.isLocalHomeomorph.localInverseAt_symm q) _

lemma ballQuotientChart_target_subset (q : ArithmeticQuotientBoostBall.Ball b) :
    (ballQuotientChart b hb Γ q).target ⊆ (ArithmeticQuotientBoostBall.ballOpen b : Set ArithmeticQuotientBoostBall.BallCoordinates) := by
  intro z hz
  exact (ballInclusion_target b hb) ▸ hz.1

@[instance_reducible] def ballQuotientAtlas : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (BallQuotient b Γ) where
  atlas := Set.range (ballQuotientChart b hb Γ)
  chartAt q := ballQuotientChart b hb Γ q.out
  chart_mem_atlas q := ⟨q.out, rfl⟩
  mem_chart_source q := by
    rw [ballQuotientChart_source]
    have h := (ballQuotientProjection_covering b Γ).isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := q.out)
    change ballQuotientProjection b Γ q.out ∈ (ballQuotientBranch b Γ q.out).source at h
    simpa only [ballQuotientProjection, Quotient.out_eq] using h

theorem ballQuotientAtlas_isManifold :
    @IsManifold ℂ _ ArithmeticQuotientBoostBall.BallCoordinates _ _ ArithmeticQuotientBoostBall.BallCoordinates _ 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1
      (BallQuotient b Γ) _ (ballQuotientAtlas b hb Γ) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (BallQuotient b Γ) := ballQuotientAtlas b hb Γ
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id_eq, Set.range_id, Set.inter_univ]
  intro z hz
  have hzball := ballQuotientChart_target_subset b hb Γ q hz.1
  let w : ArithmeticQuotientBoostBall.Ball b := ⟨z, hzball⟩
  have hzsource : ballQuotientProjection b Γ w ∈ (ballQuotientBranch b Γ q').source := by
    have h := hz.2
    change (ballQuotientChart b hb Γ q).symm z ∈ (ballQuotientChart b hb Γ q').source at h
    rw [ballQuotientChart_source, ballQuotientChart_symm_apply] at h
    simpa only [show (ballInclusion b hb).symm z = w from ballInclusion_symm_coe b hb w] using h
  have hcd := quotient_branch_contDiffAt b hb Γ (ballQuotientProjection_covering b Γ)
    (ballQuotientBranch b Γ q')
    (fun y hy => (ballQuotientProjection_covering b Γ).isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy)
    w hzsource 1
  have hfun : (fun x : ArithmeticQuotientBoostBall.BallCoordinates =>
      (ballQuotientChart b hb Γ q') ((ballQuotientChart b hb Γ q).symm x)) =
      (fun x : ArithmeticQuotientBoostBall.BallCoordinates =>
        (ballQuotientBranch b Γ q' (ballQuotientProjection b Γ ((ballInclusion b hb).symm x))).val) := by
    funext x
    rw [ballQuotientChart_apply, ballQuotientChart_symm_apply]
  change ContDiffWithinAt ℂ 1 (fun x => (ballQuotientChart b hb Γ q') ((ballQuotientChart b hb Γ q).symm x)) _ z
  rw [hfun]
  exact hcd.contDiffWithinAt

end

end OAI.Geometry.ComplexBall.QuotientAtlas.Arithmetic
