import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CircleIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CauchyKernel

/-! # Double Cauchy -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Integral

/-! A bounded iterated circle integral on the product boundary, with
joint smooth dependence on both interior Cauchy parameters. -/

open scoped Classical ContDiff
open _root_.Complex Set _root_.Metric
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CircleIntegral.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CauchyKernel.CM

section Curry

variable (T U : Type*) [TopologicalSpace T] [CompactSpace T]
  [TopologicalSpace U] [CompactSpace U]

def curryLinear : C(T × U, ℂ) →ₗ[ℂ] C(T, C(U, ℂ)) where
  toFun := ContinuousMap.curry
  map_add' f g := by ext x y; rfl
  map_smul' a f := by ext x y; rfl

def curryContinuous : C(T × U, ℂ) →L[ℂ] C(T, C(U, ℂ)) :=
  (curryLinear T U).mkContinuous 1 (by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro y
    exact f.norm_coe_le_norm (x, y))

end Curry

abbrev Torus (c : ℂ × ℂ) (r : ℝ × ℝ) := CircleIntegral.CM.Boundary c.1 r.1 × CircleIntegral.CM.Boundary c.2 r.2

def coordinate₁ (c : ℂ × ℂ) (r : ℝ × ℝ) : C(Torus c r, ℂ) :=
  ⟨fun t => t.1.val, continuous_subtype_val.comp continuous_fst⟩

def coordinate₂ (c : ℂ × ℂ) (r : ℝ × ℝ) : C(Torus c r, ℂ) :=
  ⟨fun t => t.2.val, continuous_subtype_val.comp continuous_snd⟩

def doubleIntegral (c : ℂ × ℂ) (r : ℝ × ℝ) (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    C(Torus c r, ℂ) →L[ℂ] ℂ :=
  (CircleIntegral.CM.integral c.1 r.1 hr.1).comp
    (((CircleIntegral.CM.integral c.2 r.2 hr.2).compLeftContinuous ℂ (CircleIntegral.CM.Boundary c.1 r.1)).comp
      (curryContinuous (CircleIntegral.CM.Boundary c.1 r.1) (CircleIntegral.CM.Boundary c.2 r.2)))

@[simp] theorem doubleIntegral_apply (c : ℂ × ℂ) (r : ℝ × ℝ)
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (F : C(Torus c r, ℂ)) :
    doubleIntegral c r hr F = CircleIntegral.CM.integral c.1 r.1 hr.1
      ((CircleIntegral.CM.integral c.2 r.2 hr.2).compLeftContinuous ℂ (CircleIntegral.CM.Boundary c.1 r.1) F.curry) := rfl

def kernel (c : ℂ × ℂ) (r : ℝ × ℝ) (F : C(Torus c r, ℂ)) (z : ℂ × ℂ) :
    C(Torus c r, ℂ) :=
  Ring.inverse (CauchyKernel.CM.denominator (coordinate₁ c r) z.1) *
    Ring.inverse (CauchyKernel.CM.denominator (coordinate₂ c r) z.2) * F

theorem coordinates_ne (c : ℂ × ℂ) (r : ℝ × ℝ) (z : ℂ × ℂ)
    (hz : z.1 ∈ ball c.1 r.1 ∧ z.2 ∈ ball c.2 r.2) :
    (∀ t, coordinate₁ c r t ≠ z.1) ∧ (∀ t, coordinate₂ c r t ≠ z.2) := by
  constructor
  · intro t h
    have ht := t.1.property
    change dist (coordinate₁ c r t) c.1 = r.1 at ht
    rw [h] at ht
    exact (ne_of_lt hz.1) ht
  · intro t h
    have ht := t.2.property
    change dist (coordinate₂ c r t) c.2 = r.2 at ht
    rw [h] at ht
    exact (ne_of_lt hz.2) ht

theorem kernel_apply (c : ℂ × ℂ) (r : ℝ × ℝ) (F : C(Torus c r, ℂ)) (z : ℂ × ℂ)
    (hz : z.1 ∈ ball c.1 r.1 ∧ z.2 ∈ ball c.2 r.2) (t : Torus c r) :
    kernel c r F z t = ((t.1 : ℂ) - z.1)⁻¹ * ((t.2 : ℂ) - z.2)⁻¹ * F t := by
  obtain ⟨h₁, h₂⟩ := coordinates_ne c r z hz
  simp only [kernel, ContinuousMap.mul_apply,
    CauchyKernel.CM.inverse_denominator_apply _ _ h₁, CauchyKernel.CM.inverse_denominator_apply _ _ h₂]
  rfl

theorem doubleCauchy_contDiffAt (c : ℂ × ℂ) (r : ℝ × ℝ)
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (F : C(Torus c r, ℂ)) (z : ℂ × ℂ)
    (hz : z.1 ∈ ball c.1 r.1 ∧ z.2 ∈ ball c.2 r.2) :
    ContDiffAt ℂ ∞ (fun w => doubleIntegral c r hr (kernel c r F w)) z := by
  obtain ⟨h₁, h₂⟩ := coordinates_ne c r z hz
  exact CauchyKernel.CM.double_kernel_contDiffAt (coordinate₁ c r) (coordinate₂ c r) F
    (doubleIntegral c r hr) z h₁ h₂

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Integral

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Formula

/-! The two-variable Cauchy formula follows by two applications of the
ordinary one-variable theorem. No derivative-continuity assumption is used. -/

open scoped Classical ContDiff
open _root_.Complex Set _root_.Metric
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CircleIntegral.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Integral

def closedPolydisc (c : ℂ × ℂ) (r : ℝ × ℝ) : Set (ℂ × ℂ) :=
  closedBall c.1 r.1 ×ˢ closedBall c.2 r.2

def openPolydisc (c : ℂ × ℂ) (r : ℝ × ℝ) : Set (ℂ × ℂ) :=
  ball c.1 r.1 ×ˢ ball c.2 r.2

theorem doubleCauchy_eq (c : ℂ × ℂ) (r : ℝ × ℝ)
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (f : ℂ × ℂ → ℂ)
    (hd : ∀ w ∈ closedPolydisc c r, DifferentiableAt ℂ f w)
    (F : C(Integral.Torus c r, ℂ)) (hF : ∀ t, F t = f (t.1, t.2))
    (z : ℂ × ℂ) (hz : z ∈ openPolydisc c r) :
    Integral.doubleIntegral c r hr (Integral.kernel c r F z) = (2 * Real.pi * I : ℂ) ^ 2 * f z := by
  let k : ℂ := 2 * Real.pi * I
  have hd₂ (u : ℂ) (hu : u ∈ closedBall c.1 r.1) :
      DifferentiableOn ℂ (fun v => f (u, v)) (closedBall c.2 r.2) := by
    intro v hv
    exact ((hd (u, v) ⟨hu, hv⟩).comp v
      ((differentiableAt_const u).prodMk differentiableAt_id)).differentiableWithinAt
  have hd₁ : DifferentiableOn ℂ (fun u => f (u, z.2)) (closedBall c.1 r.1) := by
    intro u hu
    exact ((hd (u, z.2) ⟨hu, ball_subset_closedBall hz.2⟩).comp u
      (differentiableAt_id.prodMk (differentiableAt_const z.2))).differentiableWithinAt
  have inner (u : CircleIntegral.CM.Boundary c.1 r.1) :
      CircleIntegral.CM.integral c.2 r.2 hr.2 ((Integral.kernel c r F z).curry u) =
        k * (((u : ℂ) - z.1)⁻¹ * f (u, z.2)) := by
    rw [CircleIntegral.CM.integral_eq_of_boundary c.2 r.2 hr.2 _
      (fun v => ((u : ℂ) - z.1)⁻¹ * ((v - z.2)⁻¹ * f (u, v))) (by
        intro v
        rw [ContinuousMap.curry_apply, Integral.kernel_apply c r F z hz, hF]
        ring)]
    rw [circleIntegral.integral_const_mul]
    have hc := (hd₂ u (sphere_subset_closedBall u.property)).circleIntegral_sub_inv_smul hz.2
    change (∮ v in C(c.2, r.2), (v - z.2)⁻¹ * f (u, v)) = k * f (u, z.2) at hc
    rw [hc]
    ring
  rw [Integral.doubleIntegral_apply, CircleIntegral.CM.integral_eq_of_boundary c.1 r.1 hr.1 _
    (fun u => k * ((u - z.1)⁻¹ * f (u, z.2))) (by
      intro u
      exact inner u)]
  rw [circleIntegral.integral_const_mul]
  have hc := hd₁.circleIntegral_sub_inv_smul hz.1
  change (∮ u in C(c.1, r.1), (u - z.1)⁻¹ * f (u, z.2)) = k * f z at hc
  rw [hc]
  ring

/-- Restrict the actual function to the product boundary. Continuity
comes from differentiability on a neighborhood of the closed polydisc. -/
def boundaryValues (c : ℂ × ℂ) (r : ℝ × ℝ) (f : ℂ × ℂ → ℂ)
    (hd : ∀ w ∈ closedPolydisc c r, DifferentiableAt ℂ f w) : C(Integral.Torus c r, ℂ) where
  toFun t := f (t.1, t.2)
  continuous_toFun := by
    have hc : ContinuousOn f (closedPolydisc c r) :=
      fun w hw => (hd w hw).continuousAt.continuousWithinAt
    apply hc.comp_continuous
    · exact (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    · intro t
      exact ⟨sphere_subset_closedBall t.1.property, sphere_subset_closedBall t.2.property⟩

/-- On the interior, the holomorphic function agrees with a smooth
bounded-operator Cauchy integral. This proves joint smoothness. -/
theorem contDiffAt_of_differentiable_polydisc
    (c : ℂ × ℂ) (r : ℝ × ℝ) (hr : 0 ≤ r.1 ∧ 0 ≤ r.2)
    (f : ℂ × ℂ → ℂ) (hd : ∀ w ∈ closedPolydisc c r, DifferentiableAt ℂ f w)
    (z : ℂ × ℂ) (hz : z ∈ openPolydisc c r) : ContDiffAt ℂ ∞ f z := by
  let F := boundaryValues c r f hd
  let k : ℂ := (2 * Real.pi * I : ℂ) ^ 2
  have hk : k ≠ 0 := pow_ne_zero 2 Complex.two_pi_I_ne_zero
  have heq : (fun w => k⁻¹ * Integral.doubleIntegral c r hr (Integral.kernel c r F w)) =ᶠ[nhds z] f := by
    apply Filter.eventuallyEq_of_mem ((isOpen_ball.prod isOpen_ball).mem_nhds hz)
    intro w hw
    change k⁻¹ * Integral.doubleIntegral c r hr (Integral.kernel c r F w) = f w
    rw [doubleCauchy_eq c r hr f hd F (fun _ => rfl) w hw]
    exact inv_mul_cancel_left₀ hk (f w)
  have hs : ContDiffAt ℂ ∞
      (fun w => k⁻¹ * Integral.doubleIntegral c r hr (Integral.kernel c r F w)) z :=
    contDiffAt_const.mul (Integral.doubleCauchy_contDiffAt c r hr F z hz)
  exact hs.congr_of_eventuallyEq heq.symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Formula

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.HolomorphicRegularity

/-! Holomorphic maps from a complex two-dimensional coordinate chart are
smooth. Joint scalar regularity comes from the proved double Cauchy formula;
finite-dimensional targets are handled by their actual linear coordinates. -/

open scoped Classical ContDiff _root_.Topology
open _root_.Complex Set _root_.Metric Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.Formula

theorem scalar_contDiffAt_of_eventually_differentiableAt
    {f : ℂ × ℂ → ℂ} {z : ℂ × ℂ}
    (h : ∀ᶠ w in nhds z, DifferentiableAt ℂ f w) : ContDiffAt ℂ ∞ f z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  have hhalf : 0 < ε / 2 := half_pos hε
  have hd : ∀ w ∈ Formula.closedPolydisc z (ε / 2, ε / 2), DifferentiableAt ℂ f w := by
    intro w hw
    apply hball
    change dist w z < ε
    rw [Prod.dist_eq]
    exact max_lt ((show dist w.1 z.1 ≤ ε / 2 from hw.1).trans_lt (half_lt_self hε))
      ((show dist w.2 z.2 ≤ ε / 2 from hw.2).trans_lt (half_lt_self hε))
  exact Formula.contDiffAt_of_differentiable_polydisc z (ε / 2, ε / 2)
    ⟨hhalf.le, hhalf.le⟩ f hd z ⟨mem_ball_self hhalf, mem_ball_self hhalf⟩

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/-- Linear coordinates reduce a finite-dimensional target to the scalar
two-variable regularity theorem. -/
theorem contDiffAt_of_eventually_differentiableAt
    {f : ℂ × ℂ → W} {z : ℂ × ℂ}
    (h : ∀ᶠ w in nhds z, DifferentiableAt ℂ f w) : ContDiffAt ℂ ∞ f z := by
  let e := (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have hc : ContDiffAt ℂ ∞ (fun w => e (f w)) z := by
    apply contDiffAt_pi.mpr
    intro i
    apply scalar_contDiffAt_of_eventually_differentiableAt
    filter_upwards [h] with w hw
    exact (show (Fin (Module.finrank ℂ W) → ℂ) →L[ℂ] ℂ from
      ContinuousLinearMap.proj i).differentiableAt.comp w (e.differentiableAt.comp w hw)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
    using e.symm.contDiff.contDiffAt.comp z hc

/-- The same statement in the source ball's literal `Fin 2 → ℂ` coordinates. -/
theorem finTwo_contDiffAt_of_eventually_differentiableAt
    {f : (Fin 2 → ℂ) → W} {z : Fin 2 → ℂ}
    (h : ∀ᶠ w in nhds z, DifferentiableAt ℂ f w) : ContDiffAt ℂ ∞ f z := by
  let e := (LinearEquiv.finTwoArrow ℂ ℂ).toContinuousLinearEquiv
  have ht : Tendsto e.symm (nhds (e z)) (nhds z) := by
    simpa only [ContinuousAt, ContinuousLinearEquiv.symm_apply_apply] using
      (e.symm.continuousAt : ContinuousAt e.symm (e z))
  have hg : ∀ᶠ w in nhds (e z), DifferentiableAt ℂ (fun u => f (e.symm u)) w := by
    filter_upwards [ht.eventually h] with w hw
    exact hw.comp w e.symm.differentiableAt
  have hs := contDiffAt_of_eventually_differentiableAt hg
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
    using hs.comp z e.contDiff.contDiffAt

/-- Regularity is unchanged by a continuous linear identification of
the domain with the ball's two-dimensional model. -/
theorem equiv_finTwo_contDiffAt_of_eventually_differentiableAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (e : V ≃L[ℂ] (Fin 2 → ℂ)) {f : V → W} {z : V}
    (h : ∀ᶠ w in nhds z, DifferentiableAt ℂ f w) : ContDiffAt ℂ ∞ f z := by
  have ht : Tendsto e.symm (nhds (e z)) (nhds z) := by
    simpa only [ContinuousAt, ContinuousLinearEquiv.symm_apply_apply] using
      (e.symm.continuousAt : ContinuousAt e.symm (e z))
  have hg : ∀ᶠ w in nhds (e z), DifferentiableAt ℂ (fun u => f (e.symm u)) w := by
    filter_upwards [ht.eventually h] with w hw
    exact hw.comp w e.symm.differentiableAt
  have hs := finTwo_contDiffAt_of_eventually_differentiableAt hg
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
    using hs.comp z e.contDiff.contDiffAt

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.HolomorphicRegularity

end

end OAI
