import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Finite Removability On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRemovabilityOn.Constructions.FiniteRemovability

noncomputable section

/-!
# RiemannProjectivity: bounded extension across finitely many branch points

Riemann's one-variable removable singularity theorem fills every point of a
finite exceptional set. The resulting function is holomorphic on the whole
open domain, agrees with the original function off that set, and retains
the same norm bound.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

attribute [local instance] Classical.propDecidable

def fill (f : ℂ → ℂ) (K : Set ℂ) (z : ℂ) : ℂ :=
  if z ∈ K then limUnder (𝓝[≠] z) f else f z

theorem fill_eq {f : ℂ → ℂ} {K : Set ℂ} {z : ℂ} (hz : z ∉ K) : fill f K z = f z :=
  ite_eq_right hz

theorem differentiableOn_fill_of_interior {f : ℂ → ℂ} {K U : Set ℂ} (hK : K.Finite)
    (hU : ∀ x ∈ U ∩ K, U ∈ 𝓝 x) (hf : DifferentiableOn ℂ f (U \ K)) {C : ℝ}
    (hbound : ∀ z ∈ U \ K, ‖f z‖ ≤ C) : DifferentiableOn ℂ (fill f K) U := by
  classical
  intro x hx
  by_cases hxK : x ∈ K
  · let A := U ∩ (K \ {x})ᶜ
    have hA : A ∈ 𝓝 x := inter_mem (hU x ⟨hx, hxK⟩)
      ((hK.sdiff : (K \ {x}).Finite).isClosed.isOpen_compl.mem_nhds (by simp))
    have hsub : A \ {x} ⊆ U \ K := by
      intro z hz
      refine ⟨hz.1.1, fun hzK => hz.1.2 ⟨hzK, hz.2⟩⟩
    have hbounded : BddAbove (norm ∘ f '' (A \ {x})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hbound z (hsub hz)
    have hd := differentiableOn_update_limUnder_of_bddAbove hA
      (hf.mono hsub) hbounded
    have heq : fill f K =ᶠ[𝓝 x] Function.update f x (limUnder (𝓝[≠] x) f) := by
      filter_upwards [hA] with z hz
      by_cases hzx : z = x
      · subst z
        simp only [fill, hxK, ite_eq_left, Function.update_self]
      · have hzK : z ∉ K := fun h => hz.2 ⟨h, hzx⟩
        rw [fill_eq hzK, Function.update_of_ne hzx]
    exact ((hd.differentiableAt hA).congr_of_eventuallyEq heq).differentiableWithinAt
  · have hcomp : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds hxK
    have hUK : U \ K ∈ 𝓝[U] x :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hcomp)
    have heq : fill f K =ᶠ[𝓝 x] f := by
      filter_upwards [hcomp] with z hz
      exact fill_eq hz
    exact ((hf x ⟨hx, hxK⟩).mono_of_mem_nhdsWithin hUK).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) (fill_eq hxK)

theorem differentiableOn_fill {f : ℂ → ℂ} {K U : Set ℂ} (hK : K.Finite)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ K)) {C : ℝ}
    (hbound : ∀ z ∈ U \ K, ‖f z‖ ≤ C) : DifferentiableOn ℂ (fill f K) U :=
  differentiableOn_fill_of_interior hK (fun _ hx => hU.mem_nhds hx.1) hf hbound

theorem norm_fill_le {f : ℂ → ℂ} {K U : Set ℂ} (hK : K.Finite)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ K)) {C : ℝ}
    (hbound : ∀ z ∈ U \ K, ‖f z‖ ≤ C) {x : ℂ} (hx : x ∈ U) : ‖fill f K x‖ ≤ C := by
  have hd := differentiableOn_fill hK hU hf hbound
  have hcont := (hd.differentiableAt (hU.mem_nhds hx)).continuousAt.norm
  apply le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ)))
  have havoid : (K \ {x})ᶜ ∈ 𝓝 x :=
    (hK.sdiff : (K \ {x}).Finite).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx),
    mem_nhdsWithin_of_mem_nhds havoid, self_mem_nhdsWithin] with z hz hzK hzx
  have hn : z ∉ K := fun h => hzK ⟨h, hzx⟩
  rw [fill_eq hn]
  exact hbound z ⟨hz, hn⟩

theorem exists_bounded_extension {f : ℂ → ℂ} {K U : Set ℂ} (hK : K.Finite)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ K)) {C : ℝ}
    (hbound : ∀ z ∈ U \ K, ‖f z‖ ≤ C) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn g f (U \ K) ∧ ∀ z ∈ U, ‖g z‖ ≤ C :=
  ⟨fill f K, differentiableOn_fill hK hU hf hbound,
    fun _ hz => fill_eq hz.2, fun _ hz => norm_fill_le hK hU hf hbound hz⟩

/-- The usual Cauchy formula remains valid at ordinary points of a disk
when finitely many interior singularities are bounded and removable. -/
theorem cauchy_formula_fill {f : ℂ → ℂ} {K : Set ℂ} (hK : K.Finite)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hinterior : K ⊆ ball c R)
    (hf : DifferentiableOn ℂ f (closedBall c R \ K)) {C : ℝ}
    (hbound : ∀ z ∈ closedBall c R \ K, ‖f z‖ ≤ C)
    {w : ℂ} (hw : w ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R), (z - w)⁻¹ * f z) = fill f K w := by
  have hd := differentiableOn_fill_of_interior hK
    (fun x hx => mem_of_superset (isOpen_ball.mem_nhds (hinterior hx.2)) ball_subset_closedBall)
    hf hbound
  have hC := hd.circleIntegral_sub_inv_smul hw
  simp only [smul_eq_mul] at hC
  have heq : (∮ z in C(c, R), (z - w)⁻¹ * f z) =
      (∮ z in C(c, R), (z - w)⁻¹ * fill f K z) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzK : z ∉ K := fun hk =>
      (ne_of_lt (mem_ball.mp (hinterior hk))) (mem_sphere.mp hz)
    change (z - w)⁻¹ * f z = (z - w)⁻¹ * fill f K z
    rw [fill_eq hzK]
  rw [heq, hC, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

theorem cauchy_formula_off_finite {f : ℂ → ℂ} {K : Set ℂ} (hK : K.Finite)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hinterior : K ⊆ ball c R)
    (hf : DifferentiableOn ℂ f (closedBall c R \ K)) {C : ℝ}
    (hbound : ∀ z ∈ closedBall c R \ K, ‖f z‖ ≤ C)
    {w : ℂ} (hw : w ∈ ball c R) (hwK : w ∉ K) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R), (z - w)⁻¹ * f z) = f w :=
  (cauchy_formula_fill hK hR hinterior hf hbound hw).trans (fill_eq hwK)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRemovabilityOn.Constructions.FiniteRemovability
