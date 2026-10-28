import OAI.AlgebraicGeometry.Comparison.Betti.CauchyAnnulusInvariance
import OAI.AlgebraicGeometry.Comparison.Betti.ParametricCauchyIntegral

/-! # Inverted Cauchy Circle -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InvertedCauchyCircle.Dolbeault

noncomputable section

section

/-! The inner Cauchy integral in the inverse coordinate extends
holomorphically through infinity, with value zero there. -/

open _root_.Complex Set _root_.Metric
open scoped _root_.Topology

def invertedUnitCauchyTransform (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ w in C(0, 1), f w * (u / (1 - w * u))

theorem invertedUnitCauchyTransform_zero (f : ℂ → ℂ) : invertedUnitCauchyTransform f 0 = 0 := by
  simp [invertedUnitCauchyTransform, circleIntegral]

theorem invertedUnitCauchyTransform_holomorphic {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere 0 1)) {u : ℂ} (hu : ‖u‖ < 1) :
    DifferentiableAt ℂ (invertedUnitCauchyTransform f) u := by
  let D : ℂ × ℂ → ℂ := fun p => 1 - p.2 * p.1
  have hD : Differentiable ℂ D := (differentiable_const (1 : ℂ)).sub
    (differentiable_snd.mul differentiable_fst)
  let W : Set (ℂ × ℂ) := D ⁻¹' ({0} : Set ℂ)ᶜ
  have hW : IsOpen W := isClosed_singleton.isOpen_compl.preimage hD.continuous
  have hG : DifferentiableOn ℂ (fun p : ℂ × ℂ => p.1 / D p) W := by
    have hfst : DifferentiableOn ℂ (Prod.fst : ℂ × ℂ → ℂ) W := differentiable_fst.differentiableOn
    have hden : DifferentiableOn ℂ D W := hD.differentiableOn
    simpa only [div_eq_mul_inv] using hfst.fun_mul (hden.fun_inv (fun p (hp : p ∈ W) => hp))
  have hsub : ball (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1 ⊆ W := by
    intro p hp hzero
    have hw : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2
    have hu' : ‖p.1‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hp.1
    have he : (1 : ℂ) = p.2 * p.1 := sub_eq_zero.mp hzero
    have hn := congrArg norm he
    rw [norm_one, norm_mul, hw, one_mul] at hn
    exact (ne_of_lt hu') hn.symm
  have h := ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral hW hG
    isOpen_ball (show u ∈ ball 0 1 by simpa only [mem_ball, dist_zero_right] using hu)
    (by norm_num : 0 ≤ (1 : ℝ)) hsub hf
  exact h.const_mul _

theorem invertedCauchyKernel_identity (w : ℂ) {u : ℂ} (hu : u ≠ 0) :
    u / (1 - w * u) = -(w - u⁻¹)⁻¹ := by
  have he : w - u⁻¹ = -(1 - w * u) / u := by
    field_simp
    ring
  rw [he, inv_div, div_neg, neg_neg]

theorem invertedUnitCauchyTransform_eq (f : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    invertedUnitCauchyTransform f u = -CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f 1 u⁻¹ := by
  have he : (∮ w in C(0, 1), f w * (u / (1 - w * u))) =
      (-1 : ℂ) * ∮ w in C(0, 1), f w / (w - u⁻¹) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (by norm_num : 0 ≤ (1 : ℝ))
    intro w _
    change f w * (u / (1 - w * u)) = -1 * (f w / (w - u⁻¹))
    rw [invertedCauchyKernel_identity w hu]
    simp only [div_eq_mul_inv]
    ring
  unfold invertedUnitCauchyTransform CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform
  rw [he]
  ring

end

/-! Holomorphic parameter dependence of the inner contour integral
in the inverse coordinate, including the point at infinity. -/

open _root_.Complex Set _root_.Metric
open scoped _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def invertedUnitCauchyFamily (G : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  invertedUnitCauchyTransform (fun w => G (q.1, w)) q.2

theorem invertedUnitCauchyFamily_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    DifferentiableOn ℂ (invertedUnitCauchyFamily G) (S ×ˢ ball (0 : ℂ) 1) := by
  let A : (P × ℂ) × ℂ → P × ℂ := fun p => (p.1.1, p.2)
  let D : (P × ℂ) × ℂ → ℂ := fun p => 1 - p.2 * p.1.2
  have hA : Differentiable ℂ A := differentiable_fst.fst.prodMk differentiable_snd
  have hD : Differentiable ℂ D := (differentiable_const (1 : ℂ)).sub
    (differentiable_snd.mul differentiable_fst.snd)
  let W := A ⁻¹' (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) ∩ D ⁻¹' ({0} : Set ℂ)ᶜ
  have hW : IsOpen W := ((hS.prod PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen).preimage hA.continuous).inter
    (isClosed_singleton.isOpen_compl.preimage hD.continuous)
  have hGA : DifferentiableOn ℂ (fun p => G (A p)) W :=
    hG.comp hA.differentiableOn (fun _ hp => hp.1)
  have hnum : DifferentiableOn ℂ (fun p : (P × ℂ) × ℂ => p.1.2) W :=
    differentiable_fst.snd.differentiableOn
  have hden : DifferentiableOn ℂ D W := hD.differentiableOn
  have hF : DifferentiableOn ℂ (fun p : (P × ℂ) × ℂ => G (A p) * (p.1.2 / D p)) W := by
    simpa only [div_eq_mul_inv] using hGA.fun_mul
      (hnum.fun_mul (hden.fun_inv (fun p (hp : p ∈ W) => hp.2)))
  have hbound : (S ×ˢ ball (0 : ℂ) 1) ×ˢ sphere (0 : ℂ) 1 ⊆ W := by
    intro p hp
    have hw : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2
    refine ⟨⟨hp.1.1, norm_pos_iff.mp (hw.symm ▸ (by norm_num : 0 < (1 : ℝ)))⟩, ?_⟩
    intro hz
    have hu : ‖p.1.2‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hp.1.2
    have he : (1 : ℂ) = p.2 * p.1.2 := sub_eq_zero.mp hz
    have hn := congrArg norm he
    rw [norm_one, norm_mul, hw, one_mul] at hn
    exact (ne_of_lt hu) hn.symm
  intro q hq
  have h := ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral hW hF
    (hS.prod isOpen_ball) hq (by norm_num : 0 ≤ (1 : ℝ)) hbound
    (w := fun _ => 1) continuousOn_const
  have h' : DifferentiableAt ℂ (fun p : P × ℂ =>
      ∮ w in C(0, 1), G (p.1, w) * (p.2 / (1 - w * p.2))) q := by
    simpa only [one_mul, A, D] using h
  exact (h'.const_mul (2 * Real.pi * I : ℂ)⁻¹).differentiableWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.InvertedCauchyCircle.Dolbeault
