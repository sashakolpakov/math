import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicParameterIntegral
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RadialLogarithm
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Holomorphic Inverse Family -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseFamily

noncomputable section

section

/-! Holomorphic dependence of a radial integral of a differential. -/

open Set _root_.Metric
open scoped _root_.Topology ContDiff

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

theorem differentiableOn_radial_integral
    (α : P × V → V →L[ℂ] V) (U : Set P) (hU : IsOpen U) (r : ℝ)
    (hα : ContDiffOn ℂ 2 α (U ×ˢ ball 0 r)) :
    DifferentiableOn ℂ (fun q : P × V => ∫ t : ℝ in 0..1, α (q.1, t • q.2) q.2)
      (U ×ˢ ball 0 r) := by
  let k : (P × V) × ℂ → P × V := fun z => (z.1.1, z.2 • z.1.2)
  have hk : ContDiff ℂ 2 k := by fun_prop
  let D : Set ((P × V) × ℂ) := k ⁻¹' (U ×ˢ ball 0 r)
  have hD : IsOpen D := (hU.prod isOpen_ball).preimage hk.continuous
  let f : (P × V) × ℂ → V := fun z => α (k z) z.1.2
  have hf : ContDiffOn ℂ 2 f D :=
    (hα.comp hk.contDiffOn (fun _ h => h)).clm_apply contDiffOn_fst.snd
  have hinside : ∀ q ∈ U ×ˢ ball (0 : V) r, ∀ t ∈ uIcc (0 : ℝ) 1,
      (q, (t : ℂ)) ∈ D := by
    intro q hq t ht
    have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [uIcc_of_le zero_le_one, mem_Icc] using ht
    refine ⟨hq.1, ?_⟩
    change (t : ℂ) • q.2 ∈ ball (0 : V) r
    rw [mem_ball, dist_zero_right, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht'.1]
    exact (mul_le_of_le_one_left (norm_nonneg q.2) ht'.2).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hq.2)
  have h := HolomorphicParameterIntegral.differentiableOn_holomorphic_parameter_integral f D hD hf
    (U ×ˢ ball (0 : V) r) (hU.prod isOpen_ball) 0 1 hinside
  have hscalar (t : ℝ) (v : V) : (t : ℂ) • v = t • v :=
    IsScalarTower.algebraMap_smul ℂ t v
  simpa only [f, k, hscalar] using h

end

/-! A continuous family of actual local inverses is holomorphic when
its inverse vertical differential is holomorphic in the base and target.
The proof uses the radial integral identity, without assuming holomorphic
dependence of the original exponential on the base. -/

open Set _root_.Metric
open scoped _root_.Topology ContDiff

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

theorem differentiableOn_inverse_family_of_vertical_differential
    (f logarithm : P × V → V) (D : P × V → V ≃L[ℂ] V)
    (U : Set P) (hU : IsOpen U) (r : ℝ)
    (hlog : ContinuousOn logarithm (U ×ˢ ball 0 r))
    (hder : ∀ p ∈ U, ∀ y ∈ ball 0 r,
      HasFDerivAt (fun v => f (p, v))
        ((D (p, y)).restrictScalars ℝ).toContinuousLinearMap (logarithm (p, y)))
    (hinv : ∀ p ∈ U, ∀ y ∈ ball 0 r, f (p, logarithm (p, y)) = y)
    (hzero : ∀ p ∈ U, logarithm (p, 0) = 0)
    (hD : ContDiffOn ℂ 2 (fun q => (D q).symm.toContinuousLinearMap) (U ×ˢ ball 0 r)) :
    DifferentiableOn ℂ logarithm (U ×ˢ ball 0 r) := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  apply (differentiableOn_radial_integral (fun q => (D q).symm.toContinuousLinearMap) U hU r hD).congr
  intro q hq
  have hlogq : ContinuousOn (fun y => logarithm (q.1, y)) (ball 0 r) :=
    hlog.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨hq.1, hy⟩)
  have hDq : ContinuousOn (fun y => (D (q.1, y)).symm.toContinuousLinearMap) (ball 0 r) :=
    hD.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => ⟨hq.1, hy⟩)
  have hDr : ContinuousOn
      (fun y => ((D (q.1, y)).restrictScalars ℝ).symm.toContinuousLinearMap) (ball 0 r) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).continuous.comp_continuousOn hDq
  exact RadialLogarithm.local_inverse_eq_radial_integral (fun v => f (q.1, v)) (fun y => logarithm (q.1, y))
    (fun y => (D (q.1, y)).restrictScalars ℝ) r hlogq (hder q.1 hq.1)
    (hinv q.1 hq.1) (hzero q.1 hq.1) hDr q.2 hq.2

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseFamily
