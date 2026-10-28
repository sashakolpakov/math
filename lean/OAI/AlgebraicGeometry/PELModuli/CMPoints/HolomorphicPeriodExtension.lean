import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Holomorphic Period Extension -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodExtension

noncomputable section

/-! The actual local logarithm continues a central period
holomorphically, with its exact central value and exponential equation. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

theorem exists_holomorphic_period_extension
    (exponential : ∀ p, V → G p)
    (hadd : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (r : ℝ) (hr : 0 < r) (logarithm : P × V → V)
    (hlog : DifferentiableOn ℂ logarithm (B ×ˢ ball (0 : V) r))
    (hlog₀ : logarithm (p₀, 0) = 0)
    (hright : ∀ p ∈ B, ∀ y ∈ ball (0 : V) r,
      embed p (exponential p (logarithm (p, y))) = e.symm (p, y))
    (v₀ : V) (hperiod : exponential p₀ v₀ = 1)
    (hsource : ∀ p ∈ B, embed p (exponential p v₀) ∈ e.source)
    (hprojection : ∀ p ∈ B, (e (embed p (exponential p v₀))).1 = p)
    (hunit₀ : e (embed p₀ 1) = (p₀, 0))
    (hhol : DifferentiableOn ℂ (fun p => (e (embed p (exponential p v₀))).2) B) :
    ∃ (U : Set P) (period : P → V), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ B ∧
      DifferentiableOn ℂ period U ∧ period p₀ = v₀ ∧
        ∀ p ∈ U, exponential p (period p) = 1 := by
  let φ := fun p => embed p (exponential p v₀)
  let z := fun p => (e (φ p)).2
  have hz₀ : z p₀ = 0 := by
    dsimp only [z, φ]
    rw [hperiod, hunit₀]
  let U := B ∩ z ⁻¹' ball (0 : V) r
  have hU : IsOpen U := hhol.continuousOn.isOpen_inter_preimage hB isOpen_ball
  have hpU : p₀ ∈ U := ⟨hp₀, hz₀ ▸ mem_ball_self hr⟩
  let period := fun p => v₀ - logarithm (p, z p)
  have hdiff : DifferentiableOn ℂ period U := (differentiableOn_const v₀).sub
    (hlog.comp (differentiableOn_id.prodMk (hhol.mono inter_subset_left))
      (fun p hp => ⟨hp.1, hp.2⟩))
  have hcenter : period p₀ = v₀ := by
    dsimp only [period]
    rw [hz₀, hlog₀, sub_zero]
  refine ⟨U, period, hU, hpU, inter_subset_left, hdiff, hcenter, ?_⟩
  intro p hp
  have he : e (φ p) = (p, z p) := Prod.ext (hprojection p hp.1) rfl
  have hinv : e.symm (p, z p) = φ p := by rw [← he, e.left_inv (hsource p hp.1)]
  have hexp : exponential p (logarithm (p, z p)) = exponential p v₀ :=
    hembed p ((hright p hp.1 (z p) hp.2).trans hinv)
  have h := hadd p (v₀ - logarithm (p, z p)) (logarithm (p, z p))
  rw [sub_add_cancel, hexp] at h
  apply mul_right_cancel (b := exponential p v₀)
  exact h.symm.trans (one_mul _).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodExtension
