import OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousFamilyPeriods

/-! # Local Period Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriodLogarithm

noncomputable section

/-! A common logarithm and the actual joint exponential construct local
kernel control and continuous period sections on open neighborhoods. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

open OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian

variable {P V X : Type} [TopologicalSpace P] [NormedAddCommGroup V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

theorem localPeriodFamily_with_open_continuation_of_logarithm
    (exponential : ∀ p, V → G p) (hzero : ∀ p, exponential p 0 = 1)
    (hadd : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (p₀ : P)
    (coordinates : ∀ p, G p → V) (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (hp₀ : p₀ ∈ B)
    (hcont : ContinuousOn (fun q : P × V => embed q.1 (exponential q.1 q.2)) (B ×ˢ Set.univ))
    (hcoordinates₀ : ∀ p ∈ B, coordinates p 1 = 0)
    (δ : ℝ) (hδ : 0 < δ) (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ closedBall (0 : V) (δ / 2)))
    (hright : ∀ p ∈ B, ∀ y ∈ closedBall (0 : V) (δ / 2),
      embed p (exponential p (logarithm (p, y))) = e.symm (p, y))
    (hleft : ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ,
      coordinates p (exponential p v) ∈ closedBall (0 : V) (δ / 2) →
        logarithm (p, coordinates p (exponential p v)) = v)
    (hprojection : ∀ p ∈ B, ∀ v, embed p (exponential p v) ∈ e.source →
      (e (embed p (exponential p v))).1 = p)
    (hunit : embed p₀ 1 ∈ e.source) (hunit₀ : e (embed p₀ 1) = (p₀, 0)) :
    ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀ ∧
      ∀ v : V, exponential p₀ v = 1 →
        ∃ (U : Set P) (period : P → V), IsOpen U ∧ p₀ ∈ U ∧
          ContinuousOn period U ∧ period p₀ = v ∧ ∀ p ∈ U, exponential p (period p) = 1 := by
  have hcentral (v : V) : ContinuousAt
      (fun q : P × V => embed q.1 (exponential q.1 q.2)) (p₀, v) :=
    hcont.continuousAt ((hB.prod isOpen_univ).mem_nhds ⟨hp₀, mem_univ v⟩)
  have H := ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.localPeriodFamily_of_logarithm G exponential hzero hadd embed hembed p₀ hcentral
    coordinates e B hB hp₀ hcoordinates₀ δ hδ logarithm hlog hright hleft hprojection hunit hunit₀
  refine ⟨H, fun v hv => ?_⟩
  have hlog₀ : logarithm (p₀, 0) = 0 := by
    have h := hleft p₀ hp₀ 0 (mem_closedBall_self (le_of_lt hδ))
    rw [hzero p₀, hcoordinates₀ p₀ hp₀] at h
    exact h (mem_closedBall_self (le_of_lt (half_pos hδ)))
  have hfixed : ContinuousOn (fun p => embed p (exponential p v)) B :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun p hp => ⟨hp, mem_univ v⟩)
  obtain ⟨U, period, hU, hpU, _, hpcont, hpzero, hpker⟩ :=
    ContinuousFamilyPeriods.exists_continuousOn_period_extension G exponential hadd embed hembed e B hB p₀ hp₀
      δ hδ logarithm hlog hlog₀ hright hprojection hunit hunit₀ v hv hfixed
  exact ⟨U, period, hU, hpU, hpcont, hpzero, hpker⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriodLogarithm
