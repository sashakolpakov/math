import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriodLogarithm
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodExtension

/-! # Holomorphic Local Period Family -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLocalPeriodFamily

noncomputable section

/-! Holomorphic local period continuation together with uniform native
kernel control, both obtained from the same actual logarithm. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

theorem localPeriodFamily_with_holomorphic_continuation_of_logarithm
    (exponential : ∀ p, V → G p) (hzero : ∀ p, exponential p 0 = 1)
    (hadd : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (p₀ : P) (coordinates : ∀ p, G p → V) (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (hp₀ : p₀ ∈ B)
    (hcont : ContinuousOn (fun q : P × V => embed q.1 (exponential q.1 q.2)) (B ×ˢ Set.univ))
    (hhol : DifferentiableOn ℂ (fun q : P × V => (e (embed q.1 (exponential q.1 q.2))).2)
      ((B ×ˢ Set.univ) ∩ (fun q : P × V => embed q.1 (exponential q.1 q.2)) ⁻¹' e.source))
    (hcoordinates₀ : ∀ p ∈ B, coordinates p 1 = 0)
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r) (hrδ : r ≤ δ / 2)
    (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ closedBall (0 : V) (δ / 2)))
    (hloghol : DifferentiableOn ℂ logarithm (B ×ˢ ball (0 : V) r))
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
          DifferentiableOn ℂ period U ∧ period p₀ = v ∧
            ∀ p ∈ U, exponential p (period p) = 1 := by
  have hdata := LocalPeriodLogarithm.localPeriodFamily_with_open_continuation_of_logarithm G exponential hzero hadd
    embed hembed p₀ coordinates e B hB hp₀ hcont hcoordinates₀ δ hδ logarithm hlog
    hright hleft hprojection hunit hunit₀
  refine ⟨hdata.1, fun v hv => ?_⟩
  have hlog₀ : logarithm (p₀, 0) = 0 := by
    have h := hleft p₀ hp₀ 0 (mem_closedBall_self (le_of_lt hδ))
    rw [hzero p₀, hcoordinates₀ p₀ hp₀] at h
    exact h (mem_closedBall_self (le_of_lt (half_pos hδ)))
  let φ := fun p => embed p (exponential p v)
  let W := B ∩ φ ⁻¹' e.source
  have hfixed : ContinuousOn φ B :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun p hp => ⟨hp, mem_univ v⟩)
  have hW : IsOpen W := hfixed.isOpen_inter_preimage hB e.open_source
  have hpW : p₀ ∈ W := ⟨hp₀, by change embed p₀ (exponential p₀ v) ∈ e.source; rw [hv]; exact hunit⟩
  have hz : DifferentiableOn ℂ (fun p => (e (φ p)).2) W :=
    hhol.comp (differentiableOn_id.prodMk (differentiableOn_const v))
      (fun p hp => ⟨⟨hp.1, mem_univ v⟩, hp.2⟩)
  obtain ⟨U, period, hU, hpU, _, hperiod, hcenter, hker⟩ :=
    HolomorphicPeriodExtension.exists_holomorphic_period_extension G exponential hadd embed hembed e W hW p₀ hpW r hr
      logarithm (hloghol.mono (Set.prod_mono inter_subset_left subset_rfl)) hlog₀
      (fun p hp y hy => hright p hp.1 y (mem_closedBall.mpr ((mem_ball.mp hy).le.trans hrδ)))
      v hv (fun p hp => hp.2) (fun p hp => hprojection p hp.1 v hp.2) hunit₀ hz
  exact ⟨U, period, hU, hpU, hperiod, hcenter, hker⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLocalPeriodFamily
