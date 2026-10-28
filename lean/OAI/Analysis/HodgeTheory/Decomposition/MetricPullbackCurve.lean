import OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricTransport
import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Metric Pullback Curve -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve.Constructions

noncomputable section

/-! A concrete curve of invertible tangent changes near the identity.
Pulling back both the tangent metric and covectors leaves their pairing fixed. -/

open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentLinearPerturbation (A : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + t • A

theorem tangentLinearPerturbation_zero (A : E →L[ℝ] E) : tangentLinearPerturbation A 0 = ContinuousLinearMap.id ℝ E := by
  simp [tangentLinearPerturbation]

theorem tangentLinearPerturbation_hasDerivAt (A : E →L[ℝ] E) : HasDerivAt (tangentLinearPerturbation A) A 0 := by
  convert!
    ((hasDerivAt_id (0 : ℝ)).smul_const A).const_add (ContinuousLinearMap.id ℝ E)
    using 1
  simp only [one_smul]

theorem tangentLinearPerturbation_eventually_equiv [CompleteSpace E] (A : E →L[ℝ] E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ L : E ≃L[ℝ] E, L.toContinuousLinearMap = tangentLinearPerturbation A t := by
  have hc : Filter.Tendsto (tangentLinearPerturbation A) (𝓝 (0 : ℝ))
      (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    have h := (tangentLinearPerturbation_hasDerivAt A).continuousAt
    change Filter.Tendsto (tangentLinearPerturbation A) (𝓝 (0 : ℝ))
      (𝓝 (tangentLinearPerturbation A 0)) at h
    rw [tangentLinearPerturbation_zero] at h
    exact h
  exact hc (ContinuousLinearEquiv.nhds (ContinuousLinearEquiv.refl ℝ E))

def bilinearMetricPullback (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  B.bilinearComp L L

theorem bilinearMetricPullback_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) (u v : E) :
    bilinearMetricPullback B L u v = B (L u) (L v) := rfl

theorem bilinearMetricPullback_id (B : E →L[ℝ] E →L[ℝ] ℝ) :
    bilinearMetricPullback B (ContinuousLinearMap.id ℝ E) = B := by ext u v; rfl

def bilinearMetricInfinitesimalPullback (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  B.bilinearComp A (ContinuousLinearMap.id ℝ E) + B.bilinearComp (ContinuousLinearMap.id ℝ E) A

theorem bilinearMetricInfinitesimalPullback_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) (u v : E) :
    bilinearMetricInfinitesimalPullback B A u v = B (A u) v + B u (A v) := rfl

theorem bilinearMetricPullback_perturbation (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) (t : ℝ) :
    bilinearMetricPullback B (tangentLinearPerturbation A t) =
      B + t • bilinearMetricInfinitesimalPullback B A + t ^ 2 • bilinearMetricPullback B A := by
  ext u v
  simp only [bilinearMetricPullback_apply, tangentLinearPerturbation, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul, smul_eq_mul,
    bilinearMetricInfinitesimalPullback_apply]
  ring

theorem bilinearMetricPullback_hasDerivAt (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    HasDerivAt (fun t => bilinearMetricPullback B (tangentLinearPerturbation A t))
      (bilinearMetricInfinitesimalPullback B A) 0 := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const (bilinearMetricInfinitesimalPullback B A)).const_add B
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (bilinearMetricPullback B A)
  have h := h1.add h2
  convert! h using 1
  · funext t
    exact bilinearMetricPullback_perturbation B A t
  · ext u v
    simp

theorem covectorPullback_hasDerivAt (n : ℕ) (A : E →L[ℝ] E) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    HasDerivAt (fun t => a.compContinuousLinearMap (tangentLinearPerturbation A t))
      (CovectorConnection.Constructions.covectorInfinitesimalAction n A a) 0 := by
  have h := (hasFDerivAt_const a (0 : ℝ)).continuousAlternatingMapCompContinuousLinearMap
    (tangentLinearPerturbation_hasDerivAt A).hasFDerivAt
  have hd := h.hasDerivAt
  simp only [tangentLinearPerturbation_zero, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hd
  exact hd

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_pullback_curve (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (A : E →L[ℝ] E) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    (fun t => BilinearFormMetric.Constructions.bilinearFormMetricPair b n (bilinearMetricPullback B (tangentLinearPerturbation A t))
      (a.compContinuousLinearMap (tangentLinearPerturbation A t))
      (c.compContinuousLinearMap (tangentLinearPerturbation A t))) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c) := by
  filter_upwards [tangentLinearPerturbation_eventually_equiv A] with t ht
  obtain ⟨L, hL⟩ := ht
  rw [← hL]
  apply BilinearMetricTransport.Constructions.bilinearFormMetricPair_transport b b n _ B _ _ hB hpos L (fun _ _ => rfl) a c
  · intro u v
    exact hB (L u) (L v)
  · intro u hu
    apply hpos
    exact fun h => hu (L.injective (h.trans L.map_zero.symm))

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve.Constructions
