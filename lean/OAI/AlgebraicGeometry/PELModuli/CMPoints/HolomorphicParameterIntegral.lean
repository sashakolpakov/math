import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Holomorphic Parameter Integral -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicParameterIntegral

noncomputable section

/-! Integrating a jointly holomorphic function over a fixed real interval
gives a holomorphic function of the remaining complex parameters. -/

open Set Filter _root_.Metric
open scoped _root_.Topology ContDiff

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem differentiableOn_holomorphic_parameter_integral
    (f : P × ℂ → V) (D : Set (P × ℂ)) (hD : IsOpen D)
    (hf : ContDiffOn ℂ 2 f D)
    (U : Set P) (hU : IsOpen U) (a b : ℝ)
    (hinside : ∀ p ∈ U, ∀ t ∈ uIcc a b, (p, (t : ℂ)) ∈ D) :
    DifferentiableOn ℂ (fun p => ∫ t : ℝ in a..b, f (p, (t : ℂ))) U := by
  let e : P × ℝ → P × ℂ := fun q => (q.1, (q.2 : ℂ))
  have he : Continuous e := continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd)
  have hmaps : MapsTo e (U ×ˢ uIcc a b) D := fun q hq => hinside q.1 hq.1 q.2 hq.2
  let F : P → ℝ → V := fun p t => f (p, (t : ℂ))
  let G : P → ℝ → P →L[ℂ] V := fun p t =>
    (fderiv ℂ f (p, (t : ℂ))).comp (ContinuousLinearMap.inl ℂ P ℂ)
  have hF : ContinuousOn (Function.uncurry F) (U ×ˢ uIcc a b) :=
    hf.continuousOn.comp he.continuousOn hmaps
  have hG : ContinuousOn (Function.uncurry G) (U ×ˢ uIcc a b) :=
    ((hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).comp he.continuousOn hmaps).clm_comp
      continuousOn_const
  have hder : ∀ p ∈ U, ∀ t ∈ uIcc a b, HasFDerivAt (fun q => F q t) (G p t) p := by
    intro p hp t ht
    have hpoint := hinside p hp t ht
    have h := (hf.contDiffAt (hD.mem_nhds hpoint)).differentiableAt (by norm_num)
    exact h.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (t : ℂ) p))
  intro p hp
  exact (HolomorphicIntervalIntegral.hasFDerivAt_intervalIntegral_of_compact F G U hU a b hF hG hder p hp).differentiableAt.differentiableWithinAt

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicParameterIntegral
