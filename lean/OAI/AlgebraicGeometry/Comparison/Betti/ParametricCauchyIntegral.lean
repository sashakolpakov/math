import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt

/-! # Parametric Cauchy Integral -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParametricCauchyIntegral.Weierstrass

noncomputable section

/-! The actual Cauchy contour integral depends holomorphically on both its
external parameters and the interior evaluation point. -/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

def parametricCauchyIntegral {E : Type*} (G : E × ℂ → ℂ) (c : ℂ) (R : ℝ) (p : E × ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), G (p.1, z) / (z - p.2)

theorem differentiableAt_parametricCauchyIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {G : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hG : DifferentiableOn ℂ G W)
    {U : Set E} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUW : U ×ˢ sphere c R ⊆ W) {x : E} (hx : x ∈ U) {w : ℂ} (hw : w ∈ ball c R) :
    DifferentiableAt ℂ (parametricCauchyIntegral G c R) (x, w) := by
  let T : (E × ℂ) × ℂ → E × ℂ := fun p => (p.1.1, p.2)
  let D : (E × ℂ) × ℂ → ℂ := fun p => p.2 - p.1.2
  have hT : Differentiable ℂ T := differentiable_fst.fst.prodMk differentiable_snd
  have hD : Differentiable ℂ D := differentiable_snd.sub differentiable_fst.snd
  let V := T ⁻¹' W ∩ D ⁻¹' ({0} : Set ℂ)ᶜ
  have hV : IsOpen V := (hW.preimage hT.continuous).inter
    (isClosed_singleton.isOpen_compl.preimage hD.continuous)
  have hGT : DifferentiableOn ℂ (fun p => G (T p)) V :=
    hG.comp hT.differentiableOn (fun p (hp : p ∈ V) => hp.1)
  have hF : DifferentiableOn ℂ (fun p => G (T p) / D p) V :=
    by simpa only [div_eq_mul_inv] using
      hGT.fun_mul (hD.differentiableOn.fun_inv (fun p (hp : p ∈ V) => hp.2))
  have hbound : (U ×ˢ ball c R) ×ˢ sphere c R ⊆ V := by
    intro p hp
    refine ⟨hUW ⟨hp.1.1, hp.2⟩, ?_⟩
    change p.2 - p.1.2 ≠ 0
    intro h
    have he := sub_eq_zero.mp h
    exact (ne_of_lt (mem_ball.mp hp.1.2)) (he ▸ mem_sphere.mp hp.2)
  have h := ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral
    hV hF (hU.prod isOpen_ball) (show (x, w) ∈ U ×ˢ ball c R from ⟨hx, hw⟩) hR hbound
    (w := fun _ => 1) continuousOn_const
  have h' : DifferentiableAt ℂ (fun p : E × ℂ => ∮ z in C(c, R), G (p.1, z) / (z - p.2)) (x, w) := by
    simpa only [one_mul] using h
  exact h'.const_mul _

theorem differentiableOn_parametricCauchyIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {G : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hG : DifferentiableOn ℂ G W)
    {U : Set E} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUW : U ×ˢ sphere c R ⊆ W) :
    DifferentiableOn ℂ (parametricCauchyIntegral G c R) (U ×ˢ ball c R) :=
  fun _ hp => (differentiableAt_parametricCauchyIntegral hW hG hU hR hUW hp.1 hp.2).differentiableWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParametricCauchyIntegral.Weierstrass
