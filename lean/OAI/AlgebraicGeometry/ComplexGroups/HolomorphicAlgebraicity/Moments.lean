import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt

/-! # Moments -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Moments.Constructions.RootFamilies

noncomputable section

/-!
# Holomorphic contour root moments

The vertical derivative and the original family are jointly holomorphic.
Their quotient is holomorphic away from zeros, so integration around a fixed
zero-free circle gives holomorphic power sums of the enclosed roots.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology BigOperators

theorem differentiableAt_moment {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {x : Fin n → ℂ} (hx : x ∈ U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ p ∈ U ×ˢ sphere c R, F p ≠ 0) (k : ℕ) :
    DifferentiableAt ℂ (fun y => RootFamiliesAt.Constructions.RootFamilies.moment (fun z => F (y, z)) c R k) x := by
  let V := W ∩ F ⁻¹' ({0} : Set ℂ)ᶜ
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage hW isClosed_singleton.isOpen_compl
  let G : (Fin n → ℂ) × ℂ → ℂ := fun p => fderiv ℂ F p (0, 1) * (F p)⁻¹
  have hG : DifferentiableOn ℂ G V :=
    ((ParametricIntegralAt.Constructions.ParametricIntegral.differentiableOn_fderiv_apply hW hF (0, 1)).mono inter_subset_left).fun_mul
      ((hF.mono inter_subset_left).fun_inv (fun _ hp => hp.2))
  have hint := ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral hV hG hU hx hR
    (fun p hp => ⟨hUW hp, hn p hp⟩) (continuous_pow k).continuousOn
  have heq : (fun y => RootFamiliesAt.Constructions.RootFamilies.moment (fun z => F (y, z)) c R k) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), z ^ k * G (y, z)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    unfold RootFamiliesAt.Constructions.RootFamilies.moment
    congr 1
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only
    congr 1
    rw [logDeriv_apply, RootFamiliesAt.Constructions.RootFamilies.deriv_slice_eq_fderiv (p := (y, z))
      (hF.differentiableAt (hW.mem_nhds (hUW ⟨hy, hz⟩)))]
    rfl
  exact (hint.const_mul _).congr_of_eventuallyEq heq

theorem differentiableOn_moment {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ p ∈ U ×ˢ sphere c R, F p ≠ 0) (k : ℕ) :
    DifferentiableOn ℂ (fun y => RootFamiliesAt.Constructions.RootFamilies.moment (fun z => F (y, z)) c R k) U :=
  fun _ hx => (differentiableAt_moment hW hF hU hx hR hUW hn k).differentiableWithinAt

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Moments.Constructions.RootFamilies
