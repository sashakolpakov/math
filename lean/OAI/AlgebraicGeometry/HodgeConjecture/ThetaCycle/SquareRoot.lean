import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Square Root -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SquareRoot.CM

noncomputable section

/-! Construct holomorphic square roots on the actual ball. Contractibility
supplies a continuous branch, and differentiability follows from the square
map's invertible derivative. This is the analytic half-determinant step. -/

open scoped Classical _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem differentiableAt_of_continuous_square
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (x : V) (hf : ContinuousAt f x)
    (hg : DifferentiableAt ℂ g x) (hfg : ∀ y, f y ^ 2 = g y)
    (hne : f x ≠ 0) : DifferentiableAt ℂ f x := by
  let c : ℂ := 2 * f x
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) hne
  have hp : HasFDerivAt (fun z : ℂ => z ^ 2)
      (ContinuousLinearMap.toSpanSingleton ℂ c) (f x) := by
    simpa only [c, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using
      (hasDerivAt_pow 2 (f x)).hasFDerivAt
  let inv : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ c⁻¹
  have hi : Function.LeftInverse inv (ContinuousLinearMap.toSpanSingleton ℂ c) := by
    intro z
    change (z * c) * c⁻¹ = z
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  exact (HasFDerivAt.of_comp_of_leftInverse hf hp hg.hasFDerivAt
    (Filter.Eventually.of_forall hfg) hi).differentiableAt

theorem ball_holomorphic_square_root
    {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hg : DifferentiableOn ℂ g B.domain) (hne : ∀ z ∈ B.domain, g z ≠ 0) :
    ∃ h : HeckeCycles.GeometricSource.CM.BallChart → ℂˣ,
      DifferentiableOn ℂ (fun z => (h z : ℂ)) B.domain ∧
      ∀ z ∈ B.domain, (h z : ℂ) ^ 2 = g z := by
  have hn : B.domain.Nonempty := ⟨0, by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr B.negative⟩
  let : ContractibleSpace B.domain := (BallConnected.CM.ball_domain_starConvex B).contractibleSpace hn
  have hsim : IsSimplyConnected B.domain := by
    change SimplyConnectedSpace B.domain
    infer_instance
  obtain ⟨f, hf, hfg⟩ := Complex.exists_continuousOn_pow_eq hsim B.domain_isOpen
    hg.continuousOn (by
      rintro ⟨z, hz, he⟩
      exact hne z hz he) (by decide : (2 : ℕ) ≠ 0)
  have hfn : ∀ z ∈ B.domain, f z ≠ 0 := by
    intro z hz he
    apply hne z hz
    rw [← hfg, he, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  let h : HeckeCycles.GeometricSource.CM.BallChart → ℂˣ := fun z =>
    if hz : z ∈ B.domain then Units.mk0 (f z) (hfn z hz) else 1
  have heq : ∀ z ∈ B.domain, (h z : ℂ) = f z := by
    intro z hz
    simp only [h, dite_eq_left hz, Units.val_mk0]
  refine ⟨h, ?_, fun z hz => by rw [heq z hz, hfg z]⟩
  intro z hz
  have hd := differentiableAt_of_continuous_square f g z
    (hf.continuousAt (B.domain_isOpen.mem_nhds hz))
    ((hg z hz).differentiableAt (B.domain_isOpen.mem_nhds hz)) hfg (hfn z hz)
  exact hd.differentiableWithinAt.congr (fun y hy => heq y hy) (heq z hz)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SquareRoot.CM
