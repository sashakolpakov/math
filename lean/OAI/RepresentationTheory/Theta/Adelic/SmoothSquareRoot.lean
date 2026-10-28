import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Smooth Square Root -/

namespace OAI.RepresentationTheory.Theta.Adelic.SmoothSquareRoot

noncomputable section

/-! A continuous nonzero square root of a smooth complex-valued
function is smooth, using the actual local inverse of squaring. -/

open scoped Classical _root_.Topology

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root

theorem contDiffAt_of_continuous_square {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : V → ℂ) (x : V) (hf : ContinuousAt f x) (hg : ContDiffAt ℝ ⊤ g x)
    (hs : ∀ y, f y ^ 2 = g y) (hn : f x ≠ 0) : ContDiffAt ℝ ⊤ f x := by
  let c := f x
  have hc : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hn
  let eC : ℂ ≃L[ℂ] ℂ :=
    LinearEquiv.toContinuousLinearEquiv (LinearEquiv.smulOfNeZero ℂ ℂ (2 * c) hc)
  let e : ℂ ≃L[ℝ] ℂ := eC.restrictScalars ℝ
  have hderC : HasFDerivAt (fun z : ℂ => z ^ 2) eC.toContinuousLinearMap c := by
    have he : eC.toContinuousLinearMap = ContinuousLinearMap.toSpanSingleton ℂ (2 * c) := by
      apply ContinuousLinearMap.ext
      intro u
      change (2 * c) * u = u * (2 * c)
      ring
    rw [he]
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using (hasDerivAt_pow 2 c).hasFDerivAt
  have hder : HasFDerivAt (fun z : ℂ => z ^ 2) e.toContinuousLinearMap c := hderC.restrictScalars ℝ
  have hp : ContDiffAt ℝ ⊤ (fun z : ℂ => z ^ 2) c := by fun_prop
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let inv := hp.localInverse hder htop
  have hi : ContDiffAt ℝ ⊤ inv (g x) := by
    rw [← hs x]
    exact hp.to_localInverse hder htop
  have he : (fun y => inv (g y)) =ᶠ[𝓝 x] f := by
    have hlocal := (hp.hasStrictFDerivAt' hder htop).eventually_left_inverse
    filter_upwards [hf hlocal] with y hy
    rw [← hs y]
    exact hy
  exact (hi.comp x hg).congr_of_eventuallyEq he.symm

theorem ball_smooth_of_continuous_square (f g : BallNatural.Ball → ℂ)
    (hf : Continuous f) (hg : BallGeometryData.BallSmooth g) (hs : ∀ z, f z ^ 2 = g z)
    (hn : ∀ z, f z ≠ 0) : BallGeometryData.BallSmooth f := by
  let F : (Fin 2 → ℂ) → ℂ := fun z => if hz : z ∈ BallGeometryData.ballDomain then f ⟨z, hz⟩ else 0
  let G : (Fin 2 → ℂ) → ℂ := fun z => if hz : z ∈ BallGeometryData.ballDomain then g ⟨z, hz⟩ else 0
  have hF : ContinuousOn F BallGeometryData.ballDomain := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply hf.congr
    intro z
    change f z = if hz : z.val ∈ BallGeometryData.ballDomain then f ⟨z.val, hz⟩ else 0
    have hz : z.val ∈ BallGeometryData.ballDomain := z.property
    rw [dite_eq_left hz]
  have hFG : ∀ z, F z ^ 2 = G z := by
    intro z
    by_cases hz : z ∈ BallGeometryData.ballDomain
    · simpa only [F, G, dite_eq_left hz] using hs ⟨z, hz⟩
    · simp [F, G, hz]
  change ContDiffOn ℝ ⊤ G BallGeometryData.ballDomain at hg
  change ContDiffOn ℝ ⊤ F BallGeometryData.ballDomain
  intro z hz
  apply (contDiffAt_of_continuous_square F G z
    (hF.continuousAt (BallHolomorphicSquare.Root.ball_domain_open.mem_nhds hz))
    ((hg z hz).contDiffAt (BallHolomorphicSquare.Root.ball_domain_open.mem_nhds hz)) hFG ?_).contDiffWithinAt
  simpa only [F, dite_eq_left hz] using hn ⟨z, hz⟩

end

end OAI.RepresentationTheory.Theta.Adelic.SmoothSquareRoot
