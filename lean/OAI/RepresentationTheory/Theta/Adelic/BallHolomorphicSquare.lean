import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Ball Holomorphic Square -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root

/-! Holomorphic square roots on the actual unit ball. The continuous
branch comes from contractibility; its differentiability follows from
the invertible derivative of the square map. -/

open scoped Classical _root_.Topology

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

theorem ball_domain_starConvex : StarConvex ℝ (0 : Fin 2 → ℂ) BallGeometryData.ballDomain := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b * b ≤ 1 := by nlinarith
  have hq : 0 ≤ Complex.normSq (z 0) + Complex.normSq (z 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  change Complex.normSq ((a • 0 + b • z) 0) + Complex.normSq ((a • 0 + b • z) 1) < 1
  simp only [smul_zero, zero_add, Pi.smul_apply, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  calc
    _ = (b * b) * (Complex.normSq (z 0) + Complex.normSq (z 1)) := by ring
    _ ≤ Complex.normSq (z 0) + Complex.normSq (z 1) := mul_le_of_le_one_left hq hb2
    _ < 1 := hz

theorem ball_domain_open : IsOpen BallGeometryData.ballDomain :=
  isOpen_lt (by fun_prop) continuous_const

theorem ball_domain_nonempty : BallGeometryData.ballDomain.Nonempty :=
  ⟨0, by simp [BallGeometryData.ballDomain]⟩

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

theorem ball_holomorphic_square_root (g : BallNatural.Ball → ℂ)
    (hg : BallGeometryData.BallHolomorphic g) (hne : ∀ z, g z ≠ 0) :
    ∃ h : BallNatural.Ball → ℂ, BallGeometryData.BallHolomorphic h ∧ ∀ z, h z ≠ 0 ∧ h z ^ 2 = g z := by
  let : ContractibleSpace BallGeometryData.ballDomain := ball_domain_starConvex.contractibleSpace ball_domain_nonempty
  have hsim : IsSimplyConnected BallGeometryData.ballDomain := by
    change SimplyConnectedSpace BallGeometryData.ballDomain
    infer_instance
  let G : (Fin 2 → ℂ) → ℂ := fun z => if hz : z ∈ BallGeometryData.ballDomain then g ⟨z, hz⟩ else 0
  change DifferentiableOn ℂ G BallGeometryData.ballDomain at hg
  have hGn : ∀ z ∈ BallGeometryData.ballDomain, G z ≠ 0 := by
    intro z hz
    simpa only [G, dite_eq_left hz] using hne ⟨z, hz⟩
  obtain ⟨f, hf, hfg⟩ := Complex.exists_continuousOn_pow_eq hsim ball_domain_open hg.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hGn z hz he) (by decide : (2 : ℕ) ≠ 0)
  have hfn : ∀ z ∈ BallGeometryData.ballDomain, f z ≠ 0 := by
    intro z hz he
    apply hGn z hz
    rw [← hfg, he, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  refine ⟨fun z => f z.val, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ f BallGeometryData.ballDomain := by
      intro z hz
      exact (differentiableAt_of_continuous_square f G z
        (hf.continuousAt (ball_domain_open.mem_nhds hz))
        ((hg z hz).differentiableAt (ball_domain_open.mem_nhds hz)) hfg (hfn z hz)).differentiableWithinAt
    apply hd.congr
    intro z hz
    rw [dite_eq_left hz]
  · intro z
    have hz : z.val ∈ BallGeometryData.ballDomain := z.property
    exact ⟨hfn z.val hz, (hfg z.val).trans (by simp only [G, dite_eq_left hz])⟩

end RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root

namespace RepresentationTheory.Theta.Adelic.BallHolomorphicSquare

/-! Continuity of holomorphic functions on the ball, and holomorphy of
a continuous nonzero square root. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root

theorem continuous_fixed_left {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y → Z)
    (hf : Continuous (fun p : X × Y => f p.1 p.2)) (x : X) : Continuous (f x) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem continuous_fixed_right {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y → Z)
    (hf : Continuous (fun p : X × Y => f p.1 p.2)) (y : Y) : Continuous (fun x => f x y) :=
  hf.comp (continuous_id.prodMk continuous_const)

theorem ball_holomorphic_continuous {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : BallNatural.Ball → V) (hf : BallGeometryData.BallHolomorphic f) : Continuous f := by
  have h := hf.continuousOn
  rw [continuousOn_iff_continuous_domRestrict] at h
  apply h.congr
  intro z
  exact dite_eq_left z.property

theorem ball_holomorphic_of_continuous_square (f g : BallNatural.Ball → ℂ)
    (hf : Continuous f) (hg : BallGeometryData.BallHolomorphic g)
    (hs : ∀ z, f z ^ 2 = g z) (hn : ∀ z, f z ≠ 0) : BallGeometryData.BallHolomorphic f := by
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
    · simp only [F, G, dite_eq_right hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  change DifferentiableOn ℂ G BallGeometryData.ballDomain at hg
  change DifferentiableOn ℂ F BallGeometryData.ballDomain
  intro z hz
  apply (Root.differentiableAt_of_continuous_square F G z
    (hF.continuousAt (Root.ball_domain_open.mem_nhds hz))
    ((hg z hz).differentiableAt (Root.ball_domain_open.mem_nhds hz)) hFG ?_).differentiableWithinAt
  simpa only [F, dite_eq_left hz] using hn ⟨z, hz⟩

end RepresentationTheory.Theta.Adelic.BallHolomorphicSquare

end

end OAI
