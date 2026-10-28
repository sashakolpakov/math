import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HomogeneousExtension
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Branch Extension -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BranchExtension.Constructions.Growth

noncomputable section

/-!
# Polynomial extension across exceptional sets of projection coefficients

Continuity and polynomial growth let interpolation extend from a dense family
of holomorphic affine lines to all lines. Countable exceptional sets on each
line are removable by the Cauchy integral theorem.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology BigOperators

/-- Countably many exceptional points are removable for a continuous complex
function which is holomorphic at every other point. -/
theorem differentiable_of_continuous_off_countable {f : ℂ → ℂ} {S : Set ℂ}
    (hf : Continuous f) (hS : S.Countable)
    (hd : ∀ z, z ∉ S → DifferentiableAt ℂ f z) : Differentiable ℂ f := by
  intro z
  exact (Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable (R := 1)
    hS hf.continuousOn (fun w hw => hd w hw.2) zero_lt_one).analyticAt.differentiableAt

/-- Polynomial growth is preserved on every affine complex line. -/
theorem growth_affineLine {n d : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (x v : Fin n → ℂ) (c : ℂ) :
    ‖f (x + c • v)‖ ≤
      (C * (max 1 ‖x‖ + max 1 ‖v‖) ^ d) * (max 1 ‖c‖) ^ d := by
  have hx : 0 ≤ max 1 ‖x‖ := le_trans zero_le_one (le_max_left _ _)
  have hv : 0 ≤ max 1 ‖v‖ := le_trans zero_le_one (le_max_left _ _)
  have hc : 1 ≤ max 1 ‖c‖ := le_max_left _ _
  have hnorm : ‖x + c • v‖ ≤ (max 1 ‖x‖ + max 1 ‖v‖) * max 1 ‖c‖ := by
    calc
      _ ≤ ‖x‖ + ‖c‖ * ‖v‖ := by simpa only [norm_smul] using norm_add_le x (c • v)
      _ ≤ max 1 ‖x‖ + max 1 ‖c‖ * max 1 ‖v‖ := by gcongr <;> exact le_max_right _ _
      _ ≤ _ := by nlinarith
  have hmax : max 1 ‖x + c • v‖ ≤ (max 1 ‖x‖ + max 1 ‖v‖) * max 1 ‖c‖ := by
    apply max_le _ hnorm
    have hx1 : 1 ≤ max 1 ‖x‖ := le_max_left _ _
    nlinarith
  calc
    _ ≤ C * max 1 ‖x + c • v‖ ^ d := hbound _
    _ ≤ C * ((max 1 ‖x‖ + max 1 ‖v‖) * max 1 ‖c‖) ^ d := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

/-- With a common polynomial-growth bound, interpolation and continuity
extend holomorphy from dense translates of each line to every translate. -/
theorem line_differentiable_of_dense_lines {n d : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (hdense : ∀ v : Fin n → ℂ,
      Dense {x | Differentiable ℂ (fun c : ℂ => f (x + c • v))})
    (x v : Fin n → ℂ) : Differentiable ℂ (fun c : ℂ => f (x + c • v)) := by
  have hC : 0 ≤ C := by
    have h := hbound 0
    simp only [norm_zero, max_eq_left zero_le_one, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hinterp (c : ℂ) : f (x + c • v) =
      ∑ i : Fin (d + 1), f (x + PolynomialGrowth.Constructions.Growth.node d i • v) * (PolynomialGrowth.Constructions.Growth.cardinalBasis d i).eval c := by
    apply (hdense v).induction (P := fun y => f (y + c • v) =
      ∑ i : Fin (d + 1), f (y + PolynomialGrowth.Constructions.Growth.node d i • v) * (PolynomialGrowth.Constructions.Growth.cardinalBasis d i).eval c) ?_ ?_ x
    · intro y hy
      obtain ⟨p, hpdeg, hp⟩ := PolynomialGrowth.Constructions.Growth.exists_polynomial_of_growth hy
        (growth_affineLine hC hbound y v)
      simpa only [hp] using PolynomialGrowth.Constructions.Growth.interpolation_formula p hpdeg c
    · apply isClosed_eq (hf.comp (continuous_id.add continuous_const))
      apply continuous_finsetSum
      intro i _
      exact (hf.comp (continuous_id.add continuous_const)).mul continuous_const
  have heq : (fun c : ℂ => f (x + c • v)) =
      (fun c => ∑ i : Fin (d + 1), f (x + PolynomialGrowth.Constructions.Growth.node d i • v) * (PolynomialGrowth.Constructions.Growth.cardinalBasis d i).eval c) :=
    funext hinterp
  rw [heq]
  apply Differentiable.fun_sum
  intro i _
  exact (PolynomialGrowth.Constructions.Growth.cardinalBasis d i).differentiable.const_mul _

/-- A continuous function of polynomial growth which is holomorphic on a
dense family of translates of every line is an actual polynomial. -/
theorem exists_polynomial_of_dense_lines {n d : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (hdense : ∀ v : Fin n → ℂ,
      Dense {x | Differentiable ℂ (fun c : ℂ => f (x + c • v))}) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ x, MvPolynomial.eval x P = f x :=
  PolynomialGrowth.Constructions.Growth.exists_mvPolynomial_of_line_growth n
    (line_differentiable_of_dense_lines hf hbound hdense) hbound

/-- A nonzero entire function of one complex variable has only countably
many zeros. -/
theorem countable_zeroSet_of_entire {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hne : ∃ z, g z ≠ 0) : {z | g z = 0}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_nhdsNE.mpr
  intro x _
  by_contra hbot
  have hfreq : ∃ᶠ z in 𝓝[≠] x, g z = 0 := frequently_iff_neBot.mpr ⟨hbot⟩
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have heq := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ x) hfreq
  obtain ⟨z, hz⟩ := hne
  exact hz (heq (mem_univ z))

/-- Continuous polynomial-growth functions extend across a zero set whose
defining function is holomorphic on every affine line and nonzero densely. -/
theorem exists_polynomial_off_zeroSet {n d : ℕ} {f g : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (hg : ∀ x v, Differentiable ℂ (fun c : ℂ => g (x + c • v)))
    (hdense : Dense {x | g x ≠ 0})
    (hd : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ x, MvPolynomial.eval x P = f x := by
  apply exists_polynomial_of_dense_lines hf hbound
  intro v
  apply hdense.mono
  intro x hx
  change g x ≠ 0 at hx
  have hline : Differentiable ℂ (fun c : ℂ => x + c • v) :=
    (differentiable_const x).add (differentiable_id.smul_const v)
  apply differentiable_of_continuous_off_countable (hf.comp hline.continuous)
    (countable_zeroSet_of_entire (hg x v) ⟨0, by simpa only [zero_smul, add_zero] using hx⟩)
  intro c hc
  exact (hd (x + c • v) hc).comp c (hline c)

/-- A function holomorphic on every affine line and nonzero somewhere is
nonzero on a dense set. -/
theorem dense_nonzero_of_line_holomorphic {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ∀ x v, Differentiable ℂ (fun c : ℂ => g (x + c • v)))
    (hne : ∃ z, g z ≠ 0) : Dense {x | g x ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨z, hz⟩ := hne
  by_contra hno
  have hzeroU : ∀ y ∈ U, g y = 0 := by
    intro y hy
    by_contra hgy
    exact hno ⟨y, hy, hgy⟩
  have hline : Differentiable ℂ (fun c : ℂ => x + c • (z - x)) :=
    (differentiable_const x).add (differentiable_id.smul_const (z - x))
  have hUline : (fun c : ℂ => x + c • (z - x)) ⁻¹' U ∈ 𝓝 0 :=
    (hU.preimage hline.continuous).mem_nhds (by
      simpa only [mem_preimage, zero_smul, add_zero] using hx)
  have hzero : ∀ᶠ c : ℂ in 𝓝 0, g (x + c • (z - x)) = 0 := by
    filter_upwards [hUline] with c hc
    exact hzeroU _ hc
  have hga : AnalyticOnNhd ℂ (fun c : ℂ => g (x + c • (z - x))) univ :=
    fun c _ => (hg x (z - x)).analyticAt c
  have heq := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ 0) (hzero.filter_mono nhdsWithin_le_nhds).frequently
  apply hz
  have hxz : x + (z - x) = z := by abel
  simpa only [one_smul, hxz, Pi.zero_apply] using heq (mem_univ (1 : ℂ))

/-- A continuous polynomial-growth function holomorphic off the zero locus
of a nonzero entire function is polynomial, including across that zero locus. -/
theorem exists_polynomial_off_entire_zeroSet {n d : ℕ}
    {f g : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (hg : Differentiable ℂ g) (hne : ∃ z, g z ≠ 0)
    (hd : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ x, MvPolynomial.eval x P = f x := by
  have hline (x v : Fin n → ℂ) : Differentiable ℂ (fun c : ℂ => g (x + c • v)) :=
    hg.comp ((differentiable_const x).add (differentiable_id.smul_const v))
  exact exists_polynomial_off_zeroSet hf hbound hline
    (dense_nonzero_of_line_holomorphic hline hne) hd

/-- Homogeneous continuous coefficients which are holomorphic away from an
entire branch equation extend as homogeneous polynomials of the same degree. -/
theorem exists_homogeneousPolynomial_off_entire_zeroSet {n d : ℕ}
    {f g : (Fin n → ℂ) → ℂ} (hd : 0 < d)
    (hf : Continuous f) (hhom : ∀ (c : ℂ) x, f (c • x) = c ^ d * f x)
    (hg : Differentiable ℂ g) (hne : ∃ z, g z ≠ 0)
    (hfdiff : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      P.IsHomogeneous d ∧ ∀ x, MvPolynomial.eval x P = f x := by
  obtain ⟨C, _, hbound⟩ := HomogeneousExtension.Constructions.Growth.polynomial_growth_of_homogeneous hd hf.continuousOn hhom
  obtain ⟨P, hP⟩ := exists_polynomial_off_entire_zeroSet hf hbound hg hne hfdiff
  have heq := HomogeneousExtension.Constructions.Growth.homogeneousComponent_eq_of_eval_smul P (by simpa only [hP] using hhom)
  refine ⟨P, ?_, hP⟩
  rw [← heq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d P

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BranchExtension.Constructions.Growth
