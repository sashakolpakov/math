import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap

/-! # Homogeneous Extension -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HomogeneousExtension.Constructions.Growth

noncomputable section

/-!
# Extension of homogeneous holomorphic coefficients across the cone vertex

A function of positive integral homogeneity, holomorphic away from the origin,
is a polynomial. The proof first handles every affine complex line, then uses
compactness of the unit sphere and polynomial interpolation.
-/

open Filter Set _root_.Metric
open scoped _root_.Topology BigOperators

/-- A homogeneous function holomorphic away from the origin is holomorphic on
each affine line: a line passing through the origin has an explicit formula. -/
theorem line_differentiable_of_homogeneous {n d : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f {0}ᶜ)
    (hhom : ∀ (c : ℂ) x, f (c • x) = c ^ d * f x)
    (x v : Fin n → ℂ) : Differentiable ℂ (fun c : ℂ => f (x + c • v)) := by
  by_cases hzero : ∃ c : ℂ, x + c • v = 0
  · obtain ⟨c₀, hc₀⟩ := hzero
    have hx : x = -(c₀ • v) := eq_neg_of_add_eq_zero_left hc₀
    have heq : (fun c : ℂ => f (x + c • v)) =
        (fun c => (c - c₀) ^ d * f v) := by
      funext c
      rw [hx, ← hhom]
      congr 1
      rw [sub_smul]
      abel
    rw [heq]
    exact ((differentiable_id.sub_const c₀).pow d).mul_const _
  · intro c
    have hne : x + c • v ∈ ({0}ᶜ : Set (Fin n → ℂ)) := by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        (not_exists.mp hzero c)
    exact (hf.differentiableAt (isOpen_compl_singleton.mem_nhds hne)).comp c
      (((differentiable_const x).add (differentiable_id.smul_const v)) c)

/-- Compactness of the unit sphere turns positive homogeneity into a global
polynomial-growth estimate. -/
theorem polynomial_growth_of_homogeneous {n d : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hd : 0 < d) (hf : ContinuousOn f {0}ᶜ)
    (hhom : ∀ (c : ℂ) x, f (c • x) = c ^ d * f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * (max 1 ‖x‖) ^ d := by
  have hs : sphere (0 : Fin n → ℂ) 1 ⊆ ({0}ᶜ : Set (Fin n → ℂ)) := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hx
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero))
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_sphere (0 : Fin n → ℂ) 1).image_of_continuousOn
      (hf.mono hs)).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    have hf0 : f 0 = 0 := by
      simpa only [zero_smul, zero_pow hd.ne', zero_mul] using hhom 0 0
    rw [hf0, norm_zero]
    positivity
  · let c : ℂ := ‖x‖
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (norm_ne_zero_iff.mpr hx)
    have hcnorm : ‖c‖ = ‖x‖ := by
      simp [c]
    let y : Fin n → ℂ := c⁻¹ • x
    have hynorm : ‖y‖ = 1 := by
      rw [show y = c⁻¹ • x from rfl, norm_smul, norm_inv, hcnorm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
    have hy : y ∈ sphere (0 : Fin n → ℂ) 1 := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hynorm
    have hcy : c • y = x := by
      rw [show y = c⁻¹ • x from rfl, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hfy : ‖f y‖ ≤ C := hbound _ (mem_image_of_mem f hy)
    calc
      ‖f x‖ = ‖x‖ ^ d * ‖f y‖ := by
        conv_lhs => rw [← hcy, hhom, norm_mul, norm_pow, hcnorm]
      _ ≤ ‖x‖ ^ d * C := by gcongr
      _ ≤ (max 1 ‖x‖) ^ d * C := by gcongr; exact le_max_right _ _
      _ = C * (max 1 ‖x‖) ^ d := mul_comm _ _

/-- Positive homogeneous holomorphic coefficients on a punctured complex
coordinate space extend across the origin as actual polynomials. -/
theorem exists_polynomial_of_punctured_homogeneous {n d : ℕ}
    {f : (Fin n → ℂ) → ℂ} (hd : 0 < d)
    (hf : DifferentiableOn ℂ f {0}ᶜ)
    (hhom : ∀ (c : ℂ) x, f (c • x) = c ^ d * f x) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ x, MvPolynomial.eval x P = f x := by
  obtain ⟨C, _, hC⟩ := polynomial_growth_of_homogeneous hd hf.continuousOn hhom
  exact PolynomialGrowth.Constructions.Growth.exists_mvPolynomial_of_line_growth n
    (line_differentiable_of_homogeneous hf hhom) (C := C) hC

/-- A polynomial function satisfying a homogeneous scaling law is represented
by its component of precisely that degree. -/
theorem homogeneousComponent_eq_of_eval_smul {n d : ℕ}
    (P : MvPolynomial (Fin n) ℂ)
    (hhom : ∀ (c : ℂ) x,
      MvPolynomial.eval (c • x) P = c ^ d * MvPolynomial.eval x P) :
    MvPolynomial.homogeneousComponent d P = P := by
  apply MvPolynomial.funext
  intro x
  have hscale (c : ℂ) : MvPolynomial.eval (c • x) P =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        c ^ k * MvPolynomial.eval x (MvPolynomial.homogeneousComponent k P) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent P]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact Foundations.Scheme.HomogeneousEvalMap.eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous k P) c x
  have hpoly : (∑ k ∈ Finset.range (P.totalDegree + 1),
      Polynomial.monomial k
        (MvPolynomial.eval x (MvPolynomial.homogeneousComponent k P))) =
      Polynomial.monomial d (MvPolynomial.eval x P) := by
    apply Polynomial.funext
    intro c
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using
      (hscale c).symm.trans (hhom c x)
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hpoly
  by_cases hd : d ∈ Finset.range (P.totalDegree + 1)
  · simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hd] using hcoeff
  · have hdeg : P.totalDegree < d := by
      simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hdeg, map_zero]
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hd] using hcoeff

/-- The polynomial extension retains the specified homogeneous degree. -/
theorem exists_homogeneousPolynomial_of_punctured_homogeneous {n d : ℕ}
    {f : (Fin n → ℂ) → ℂ} (hd : 0 < d)
    (hf : DifferentiableOn ℂ f {0}ᶜ)
    (hhom : ∀ (c : ℂ) x, f (c • x) = c ^ d * f x) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      P.IsHomogeneous d ∧ ∀ x, MvPolynomial.eval x P = f x := by
  obtain ⟨P, hP⟩ := exists_polynomial_of_punctured_homogeneous hd hf hhom
  have heq := homogeneousComponent_eq_of_eval_smul P (by simpa only [hP] using hhom)
  refine ⟨P, ?_, hP⟩
  rw [← heq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d P

/-- Only the punctured scaling law is needed: setting the value at the origin
to zero gives the unique positive-degree homogeneous polynomial extension. -/
theorem extend_punctured_homogeneous {n d : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hd : 0 < d) (hf : DifferentiableOn ℂ f {0}ᶜ)
    (hhom : ∀ (c : ℂ), c ≠ 0 → ∀ x, x ≠ 0 → f (c • x) = c ^ d * f x) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      P.IsHomogeneous d ∧ ∀ x, x ≠ 0 → MvPolynomial.eval x P = f x := by
  classical
  let g : (Fin n → ℂ) → ℂ := fun x => if x = 0 then 0 else f x
  have hgf (x : Fin n → ℂ) (hx : x ∈ ({0}ᶜ : Set (Fin n → ℂ))) : g x = f x := by
    exact ite_eq_right (by simpa only [mem_compl_iff, mem_singleton_iff] using hx)
  have hg : DifferentiableOn ℂ g {0}ᶜ := hf.congr hgf
  have hghom (c : ℂ) (x : Fin n → ℂ) : g (c • x) = c ^ d * g x := by
    by_cases hc : c = 0
    · simp [hc, g, zero_pow hd.ne']
    by_cases hx : x = 0
    · simp [hx, g]
    simp only [g, ite_eq_right hx, ite_eq_right (smul_ne_zero hc hx)]
    exact hhom c hc x hx
  obtain ⟨P, hP, heq⟩ := exists_homogeneousPolynomial_of_punctured_homogeneous hd hg hghom
  refine ⟨P, hP, fun x hx => ?_⟩
  simpa only [g, ite_eq_right hx] using heq x

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HomogeneousExtension.Constructions.Growth
