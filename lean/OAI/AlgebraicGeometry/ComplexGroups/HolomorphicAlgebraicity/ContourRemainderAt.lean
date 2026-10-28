import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-! # Contour Remainder At -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

noncomputable section

/-!
# Polynomial remainders from contour integrals

The polynomial quotient by `X - z` gives a finite Cauchy kernel. Integrating
its coefficients produces a polynomial which agrees with a holomorphic
function at every root of the given polynomial inside the circle.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology BigOperators

def kernelCoeff (d : ℕ) (P : Polynomial ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (k + 1) d, z ^ (j - (k + 1)) * P.coeff j

theorem kernelCoeff_eq {d : ℕ} (P : Polynomial ℂ) (hP : P.natDegree = d) (z : ℂ) (k : ℕ) :
    kernelCoeff d P z k = (P /ₘ (X - C z)).coeff k := by
  rw [coeff_divByMonic_X_sub_C, hP]
  rfl

theorem continuous_kernelCoeff (d : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    Continuous (fun z => kernelCoeff d P z k) := by
  unfold kernelCoeff
  exact continuous_finsetSum _ (fun j _ => (continuous_pow _).mul_const _)

theorem kernel_eval_eq {d : ℕ} (P : Polynomial ℂ) (hP : P.natDegree = d) (z w : ℂ) :
    (P /ₘ (X - C z)).eval w = ∑ k ∈ Finset.range (d + 1), kernelCoeff d P z k * w ^ k := by
  have hdeg : (P /ₘ (X - C z)).natDegree < d + 1 := by
    rw [natDegree_divByMonic P (monic_X_sub_C z), natDegree_X_sub_C, hP]
    omega
  rw [eval_eq_sum_range' hdeg]
  simp only [kernelCoeff_eq P hP]

theorem kernel_identity_at_root {d : ℕ} (P : Polynomial ℂ) (hP : P.natDegree = d)
    {w : ℂ} (hw : P.eval w = 0) (z : ℂ) :
    (z - w) * (∑ k ∈ Finset.range (d + 1), kernelCoeff d P z k * w ^ k) = P.eval z := by
  have h := congrArg (fun Q : Polynomial ℂ => Q.eval w) (P.modByMonic_add_div (X - C z))
  rw [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_C,
    hw, kernel_eval_eq P hP] at h
  linear_combination -h

def remainderCoeff (d : ℕ) (P : Polynomial ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), g z / P.eval z * kernelCoeff d P z k

def remainderPolynomial (d : ℕ) (P : Polynomial ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1), monomial k (remainderCoeff d P g c R k)

theorem remainderPolynomial_natDegree_le (d : ℕ) (P : Polynomial ℂ) (g : ℂ → ℂ)
    (c : ℂ) (R : ℝ) : (remainderPolynomial d P g c R).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem remainderPolynomial_coeff (d : ℕ) (P : Polynomial ℂ) (g : ℂ → ℂ)
    (c : ℂ) (R : ℝ) (k : ℕ) :
    (remainderPolynomial d P g c R).coeff k =
      if k ≤ d then remainderCoeff d P g c R k else 0 := by
  simp [remainderPolynomial, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']

theorem remainderPolynomial_eval_at_root {d : ℕ} (P : Polynomial ℂ) (hP : P.natDegree = d)
    {g : ℂ → ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, P.eval z ≠ 0)
    (hw : w ∈ ball c R) (hroot : P.eval w = 0) :
    (remainderPolynomial d P g c R).eval w = g w := by
  have hc (k : ℕ) : CircleIntegrable
      (fun z => g z / P.eval z * kernelCoeff d P z k * w ^ k) c R :=
    ((((hg.continuousOn.mono sphere_subset_closedBall).div P.continuous.continuousOn hboundary).mul
      (continuous_kernelCoeff d P k).continuousOn).mul_const _).circleIntegrable hR.le
  have heq (z : ℂ) (hz : z ∈ sphere c R) :
      (∑ k ∈ Finset.range (d + 1), g z / P.eval z * kernelCoeff d P z k * w ^ k) =
        (z - w)⁻¹ * g z := by
    have hzw : z - w ≠ 0 := by
      intro h
      have : z = w := sub_eq_zero.mp h
      exact (ne_of_lt (mem_ball.mp hw)) (this ▸ mem_sphere.mp hz)
    simp only [mul_assoc, ← Finset.mul_sum]
    have hker := kernel_identity_at_root P hP hroot z
    have hker' : (∑ k ∈ Finset.range (d + 1), kernelCoeff d P z k * w ^ k) =
        P.eval z / (z - w) := (eq_div_iff hzw).mpr (by simpa only [mul_comm] using hker)
    rw [hker']
    field_simp [hboundary z hz]
  calc
    _ = ∑ k ∈ Finset.range (d + 1), remainderCoeff d P g c R k * w ^ k := by
      simp only [remainderPolynomial, eval_finsetSum, eval_monomial]
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        ∑ k ∈ Finset.range (d + 1), (∮ z in C(c, R),
          g z / P.eval z * kernelCoeff d P z k * w ^ k) := by
      simp only [remainderCoeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hint := circleIntegral.integral_smul_const
        (fun z => g z / P.eval z * kernelCoeff d P z k) (w ^ k) c R
      simp only [smul_eq_mul] at hint
      rw [hint, mul_assoc]
    _ = (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R),
        ∑ k ∈ Finset.range (d + 1), g z / P.eval z * kernelCoeff d P z k * w ^ k) := by
      rw [circleIntegral.integral_fun_sum (fun k _ => hc k)]
    _ = (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R), (z - w)⁻¹ * g z) := by
      congr 1
      exact circleIntegral.integral_congr hR.le heq
    _ = g w := by
      have hC := hg.circleIntegral_sub_inv_smul hw
      simp only [smul_eq_mul] at hC
      rw [hC, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

theorem differentiableOn_polynomial_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : E → Polynomial ℂ} {U : Set E} {d : ℕ}
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d) :
    DifferentiableOn ℂ (fun p : E × ℂ => (P p.1).eval p.2) (U ×ˢ univ) := by
  have hsum : DifferentiableOn ℂ (fun p : E × ℂ =>
      ∑ k ∈ Finset.range (d + 1), (P p.1).coeff k * p.2 ^ k) (U ×ˢ univ) := by
    apply DifferentiableOn.fun_sum
    intro k _
    exact ((hcoeff k).comp differentiable_fst.differentiableOn (fun _ hp => hp.1)).fun_mul
      (differentiable_snd.pow k).differentiableOn
  apply hsum.congr
  intro p hp
  exact eval_eq_sum_range' (lt_of_le_of_lt (hdegree p.1 hp.1) (Nat.lt_succ_self d)) p.2

theorem differentiableOn_kernelCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : E → Polynomial ℂ} {U : Set E} (d k : ℕ)
    (hcoeff : ∀ j : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff j) U) :
    DifferentiableOn ℂ (fun p : E × ℂ => kernelCoeff d (P p.1) p.2 k) (U ×ˢ univ) := by
  unfold kernelCoeff
  apply DifferentiableOn.fun_sum
  intro j _
  exact (differentiable_snd.pow _).differentiableOn.fun_mul
    ((hcoeff j).comp differentiable_fst.differentiableOn (fun _ hp => hp.1))

theorem differentiableAt_remainderCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) {P : E → Polynomial ℂ} {d : ℕ}
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0) (k : ℕ) :
    DifferentiableAt ℂ (fun y => remainderCoeff d (P y) (fun z => F (y, z)) c R k) x := by
  have hEval := differentiableOn_polynomial_eval hcoeff hdegree
  let V : Set (E × ℂ) := W ∩ ((U ×ˢ univ) ∩
    (fun p : E × ℂ => (P p.1).eval p.2) ⁻¹' ({0} : Set ℂ)ᶜ)
  have hV : IsOpen V := hW.inter (hEval.continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) isClosed_singleton.isOpen_compl)
  let G : E × ℂ → ℂ := fun p =>
    F p * ((P p.1).eval p.2)⁻¹ * kernelCoeff d (P p.1) p.2 k
  have hVU : V ⊆ U ×ˢ univ := fun _ hp => hp.2.1
  have hG : DifferentiableOn ℂ G V :=
    ((hF.mono inter_subset_left).fun_mul ((hEval.mono hVU).fun_inv (fun _ hp => hp.2.2))).fun_mul
      ((differentiableOn_kernelCoeff d k hcoeff).mono hVU)
  have hUV : U ×ˢ sphere c R ⊆ V := fun p hp =>
    ⟨hUW hp, ⟨hp.1, mem_univ _⟩, hn p.1 hp.1 p.2 hp.2⟩
  have hint := ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral hV hG hU hx hR hUV
    (w := fun _ => 1) continuousOn_const
  have hint' : DifferentiableAt ℂ (fun y => ∮ z in C(c, R), G (y, z)) x := by
    simpa only [one_mul] using hint
  exact hint'.const_mul _

theorem differentiableOn_remainderPolynomial_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {U : Set E} (hU : IsOpen U) {P : E → Polynomial ℂ} {d : ℕ}
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0) (k : ℕ) :
    DifferentiableOn ℂ (fun y =>
      (remainderPolynomial d (P y) (fun z => F (y, z)) c R).coeff k) U := by
  simp only [remainderPolynomial_coeff]
  split_ifs with hk
  · intro y hy
    exact (differentiableAt_remainderCoeff hW hF hU hy hcoeff hdegree hR hUW hn k).differentiableWithinAt
  · exact differentiableOn_const _

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder
