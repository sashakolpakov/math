import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.AlgebraicGeometry.ComplexMultiplication.LatticeGaussian
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Group.Tannery
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Projectivity Criterion -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

noncomputable section

/-!
# RiemannProjectivity: the Riemann projectivity criterion

This file proves the criterion in `Statements/RiemannProjectivity.lean` without importing that
statement stub. Positive integral Hermitian data give convergent theta sections
separating points and tangent vectors, hence a finite closed holomorphic
projective embedding. Conversely, projective curvature gives a positive
Hermitian form whose lattice periods are integral by local Stokes and grid
boundary cancellation. Averaging over the torus preserves those periods.

The final theorem `Hodge.RiemannProjectivity.riemann_projectivity_criterion` has exactly the
hypotheses and conclusion of the committed specification. Its axiom audit uses
only `propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace Construction
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem hermitian_add_left (u v w : V) : H (u + v) w = H u w + H v w := by
  simp

theorem hermitian_smul_left (a : ℂ) (u v : V) :
    H (a • u) v = star a * H u v := by
  simp

theorem hermitian_imaginary_self
    (hsym : ∀ u v : V, H v u = star (H u v)) (u : V) :
    (H u u).im = 0 := by
  have h := congrArg Complex.im (hsym u u)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem hermitian_imaginary_swap
    (hsym : ∀ u v : V, H v u = star (H u v)) (u v : V) :
    (H v u).im = -(H u v).im := by
  rw [hsym]
  rfl

theorem hermitian_imaginary_mul_I (u v : V) :
    (H u (Complex.I • v)).im = (H u v).re := by
  simp [map_smul, Complex.mul_im]

theorem hermitian_complex_invariant (u v : V) :
    H (Complex.I • u) (Complex.I • v) = H u v := by
  simp [map_smul, ← mul_assoc]

theorem hermitian_riemann_positive
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (u : V) (hu : u ≠ 0) :
    0 < (H u (Complex.I • u)).im := by
  rw [hermitian_imaginary_mul_I]
  exact hpos u hu

theorem hermitian_skew
    (hsym : ∀ u v : V, H v u = star (H u v)) (u v : V) :
    H u v - H v u = 2 * Complex.I * ((H u v).im : ℂ) := by
  rw [hsym u v]
  apply Complex.ext
  · simp
  · simp only [Complex.sub_im, Complex.star_def, Complex.conj_im,
      Complex.mul_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- The doubled polarization has a factor of automorphy without a choice of
semicharacter. Its definition uses the original Hermitian form. -/
def doubledAutomorphy (l z : V) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * H l z + (Real.pi : ℂ) * H l l)

theorem doubledAutomorphy_ne_zero (l z : V) : doubledAutomorphy H l z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem doubledAutomorphy_zero (z : V) : doubledAutomorphy H 0 z = 1 := by
  simp [doubledAutomorphy]

/-- Integrality of the original form, rather than a projectivity assumption,
proves the lattice translation cocycle identity. -/
theorem doubledAutomorphy_add
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (l m z : V) (hl : l ∈ Λ) (hm : m ∈ Λ) :
    doubledAutomorphy H (l + m) z =
      doubledAutomorphy H l (z + m) * doubledAutomorphy H m z := by
  obtain ⟨n, hn⟩ := hint l hl m hm
  have hs := hermitian_skew H hsym l m
  rw [hn] at hs
  push_cast at hs
  simp only [doubledAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-n, ?_⟩
  push_cast
  linear_combination -(Real.pi : ℂ) * hs

theorem doubledAutomorphy_differentiable [FiniteDimensional ℂ V] (l : V) :
    Differentiable ℂ (doubledAutomorphy H l) := by
  have hH : Differentiable ℂ (H l) := (H l).toContinuousLinearMap.differentiable
  exact ((hH.const_mul _).add_const _).cexp

section Bounds

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]

/-- The given sesquilinear form as a continuous real bilinear map. -/
def hermitianBilin : V →L[ℝ] V →L[ℝ] ℂ :=
  (show V →ₗ[ℝ] (V →L[ℝ] ℂ) from
    { toFun := fun x => (H x).toContinuousLinearMap.restrictScalars ℝ
      map_add' := by
        intro x y
        ext z
        exact hermitian_add_left H x y z
      map_smul' := by
        intro r x
        ext y
        change H (r • x) y = r • H x y
        have hr : (r : ℂ) • x = r • x := algebraMap_smul ℂ r x
        rw [← hr, Complex.real_smul, hermitian_smul_left]
        simp }).toContinuousLinearMap

@[simp]
theorem hermitianBilin_apply (u v : V) : hermitianBilin H u v = H u v := rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℂ V] in
theorem hermitian_real_smul_self (r : ℝ) (u : V) :
    (H (r • u) (r • u)).re = r ^ 2 * (H u u).re := by
  have hr : (r : ℂ) • u = r • u := algebraMap_smul ℂ r u
  rw [← hr, hermitian_smul_left, map_smul]
  simp [Complex.mul_re, pow_two, mul_assoc]

theorem hermitian_self_re_continuous : Continuous (fun u : V => (H u u).re) :=
  Complex.continuous_re.comp ((hermitianBilin H).continuous₂.comp
    (continuous_id.prodMk continuous_id))

/-- Strict positivity yields Gaussian decay in the original ambient norm. -/
theorem hermitian_exists_lower_bound
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).re := by
  classical
  by_cases hV : ∃ u : V, u ≠ 0
  · let : ProperSpace V := FiniteDimensional.proper ℝ V
    have normalize_mem (u : V) (hu : u ≠ 0) :
        ‖u‖⁻¹ • u ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hu]
    obtain ⟨u, hu⟩ := hV
    obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      ⟨‖u‖⁻¹ • u, normalize_mem u hu⟩ (hermitian_self_re_continuous H).continuousOn
    have hv0 : v ≠ 0 := by
      intro hv0
      simp [hv0] at hv
    refine ⟨(H v v).re, hpos v hv0, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hb := hmin (normalize_mem x hx)
      change (H v v).re ≤ (H (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re at hb
      rw [hermitian_real_smul_self] at hb
      have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)
      have hid : ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * (H x x).re) = (H x x).re := by
        field_simp
      rw [hid] at hb'
      simpa [mul_comm] using hb'
  · refine ⟨1, zero_lt_one, fun u => ?_⟩
    have hu : u = 0 := by simpa using not_exists.mp hV u
    simp [hu]

theorem hermitian_norm_le (u v : V) :
    ‖H u v‖ ≤ ‖hermitianBilin H‖ * ‖u‖ * ‖v‖ :=
  ((hermitianBilin H u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((hermitianBilin H).le_opNorm u) (norm_nonneg v))

theorem hermitian_linear_norm_le (u : V) :
    ‖(H u).toContinuousLinearMap‖ ≤ ‖hermitianBilin H‖ * ‖u‖ := by
  let f : V →L[ℂ] ℂ := (H u).toContinuousLinearMap
  change ‖f‖ ≤ ‖hermitianBilin H‖ * ‖u‖
  apply f.opNorm_le_bound (M := ‖hermitianBilin H‖ * ‖u‖)
    (mul_nonneg (norm_nonneg (hermitianBilin H)) (norm_nonneg u))
  exact hermitian_norm_le H u

end Bounds

/-- The inverse factor of automorphy is the summand of the theta series. -/
def thetaTerm (l z : V) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * H l z + (Real.pi : ℂ) * H l l))

theorem thetaTerm_eq_inverse (l z : V) :
    thetaTerm H l z = (doubledAutomorphy H l z)⁻¹ := Complex.exp_neg _

@[simp]
theorem thetaTerm_zero (z : V) : thetaTerm H 0 z = 1 := by
  simp [thetaTerm]

theorem thetaTerm_norm (l z : V) :
    ‖thetaTerm H l z‖ =
      Real.exp (-2 * Real.pi * (H l z).re - Real.pi * (H l l).re) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem hermitian_self_eq_real
    (hsym : ∀ u v : V, H v u = star (H u v)) (u : V) :
    H u u = ((H u u).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact hermitian_imaginary_self H hsym u

theorem thetaTerm_at_zero
    (hsym : ∀ u v : V, H v u = star (H u v)) (l : V) :
    thetaTerm H l 0 = (Real.exp (-Real.pi * (H l l).re) : ℂ) := by
  rw [thetaTerm, map_zero, mul_zero, zero_add, hermitian_self_eq_real H hsym l,
    Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- A theta series indexed by the original additive lattice. -/
def theta (Λ : AddSubgroup V) (z : V) : ℂ := ∑' l : Λ, thetaTerm H l z

theorem thetaTerm_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (l m : Λ) (z : V) :
    thetaTerm H l (z + m) = doubledAutomorphy H m z * thetaTerm H (l + m) z := by
  rw [thetaTerm_eq_inverse, thetaTerm_eq_inverse,
    doubledAutomorphy_add H hsym Λ hint l m z l.property m.property,
    mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (doubledAutomorphy_ne_zero H m z), one_mul]

theorem theta_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (m : Λ) (z : V) :
    theta H Λ (z + m) = doubledAutomorphy H m z * theta H Λ z := by
  unfold theta
  simp_rw [thetaTerm_translation H hsym Λ hint]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight m).tsum_eq (fun l : Λ => thetaTerm H l z)

section ThetaAnalytic

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

def thetaMajorant (c R : ℝ) (l : Λ) : ℝ :=
  Real.exp (-(Real.pi * c) * ‖l‖ ^ 2 +
    (2 * Real.pi * ‖hermitianBilin H‖ * R) * ‖l‖)

theorem thetaMajorant_summable (c R : ℝ) (hc : 0 < c) :
    Summable (thetaMajorant H Λ c R) := by
  let : DiscreteTopology Λ.toIntSubmodule := inferInstanceAs (DiscreteTopology Λ)
  exact AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_summable Λ.toIntSubmodule _ _ (mul_pos Real.pi_pos hc)

omit [DiscreteTopology Λ] in
theorem thetaTerm_norm_le (c R : ℝ)
    (hbound : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).re)
    (l : Λ) (z : V) (hz : ‖z‖ ≤ R) :
    ‖thetaTerm H l z‖ ≤ thetaMajorant H Λ c R l := by
  rw [thetaTerm_norm, thetaMajorant]
  apply Real.exp_le_exp.mpr
  have hh : -(H l z).re ≤ ‖hermitianBilin H‖ * ‖(l : V)‖ * R := by
    calc
      -(H l z).re ≤ ‖H l z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ ‖hermitianBilin H‖ * ‖(l : V)‖ * ‖z‖ := hermitian_norm_le H l z
      _ ≤ ‖hermitianBilin H‖ * ‖(l : V)‖ * R := by gcongr
  have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * Real.pi by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hbound l) Real.pi_pos.le
  change -2 * Real.pi * (H l z).re - Real.pi * (H l l).re ≤
    -(Real.pi * c) * ‖(l : V)‖ ^ 2 +
      (2 * Real.pi * ‖hermitianBilin H‖ * R) * ‖(l : V)‖
  nlinarith

theorem thetaTerm_summable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (z : V) :
    Summable (fun l : Λ => thetaTerm H l z) := by
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  exact (thetaMajorant_summable H Λ c ‖z‖ hc).of_norm_bounded
    (fun l => thetaTerm_norm_le H Λ c ‖z‖ hbound l z le_rfl)

theorem theta_at_zero_re_ge_one
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) :
    1 ≤ (theta H Λ 0).re := by
  have hs := Complex.hasSum_re (thetaTerm_summable H Λ hpos 0).hasSum
  rw [theta, Complex.re_tsum (thetaTerm_summable H Λ hpos 0)]
  have hn : ∀ l : Λ, 0 ≤ (thetaTerm H l 0).re := by
    intro l
    rw [thetaTerm_at_zero H hsym, Complex.ofReal_re]
    exact (Real.exp_pos _).le
  simpa only [AddSubgroup.coe_zero, thetaTerm_zero, Complex.one_re] using
    (Summable.le_tsum hs.summable (0 : Λ) (fun l _ => hn l))

theorem theta_at_zero_ne_zero
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) : theta H Λ 0 ≠ 0 := by
  intro h
  have hp := theta_at_zero_re_ge_one H Λ hsym hpos
  rw [h, Complex.zero_re] at hp
  norm_num at hp

def thetaTermDerivative (l z : V) : V →L[ℂ] ℂ :=
  thetaTerm H l z • ((-2 * (Real.pi : ℂ)) • (H l).toContinuousLinearMap)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V] in
theorem thetaTerm_hasFDerivAt (l z : V) :
    HasFDerivAt (thetaTerm H l) (thetaTermDerivative H l z) z := by
  have h := (((H l).toContinuousLinearMap.hasFDerivAt (x := z)).const_smul
    (-2 * (Real.pi : ℂ))).add_const (-(Real.pi : ℂ) * H l l)
  convert! h.cexp using 1
  · funext w
    unfold thetaTerm
    congr 1
    change -(2 * (Real.pi : ℂ) * H l w + (Real.pi : ℂ) * H l l) =
      (-2 * (Real.pi : ℂ)) * H l w + (-(Real.pi : ℂ)) * H l l
    ring
  · unfold thetaTermDerivative thetaTerm
    congr 2
    change -(2 * (Real.pi : ℂ) * H l z + (Real.pi : ℂ) * H l l) =
      (-2 * (Real.pi : ℂ)) * H l z + (-(Real.pi : ℂ)) * H l l
    ring

def thetaDerivativeMajorant (c R : ℝ) (l : Λ) : ℝ :=
  (2 * Real.pi * ‖hermitianBilin H‖) * (‖l‖ * thetaMajorant H Λ c R l)

theorem thetaDerivativeMajorant_summable (c R : ℝ) (hc : 0 < c) :
    Summable (thetaDerivativeMajorant H Λ c R) := by
  let : DiscreteTopology Λ.toIntSubmodule := inferInstanceAs (DiscreteTopology Λ)
  have hs : Summable (fun l : Λ => ‖l‖ ^ 1 *
      Real.exp (-(Real.pi * c) * ‖l‖ ^ 2 +
        (2 * Real.pi * ‖hermitianBilin H‖ * R) * ‖l‖)) :=
    AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_poly_summable Λ.toIntSubmodule
    (Real.pi * c) (2 * Real.pi * ‖hermitianBilin H‖ * R)
    (mul_pos Real.pi_pos hc) 1
  have h := hs.mul_left (2 * Real.pi * ‖hermitianBilin H‖)
  change Summable (fun l : Λ => (2 * Real.pi * ‖hermitianBilin H‖) *
    (‖l‖ * Real.exp (-(Real.pi * c) * ‖l‖ ^ 2 +
      (2 * Real.pi * ‖hermitianBilin H‖ * R) * ‖l‖)))
  simpa only [pow_one] using h

omit [DiscreteTopology Λ] in
theorem thetaTermDerivative_norm_le (c R : ℝ)
    (hbound : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).re)
    (l : Λ) (z : V) (hz : ‖z‖ ≤ R) :
    ‖thetaTermDerivative H l z‖ ≤ thetaDerivativeMajorant H Λ c R l := by
  rw [thetaTermDerivative, norm_smul, norm_smul]
  have hc : ‖(-2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by simp
  rw [hc]
  calc
    ‖thetaTerm H l z‖ * (2 * Real.pi * ‖(H l).toContinuousLinearMap‖) ≤
        thetaMajorant H Λ c R l * (2 * Real.pi * (‖hermitianBilin H‖ * ‖(l : V)‖)) := by
      gcongr
      · exact (Real.exp_pos _).le
      · exact thetaTerm_norm_le H Λ c R hbound l z hz
      · exact hermitian_linear_norm_le H l
    _ = thetaDerivativeMajorant H Λ c R l := by
      unfold thetaDerivativeMajorant
      change _ = (2 * Real.pi * ‖hermitianBilin H‖) * (‖(l : V)‖ * thetaMajorant H Λ c R l)
      ring

/-- Gaussian derivative estimates prove holomorphicity of the actual series. -/
theorem theta_hasFDerivAt
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (z : V) :
    HasFDerivAt (theta H Λ) (∑' l : Λ, thetaTermDerivative H l z) z := by
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball (0 : V) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  exact hasFDerivAt_tsum_of_isPreconnected
    (thetaDerivativeMajorant_summable H Λ c R hc) Metric.isOpen_ball
    (convex_ball (0 : V) R).isPreconnected
    (fun l w _ => thetaTerm_hasFDerivAt H l w)
    (fun l w hw => thetaTermDerivative_norm_le H Λ c R hbound l w
      (show ‖w‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hw).le)
    (Metric.mem_ball_self hR) (thetaTerm_summable H Λ hpos 0) hz

theorem theta_differentiable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) : Differentiable ℂ (theta H Λ) :=
  fun z => (theta_hasFDerivAt H Λ hpos z).differentiableAt

end ThetaAnalytic

/-- The right-hand data of RiemannProjectivity produce a nonzero entire theta function with
the required lattice automorphy, without additional real-space hypotheses. -/
theorem exists_nonzero_holomorphic_theta [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) [DiscreteTopology Λ]
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∃ t : V → ℂ, Differentiable ℂ t ∧ t 0 ≠ 0 ∧
      ∀ (l : Λ) (z : V), t (z + l) = doubledAutomorphy H l z * t z := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact ⟨theta H Λ, theta_differentiable H Λ hpos, theta_at_zero_ne_zero H Λ hsym hpos,
    theta_translation H hsym Λ hint⟩

section Products

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]

/-- Three translates whose translation parameters sum to zero have the same
cubed multiplier. The two parameters are free. -/
def thetaTriple (a b z : V) : ℂ :=
  theta H Λ (z - a) * theta H Λ (z - b) * theta H Λ (z + a + b)

theorem thetaTriple_differentiable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (a b : V) :
    Differentiable ℂ (thetaTriple H Λ a b) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact ((theta_differentiable H Λ hpos |>.comp (differentiable_id.sub_const a)).mul
    (theta_differentiable H Λ hpos |>.comp (differentiable_id.sub_const b))).mul
    (theta_differentiable H Λ hpos |>.comp
      ((differentiable_id.add_const a).add_const b))

omit [FiniteDimensional ℂ V] in
theorem doubledAutomorphy_triple (l a b z : V) :
    doubledAutomorphy H l (z - a) * doubledAutomorphy H l (z - b) *
      doubledAutomorphy H l (z + a + b) = doubledAutomorphy H l z ^ 3 := by
  simp only [doubledAutomorphy, ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  simp only [map_sub, map_add]
  ring

omit [FiniteDimensional ℂ V] [DiscreteTopology Λ] in
theorem thetaTriple_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (a b : V) (l : Λ) (z : V) :
    thetaTriple H Λ a b (z + l) = doubledAutomorphy H l z ^ 3 * thetaTriple H Λ a b z := by
  unfold thetaTriple
  rw [show z + (l : V) - a = (z - a) + l by abel,
    show z + (l : V) - b = (z - b) + l by abel,
    show z + (l : V) + a + b = (z + a + b) + l by abel,
    theta_translation H hsym Λ hint, theta_translation H hsym Λ hint,
    theta_translation H hsym Λ hint]
  calc
    _ = (doubledAutomorphy H l (z - a) * doubledAutomorphy H l (z - b) *
          doubledAutomorphy H l (z + a + b)) *
        (theta H Λ (z - a) * theta H Λ (z - b) * theta H Λ (z + a + b)) := by ring
    _ = _ := by rw [doubledAutomorphy_triple]

/-- The identity theorem on a complex line shows that the triple family has
no common zero. This does not assert separation of points or tangent vectors. -/
theorem exists_thetaTriple_ne_zero
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (z : V) :
    ∃ a b : V, thetaTriple H Λ a b z ≠ 0 := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  by_contra! hzero
  let f : ℂ → ℂ := fun t => theta H Λ (z - t • z)
  let g : ℂ → ℂ := fun t => theta H Λ (z + t • z + t • z)
  have hf : Differentiable ℂ f := (theta_differentiable H Λ hpos).comp
    ((differentiable_const z).sub (differentiable_id.smul_const z))
  have hg : Differentiable ℂ g := (theta_differentiable H Λ hpos).comp
    (((differentiable_const z).add (differentiable_id.smul_const z)).add
      (differentiable_id.smul_const z))
  have hff : Differentiable ℂ (fun t => f t * f t) := hf.mul hf
  have hfg : ∀ t ∈ (Set.univ : Set ℂ), (f t * f t) * g t = 0 :=
    fun t _ => hzero (t • z) (t • z)
  have hff' : AnalyticOnNhd ℂ (fun t => f t * f t) Set.univ :=
    fun t _ => hff.analyticAt t
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun t _ => hg.analyticAt t
  rcases hff'.eq_zero_or_eq_zero_of_mul_eq_zero hg' hfg isPreconnected_univ with h | h
  · have hz := h 1 (Set.mem_univ _)
    have hn := theta_at_zero_ne_zero H Λ hsym hpos
    simp [f, hn] at hz
  · have hz := h (-(1 / 2 : ℂ)) (Set.mem_univ _)
    have he : z + (-(1 / 2 : ℂ)) • z + (-(1 / 2 : ℂ)) • z = 0 := by module
    apply theta_at_zero_ne_zero H Λ hsym hpos
    simpa only [g, he] using hz

omit [FiniteDimensional ℂ V] [DiscreteTopology Λ] in
theorem thetaTriple_ne_zero_of_mk_eq
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (a b x y : V)
    (hxy : (QuotientAddGroup.mk x : V ⧸ Λ) = QuotientAddGroup.mk y)
    (hx : thetaTriple H Λ a b x ≠ 0) : thetaTriple H Λ a b y ≠ 0 := by
  have hl : x - y ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hxy
  let l : Λ := ⟨x - y, hl⟩
  have he : y + (l : V) = x := by dsimp [l]; abel
  have ht := thetaTriple_translation H Λ hsym hint a b l y
  rw [he] at ht
  intro hy
  exact hx (by rw [ht, hy, mul_zero])

/-- Compactness extracts a finite family of entire functions with a common
multiplier and no common zero. The embedding requirements remain separate. -/
theorem exists_finite_thetaTriples [CompactSpace (V ⧸ Λ)]
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∃ s : Finset (V × V), ∀ z : V, ∃ ab ∈ s, thetaTriple H Λ ab.1 ab.2 z ≠ 0 := by
  classical
  let U (ab : V × V) : Set (V ⧸ Λ) :=
    QuotientAddGroup.mk '' {z : V | thetaTriple H Λ ab.1 ab.2 z ≠ 0}
  have hopen (ab : V × V) : IsOpen (U ab) :=
    QuotientAddGroup.isOpenMap_coe _
      (isOpen_ne_fun (thetaTriple_differentiable H Λ hpos ab.1 ab.2).continuous continuous_const)
  have hcover : (Set.univ : Set (V ⧸ Λ)) ⊆ ⋃ ab, U ab := by
    intro q _
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨a, b, h⟩ := exists_thetaTriple_ne_zero H Λ hsym hpos z
    exact Set.mem_iUnion.mpr ⟨(a, b), z, h, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨s, fun z => ?_⟩
  have hz := hs (Set.mem_univ (QuotientAddGroup.mk z : V ⧸ Λ))
  obtain ⟨ab, hab, w, hw, hwz⟩ :=
    (show ∃ ab ∈ s, ∃ w, thetaTriple H Λ ab.1 ab.2 w ≠ 0 ∧
        (QuotientAddGroup.mk w : V ⧸ Λ) = QuotientAddGroup.mk z from by
      simpa only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, exists_prop, U] using hz)
  exact ⟨ab, hab, thetaTriple_ne_zero_of_mk_eq H Λ hsym hint ab.1 ab.2 w z hwz hw⟩

end Products

section Powers

open Filter _root_.Topology

def powerHermitian (n : ℕ) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := (n : ℂ) • H

@[simp]
theorem powerHermitian_apply (n : ℕ) (u v : V) :
    powerHermitian H n u v = (n : ℂ) * H u v := rfl

theorem powerHermitian_symm
    (hsym : ∀ u v : V, H v u = star (H u v)) (n : ℕ) (u v : V) :
    powerHermitian H n v u = star (powerHermitian H n u v) := by
  simp [hsym u v]

theorem powerHermitian_positive
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n)
    (u : V) (hu : u ≠ 0) : 0 < (powerHermitian H n u u).re := by
  simp only [powerHermitian_apply, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  exact mul_pos (by exact_mod_cast hn) (hpos u hu)

theorem hermitian_self_nonneg
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (u : V) : 0 ≤ (H u u).re := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (hpos u hu).le

theorem hermitian_self_add_re
    (hsym : ∀ u v : V, H v u = star (H u v)) (u v : V) :
    (H (u + v) (u + v)).re = (H u u).re + 2 * (H v u).re + (H v v).re := by
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  have h := congrArg Complex.re (hsym u v)
  simp only [Complex.star_def, Complex.conj_re] at h
  linarith

theorem powerTerm_norm (n : ℕ) (l z : V) :
    ‖thetaTerm (powerHermitian H n) l z‖ =
      Real.exp ((n : ℝ) * (-2 * Real.pi * (H l z).re - Real.pi * (H l l).re)) := by
  rw [thetaTerm_norm]
  simp only [powerHermitian_apply, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  congr 1
  ring

theorem doubledAutomorphy_power (n : ℕ) (l z : V) :
    doubledAutomorphy (powerHermitian H n) l z = doubledAutomorphy H l z ^ n := by
  simp only [doubledAutomorphy, powerHermitian_apply, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem powerHermitian_integral (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (u : V) (hu : u ∈ Λ) (v : V) (hv : v ∈ Λ) :
    ∃ m : ℤ, (powerHermitian H n u v).im = (m : ℝ) := by
  obtain ⟨m, hm⟩ := hint u hu v hv
  refine ⟨(n : ℤ) * m, ?_⟩
  simp [Complex.mul_im, hm]

def powerMetricNorm (Λ : AddSubgroup V) (n : ℕ) (z : V) : ℝ :=
  ‖theta (powerHermitian H n) Λ z‖ * Real.exp (-Real.pi * (n : ℝ) * (H z z).re)

def powerGaussian (Λ : AddSubgroup V) (n : ℕ) (z : V) (l : Λ) : ℝ :=
  Real.exp (-Real.pi * (n : ℝ) * (H (z + l) (z + l)).re)

theorem powerTerm_weighted_norm
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V) (n : ℕ) (z : V) (l : Λ) :
    ‖thetaTerm (powerHermitian H n) l z‖ *
      Real.exp (-Real.pi * (n : ℝ) * (H z z).re) = powerGaussian H Λ n z l := by
  rw [powerTerm_norm, powerGaussian, ← Real.exp_add, hermitian_self_add_re H hsym]
  congr 1
  ring

theorem powerMetricNorm_nonneg (Λ : AddSubgroup V) (n : ℕ) (z : V) :
    0 ≤ powerMetricNorm H Λ n z := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem powerGaussian_le_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (Λ : AddSubgroup V) (n : ℕ) (hn : 0 < n) (z : V) (l : Λ) :
    powerGaussian H Λ n z l ≤ powerGaussian H Λ 1 z l := by
  unfold powerGaussian
  apply Real.exp_le_exp.mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := hermitian_self_nonneg H hpos (z + l)
  have hp := mul_nonneg Real.pi_pos.le hq
  norm_num only [Nat.cast_one, mul_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') hp]

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

theorem powerTerm_summable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (z : V) :
    Summable (fun l : Λ => thetaTerm (powerHermitian H n) l z) :=
  thetaTerm_summable _ Λ (powerHermitian_positive H hpos n hn) z

theorem powerTheta_differentiable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) :
    Differentiable ℂ (theta (powerHermitian H n) Λ) :=
  theta_differentiable _ Λ (powerHermitian_positive H hpos n hn)

theorem powerGaussian_summable
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (z : V) :
    Summable (powerGaussian H Λ n z) := by
  convert! (powerTerm_summable H Λ hpos n hn z).norm.mul_right
    (Real.exp (-Real.pi * (n : ℝ) * (H z z).re)) using 1
  funext l
  exact (powerTerm_weighted_norm H hsym Λ n z l).symm

theorem powerMetricNorm_le_gaussian
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (z : V) :
    powerMetricNorm H Λ n z ≤ ∑' l, powerGaussian H Λ n z l := by
  unfold powerMetricNorm theta
  calc
    _ ≤ (∑' l : Λ, ‖thetaTerm (powerHermitian H n) l z‖) *
        Real.exp (-Real.pi * (n : ℝ) * (H z z).re) :=
      mul_le_mul_of_nonneg_right
        (norm_tsum_le_tsum_norm (powerTerm_summable H Λ hpos n hn z).norm) (Real.exp_pos _).le
    _ = _ := by
      rw [← tsum_mul_right]
      exact tsum_congr (fun l => powerTerm_weighted_norm H hsym Λ n z l)

omit [DiscreteTopology Λ] in
theorem powerGaussian_le_majorant
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (c R : ℝ) (hbound : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).re)
    (n : ℕ) (hn : 0 < n) (z : V) (hz : ‖z‖ ≤ R) (l : Λ) :
    powerGaussian H Λ n z l ≤ thetaMajorant H Λ c R l := by
  apply (powerGaussian_le_one H hpos Λ n hn z l).trans
  rw [← powerTerm_weighted_norm H hsym]
  have ht : thetaTerm (powerHermitian H 1) l z = thetaTerm H l z := by
    simp [powerHermitian]
  rw [ht]
  apply le_trans _ (thetaTerm_norm_le H Λ c R hbound l z hz)
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hp := mul_nonneg Real.pi_pos.le (hermitian_self_nonneg H hpos z)
  norm_num only [Nat.cast_one, mul_one]
  linarith

omit [DiscreteTopology Λ] in
theorem powerGaussian_moving_tendsto_zero
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (w : ℕ → V) (z : V) (hw : Tendsto w atTop (𝓝 z)) (hz : z ∉ Λ) (l : Λ) :
    Tendsto (fun n : ℕ => powerGaussian H Λ n (w n) l) atTop (𝓝 0) := by
  have hne : z + (l : V) ≠ 0 := by
    intro h
    have he : z = -(l : V) := eq_neg_of_add_eq_zero_left h
    exact hz (he.symm ▸ Λ.neg_mem l.property)
  let q : ℝ := (H (z + l) (z + l)).re
  have hq : 0 < q := hpos (z + l) hne
  have ht := (hermitian_self_re_continuous H).continuousAt.tendsto.comp
    (hw.add_const (l : V))
  have hb : ∀ᶠ n in atTop, q / 2 ≤ (H (w n + l) (w n + l)).re :=
    (ht.eventually (lt_mem_nhds (show q / 2 < q by linarith))).mono (fun _ h => h.le)
  have ha : Real.exp (-Real.pi * q / 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos Real.pi_pos hq]
  apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    _ (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le ha)
  filter_upwards [hb] with n hn
  change Real.exp (-Real.pi * (n : ℝ) * (H (w n + l) (w n + l)).re) ≤
    Real.exp (-Real.pi * q / 2) ^ n
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hn
    (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  nlinarith

theorem powerMetricNorm_moving_tendsto_zero
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (w : ℕ → V) (z : V) (hw : Tendsto w atTop (𝓝 z)) (hz : z ∉ Λ) :
    Tendsto (fun n : ℕ => powerMetricNorm H Λ n (w n)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  let R : ℝ := ‖z‖ + 1
  have hb : ∀ᶠ n in atTop, ‖w n‖ ≤ R :=
    (hw.norm.eventually (gt_mem_nhds (show ‖z‖ < R by dsimp [R]; linarith))).mono
      (fun _ h => h.le)
  have h := tendsto_tsum_of_dominated_convergence (thetaMajorant_summable H Λ c R hc)
    (fun l => powerGaussian_moving_tendsto_zero H Λ hpos w z hw hz l)
    (show ∀ᶠ n : ℕ in atTop, ∀ l : Λ,
        ‖powerGaussian H Λ n (w n) l‖ ≤ thetaMajorant H Λ c R l from by
      filter_upwards [eventually_ge_atTop 1, hb] with n hn hR l
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ powerGaussian H Λ n (w n) l from (Real.exp_pos _).le)]
      exact powerGaussian_le_majorant H Λ hsym hpos c R hbound n hn (w n) hR l)
  simp only [tsum_zero] at h
  apply squeeze_zero' (Eventually.of_forall (fun n => powerMetricNorm_nonneg H Λ n (w n))) _ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact powerMetricNorm_le_gaussian H Λ hsym hpos n hn (w n)

omit [DiscreteTopology Λ] in
theorem powerTerm_small_norm_le (n : ℕ) (C : ℝ) (l z : V) (hz : (n : ℝ) * ‖z‖ ≤ C) :
    ‖thetaTerm (powerHermitian H n) l z‖ ≤
      Real.exp (-(n : ℝ) * Real.pi * (H l l).re +
        2 * Real.pi * ‖hermitianBilin H‖ * ‖l‖ * C) := by
  rw [powerTerm_norm]
  apply Real.exp_le_exp.mpr
  have hl : (n : ℝ) * (-(H l z).re) ≤ ‖hermitianBilin H‖ * ‖l‖ * C := by
    calc
      (n : ℝ) * (-(H l z).re) ≤ (n : ℝ) * ‖H l z‖ :=
        mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
          (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * (‖hermitianBilin H‖ * ‖l‖ * ‖z‖) := by
        gcongr
        exact hermitian_norm_le H l z
      _ = (‖hermitianBilin H‖ * ‖l‖) * ((n : ℝ) * ‖z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz
        (mul_nonneg (norm_nonneg (hermitianBilin H)) (norm_nonneg l))
  have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

omit [DiscreteTopology Λ] in
theorem powerTerm_small_norm_le_majorant
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (c C : ℝ) (hbound : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).re)
    (n : ℕ) (hn : 0 < n) (l : Λ) (z : V) (hz : (n : ℝ) * ‖z‖ ≤ C) :
    ‖thetaTerm (powerHermitian H n) l z‖ ≤ thetaMajorant H Λ c C l := by
  apply (powerTerm_small_norm_le H n C l z hz).trans
  rw [thetaMajorant]
  apply Real.exp_le_exp.mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : c * ‖(l : V)‖ ^ 2 ≤ (n : ℝ) * (H l l).re :=
    (hbound l).trans (le_mul_of_one_le_left (hermitian_self_nonneg H hpos l) hn')
  have h := mul_le_mul_of_nonneg_left hq Real.pi_pos.le
  change -(n : ℝ) * Real.pi * (H l l).re + 2 * Real.pi * ‖hermitianBilin H‖ * ‖(l : V)‖ * C ≤
    -(Real.pi * c) * ‖(l : V)‖ ^ 2 + (2 * Real.pi * ‖hermitianBilin H‖ * C) * ‖(l : V)‖
  nlinarith

omit [DiscreteTopology Λ] in
theorem powerTerm_small_tendsto_zero
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (w : ℕ → V) (C : ℝ) (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) * ‖w n‖ ≤ C)
    (l : V) (hl : l ≠ 0) :
    Tendsto (fun n : ℕ => thetaTerm (powerHermitian H n) l (w n)) atTop (𝓝 0) := by
  have hq := hpos l hl
  have ha : Real.exp (-Real.pi * (H l l).re) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos Real.pi_pos hq]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le ha).mul_const
    (Real.exp (2 * Real.pi * ‖hermitianBilin H‖ * ‖l‖ * C))
  rw [zero_mul] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [hw] with n hn
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  convert! powerTerm_small_norm_le H n C l (w n) hn using 1
  congr 1
  ring

theorem powerTheta_small_tendsto_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (w : ℕ → V) (C : ℝ) (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) * ‖w n‖ ≤ C) :
    Tendsto (fun n : ℕ => theta (powerHermitian H n) Λ (w n)) atTop (𝓝 1) := by
  classical
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  have ht : ∀ l : Λ, Tendsto (fun n : ℕ => thetaTerm (powerHermitian H n) l (w n))
      atTop (𝓝 (if l = 0 then (1 : ℂ) else 0)) := by
    intro l
    by_cases hl : l = 0
    · simp only [hl, AddSubgroup.coe_zero, thetaTerm_zero, ↓reduceIte]
      exact tendsto_const_nhds
    · rw [ite_eq_right hl]
      exact powerTerm_small_tendsto_zero H hpos w C hw l (fun h => hl (Subtype.ext h))
  have h := tendsto_tsum_of_dominated_convergence (thetaMajorant_summable H Λ c C hc) ht
    (show ∀ᶠ n : ℕ in atTop, ∀ l : Λ,
        ‖thetaTerm (powerHermitian H n) l (w n)‖ ≤ thetaMajorant H Λ c C l from by
      filter_upwards [eventually_ge_atTop 1, hw] with n hn hC l
      exact powerTerm_small_norm_le_majorant H Λ hpos c C hbound n hn l (w n) hC)
  simpa only [theta, tsum_ite_eq] using h

theorem powerMetricNorm_small_tendsto_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (w : ℕ → V) (C : ℝ) (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) * ‖w n‖ ≤ C)
    (hw0 : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => powerMetricNorm H Λ n (w n)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (‖hermitianBilin H‖ * C) * ‖w n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hw0.norm.const_mul (‖hermitianBilin H‖ * C)
  have hq : Tendsto (fun n : ℕ => (n : ℝ) * (H (w n) (w n)).re) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n =>
      mul_nonneg (Nat.cast_nonneg n) (hermitian_self_nonneg H hpos (w n)))) _ ht
    filter_upwards [hw] with n hn
    calc
      (n : ℝ) * (H (w n) (w n)).re ≤ (n : ℝ) * ‖H (w n) (w n)‖ :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (Complex.abs_re_le_norm _))
          (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * (‖hermitianBilin H‖ * ‖w n‖ * ‖w n‖) := by
        gcongr
        exact hermitian_norm_le H (w n) (w n)
      _ = (‖hermitianBilin H‖ * ‖w n‖) * ((n : ℝ) * ‖w n‖) := by ring
      _ ≤ (‖hermitianBilin H‖ * ‖w n‖) * C :=
        mul_le_mul_of_nonneg_left hn
          (mul_nonneg (norm_nonneg (hermitianBilin H)) (norm_nonneg (w n)))
      _ = _ := by ring
  have he : Tendsto (fun n : ℕ => Real.exp (-Real.pi * (n : ℝ) * (H (w n) (w n)).re))
      atTop (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp (hq.const_mul (-Real.pi))
    convert! h using 1
    all_goals simp only [Function.comp_def, ← mul_assoc, mul_zero, Real.exp_zero]
  have h := (powerTheta_small_tendsto_one H Λ hpos w C hw).norm.mul he
  simpa only [powerMetricNorm, norm_one, one_mul] using h

end Powers

section LatticeApproximation

open Filter _root_.Topology

variable (Λ : AddSubgroup V) [CompactSpace (V ⧸ Λ)]

omit [NormedSpace ℂ V] in
/-- Compactness of the quotient gives a uniform distance bound to the lattice. -/
theorem exists_rounding_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : V, ∃ l : Λ, ‖z - l‖ ≤ C := by
  classical
  let U (z : V) : Set (V ⧸ Λ) := QuotientAddGroup.mk '' Metric.ball z 1
  have hopen (z : V) : IsOpen (U z) := QuotientAddGroup.isOpenMap_coe _ Metric.isOpen_ball
  have hcover : (Set.univ : Set (V ⧸ Λ)) ⊆ ⋃ z, U z := by
    intro q _
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨z, z, Metric.mem_ball_self zero_lt_one, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨(∑ z ∈ s, ‖z‖) + 1, by positivity, fun z => ?_⟩
  have hz := hs (Set.mem_univ (QuotientAddGroup.mk z : V ⧸ Λ))
  obtain ⟨c, hc, w, hw, hwz⟩ :=
    (show ∃ c ∈ s, ∃ w ∈ Metric.ball c 1,
        (QuotientAddGroup.mk w : V ⧸ Λ) = QuotientAddGroup.mk z from by
      simpa only [Set.mem_iUnion, Set.mem_image, exists_prop, U] using hz)
  have hl : z - w ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hwz.symm
  refine ⟨⟨z - w, hl⟩, ?_⟩
  change ‖z - (z - w)‖ ≤ _
  rw [sub_sub_cancel]
  have hc' : ‖c‖ ≤ ∑ x ∈ s, ‖x‖ := Finset.single_le_sum (fun x _ => norm_nonneg x) hc
  have hw' : ‖w - c‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hn := norm_add_le (w - c) c
  rw [sub_add_cancel] at hn
  linarith

def roundingBound : ℝ := (exists_rounding_bound Λ).choose

omit [NormedSpace ℂ V] in
theorem roundingBound_nonneg : 0 ≤ roundingBound Λ := (exists_rounding_bound Λ).choose_spec.1

def roundToLattice (z : V) : Λ := ((exists_rounding_bound Λ).choose_spec.2 z).choose

omit [NormedSpace ℂ V] in
theorem roundToLattice_norm_le (z : V) : ‖z - roundToLattice Λ z‖ ≤ roundingBound Λ :=
  ((exists_rounding_bound Λ).choose_spec.2 z).choose_spec

def divisionApproximation (n : ℕ) (z : V) : V :=
  (n : ℝ)⁻¹ • (roundToLattice Λ ((n : ℝ) • z) : V)

theorem divisionApproximation_smul (n : ℕ) (hn : 0 < n) (z : V) :
    (n : ℝ) • divisionApproximation Λ n z = roundToLattice Λ ((n : ℝ) • z) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [divisionApproximation, smul_smul, mul_inv_cancel₀ hn', one_smul]

theorem divisionApproximation_mem (n : ℕ) (hn : 0 < n) (z : V) :
    n • divisionApproximation Λ n z ∈ Λ := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, divisionApproximation_smul Λ n hn z]
  exact (roundToLattice Λ ((n : ℝ) • z)).property

theorem divisionApproximation_scaled_error (n : ℕ) (hn : 0 < n) (z : V) :
    (n : ℝ) * ‖z - divisionApproximation Λ n z‖ ≤ roundingBound Λ := by
  have he : (n : ℝ) • (z - divisionApproximation Λ n z) =
      (n : ℝ) • z - roundToLattice Λ ((n : ℝ) • z) := by
    rw [smul_sub, divisionApproximation_smul Λ n hn z]
  have h := roundToLattice_norm_le Λ ((n : ℝ) • z)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at h
  exact h

theorem divisionApproximation_error_tendsto_zero (z : V) :
    Tendsto (fun n : ℕ => z - divisionApproximation Λ n z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    _ (tendsto_const_div_atTop_nhds_zero_nat (roundingBound Λ))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  apply (le_div_iff₀ hn').mpr
  simpa only [mul_comm] using divisionApproximation_scaled_error Λ n hn z

theorem divisionApproximation_tendsto (z : V) :
    Tendsto (fun n : ℕ => divisionApproximation Λ n z) atTop (𝓝 z) := by
  have h := (tendsto_const_nhds (x := z)).sub (divisionApproximation_error_tendsto_zero Λ z)
  simpa only [sub_sub_cancel, sub_zero] using h

end LatticeApproximation

section CenteredPowers

open Filter _root_.Topology

theorem hermitian_nsmul_left (n : ℕ) (u z : V) : H (n • u) z = (n : ℂ) * H u z := by
  simp

def centerFactor (n : ℕ) (u z : V) : ℂ :=
  Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * H u z - (Real.pi : ℂ) * H u u))

def centeredTheta (Λ : AddSubgroup V) (n : ℕ) (u z : V) : ℂ :=
  centerFactor H n u z * theta (powerHermitian H n) Λ (z - u)

theorem centerFactor_ne_zero (n : ℕ) (u z : V) : centerFactor H n u z ≠ 0 :=
  Complex.exp_ne_zero _

theorem centerFactor_norm (n : ℕ) (u z : V) :
    ‖centerFactor H n u z‖ =
      Real.exp ((n : ℝ) * (2 * Real.pi * (H u z).re - Real.pi * (H u u).re)) := by
  rw [centerFactor, Complex.norm_exp]
  congr 1
  simp

theorem hermitian_self_sub_re
    (hsym : ∀ u v : V, H v u = star (H u v)) (z u : V) :
    (H (z - u) (z - u)).re = (H z z).re - 2 * (H u z).re + (H u u).re := by
  have h := congrArg Complex.re (hsym u z)
  simp only [Complex.star_def, Complex.conj_re] at h
  simp only [map_sub, LinearMap.sub_apply, Complex.sub_re]
  linarith

theorem centeredTheta_weighted_norm
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V) (n : ℕ) (u z : V) :
    ‖centeredTheta H Λ n u z‖ * Real.exp (-Real.pi * (n : ℝ) * (H z z).re) =
      powerMetricNorm H Λ n (z - u) := by
  rw [centeredTheta, norm_mul, centerFactor_norm, powerMetricNorm]
  rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
  congr 1
  rw [hermitian_self_sub_re H hsym]
  congr 1
  ring

theorem centerFactor_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (u z : V) (hu : n • u ∈ Λ) (l : Λ) :
    centerFactor H n u (z + l) * doubledAutomorphy H l (z - u) ^ n =
      doubledAutomorphy H l z ^ n * centerFactor H n u z := by
  obtain ⟨k, hk⟩ := hint l l.property (n • u) hu
  have hs := hermitian_skew H hsym l (n • u)
  rw [hk, hermitian_nsmul_left, map_nsmul, nsmul_eq_mul] at hs
  push_cast at hs
  simp only [centerFactor, doubledAutomorphy, ← Complex.exp_nat_mul,
    ← Complex.exp_add, map_add, map_sub]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(2 * k), ?_⟩
  push_cast
  linear_combination -2 * (Real.pi : ℂ) * hs

theorem centeredTheta_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (Λ : AddSubgroup V)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (u z : V) (hu : n • u ∈ Λ) (l : Λ) :
    centeredTheta H Λ n u (z + l) = doubledAutomorphy H l z ^ n * centeredTheta H Λ n u z := by
  unfold centeredTheta
  rw [show z + (l : V) - u = (z - u) + l by abel,
    theta_translation _ (powerHermitian_symm H hsym n) Λ (powerHermitian_integral H Λ hint n),
    doubledAutomorphy_power, ← mul_assoc, centerFactor_translation H hsym Λ hint n u z hu l,
    mul_assoc]

variable [FiniteDimensional ℂ V]

theorem centerFactor_differentiable (n : ℕ) (u : V) : Differentiable ℂ (centerFactor H n u) :=
  (((((H u).toContinuousLinearMap.differentiable).const_mul _).sub_const _).const_mul _).cexp

theorem centeredTheta_differentiable (Λ : AddSubgroup V) [DiscreteTopology Λ]
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (u : V) :
    Differentiable ℂ (centeredTheta H Λ n u) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact (centerFactor_differentiable H n u).mul
    ((powerTheta_differentiable H Λ hpos n hn).comp (differentiable_id.sub_const u))

variable (Λ : AddSubgroup V) [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)]

def peakTheta (n : ℕ) (p z : V) : ℂ := centeredTheta H Λ n (divisionApproximation Λ n p) z

theorem peakTheta_differentiable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (p : V) :
    Differentiable ℂ (peakTheta H Λ n p) := centeredTheta_differentiable H Λ hpos n hn _

omit [FiniteDimensional ℂ V] [DiscreteTopology Λ] in
theorem peakTheta_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (p z : V) (l : Λ) :
    peakTheta H Λ n p (z + l) = doubledAutomorphy H l z ^ n * peakTheta H Λ n p z :=
  centeredTheta_translation H hsym Λ hint n _ z (divisionApproximation_mem Λ n hn p) l

def peakMetricNorm (n : ℕ) (p z : V) : ℝ :=
  ‖peakTheta H Λ n p z‖ * Real.exp (-Real.pi * (n : ℝ) * (H z z).re)

omit [FiniteDimensional ℂ V] [DiscreteTopology Λ] in
theorem peakMetricNorm_eq
    (hsym : ∀ u v : V, H v u = star (H u v)) (n : ℕ) (p z : V) :
    peakMetricNorm H Λ n p z = powerMetricNorm H Λ n (z - divisionApproximation Λ n p) :=
  centeredTheta_weighted_norm H hsym Λ n _ z

theorem peakMetricNorm_tendsto_one
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (p : V) :
    Tendsto (fun n : ℕ => peakMetricNorm H Λ n p p) atTop (𝓝 1) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  simp_rw [peakMetricNorm_eq H Λ hsym]
  apply powerMetricNorm_small_tendsto_one H Λ hpos _ (roundingBound Λ) _
    (divisionApproximation_error_tendsto_zero Λ p)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact divisionApproximation_scaled_error Λ n hn p

theorem peakMetricNorm_tendsto_zero
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (p z : V) (hz : z - p ∉ Λ) :
    Tendsto (fun n : ℕ => peakMetricNorm H Λ n p z) atTop (𝓝 0) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  simp_rw [peakMetricNorm_eq H Λ hsym]
  exact powerMetricNorm_moving_tendsto_zero H Λ hsym hpos _ (z - p)
    ((tendsto_const_nhds (x := z)).sub (divisionApproximation_tendsto Λ p)) hz

theorem peakTheta_eventually_separates
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (p q : V) (hpq : q - p ∉ Λ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      peakTheta H Λ n p p * peakTheta H Λ n q q ≠ peakTheta H Λ n p q * peakTheta H Λ n q p := by
  have hqp : p - q ∉ Λ := by
    intro h
    apply hpq
    simpa only [neg_sub] using Λ.neg_mem h
  have hdiag := (peakMetricNorm_tendsto_one H Λ hsym hpos p).mul
    (peakMetricNorm_tendsto_one H Λ hsym hpos q)
  have hoff := (peakMetricNorm_tendsto_zero H Λ hsym hpos p q hpq).mul
    (peakMetricNorm_tendsto_zero H Λ hsym hpos q p hqp)
  rw [one_mul] at hdiag
  rw [zero_mul] at hoff
  filter_upwards [eventually_ge_atTop 1,
    hdiag.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hoff.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn hd ho
  refine ⟨hn, fun he => ?_⟩
  have he' := congrArg norm he
  rw [norm_mul, norm_mul] at he'
  have hm : peakMetricNorm H Λ n p p * peakMetricNorm H Λ n q q =
      peakMetricNorm H Λ n p q * peakMetricNorm H Λ n q p := by
    unfold peakMetricNorm
    linear_combination
      (Real.exp (-Real.pi * (n : ℝ) * (H p p).re) *
        Real.exp (-Real.pi * (n : ℝ) * (H q q).re)) * he'
  linarith

/-- Positive integral Hermitian data supply holomorphic sections of one common
positive degree separating any prescribed distinct lattice cosets. -/
theorem exists_sections_separating_points
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (p q : V) (hpq : q - p ∉ Λ) :
    ∃ (n : ℕ) (s t : V → ℂ), 0 < n ∧ Differentiable ℂ s ∧ Differentiable ℂ t ∧
      (∀ (l : Λ) z, s (z + l) = doubledAutomorphy H l z ^ n * s z) ∧
      (∀ (l : Λ) z, t (z + l) = doubledAutomorphy H l z ^ n * t z) ∧
      s p * t q ≠ s q * t p := by
  obtain ⟨n, hn, hsep⟩ := (peakTheta_eventually_separates H Λ hsym hpos p q hpq).exists
  exact ⟨n, peakTheta H Λ n p, peakTheta H Λ n q, hn,
    peakTheta_differentiable H Λ hpos n hn p, peakTheta_differentiable H Λ hpos n hn q,
    fun l z => peakTheta_translation H Λ hsym hint n hn p z l,
    fun l z => peakTheta_translation H Λ hsym hint n hn q z l, hsep⟩

end CenteredPowers

section TangentEstimates

open Filter _root_.Topology

omit [NormedSpace ℂ V] in
theorem exists_lattice_norm_lower_bound (Λ : AddSubgroup V) [DiscreteTopology Λ] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l : Λ, l ≠ 0 → ρ ≤ ‖l‖ := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_singleton_iff.mp (isOpen_discrete ({0} : Set Λ))
  refine ⟨ρ, hρ, fun l hl => le_of_not_gt (fun h => hl (hball l ?_))⟩
  simpa only [dist_zero_right] using h

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

/-- Discreteness supplies a fixed neighborhood in which every nonzero lattice
term decays exponentially in the degree. -/
theorem exists_local_power_bound
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2) := by
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  obtain ⟨ρ, hρ, hlattice⟩ := exists_lattice_norm_lower_bound Λ
  let B : ℝ := ‖hermitianBilin H‖
  have hB : 0 ≤ B := norm_nonneg (hermitianBilin H)
  let R : ℝ := c * ρ / (4 * (B + 1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hR_eq : 4 * (B + 1) * R = c * ρ := by
    dsimp [R]
    field_simp
  refine ⟨Real.pi * c / 2, R, by positivity, hR, fun n l z hz => ?_⟩
  by_cases hl : l = 0
  · simp [hl]
  · have hlnorm : ρ ≤ ‖(l : V)‖ := hlattice l hl
    have hcoeff : 4 * B * R ≤ c * ‖(l : V)‖ := by
      have hh := mul_le_mul_of_nonneg_left hlnorm hc.le
      nlinarith
    have hh : -(H l z).re ≤ B * ‖(l : V)‖ * R := by
      calc
        -(H l z).re ≤ ‖H l z‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ ≤ B * ‖(l : V)‖ * ‖z‖ := hermitian_norm_le H l z
        _ ≤ B * ‖(l : V)‖ * R := by gcongr
    have hco := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (l : V))
    have hq := hbound (l : V)
    have hneg : -2 * (H l z).re - (H l l).re ≤ -(c / 2) * ‖(l : V)‖ ^ 2 := by
      nlinarith
    have hex := mul_le_mul_of_nonneg_left hneg
      (mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) Real.pi_pos.le)
    rw [powerTerm_norm]
    apply Real.exp_le_exp.mpr
    change (n : ℝ) * (-2 * Real.pi * (H l z).re - Real.pi * (H l l).re) ≤
      -(Real.pi * c / 2) * (n : ℝ) * ‖(l : V)‖ ^ 2
    nlinarith

omit [DiscreteTopology Λ] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V] in
theorem powerTerm_tendsto_of_local_bound (a R : ℝ) (ha : 0 < a)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2))
    (w : ℕ → V) (hw : ∀ᶠ n in atTop, ‖w n‖ ≤ R) (l : Λ) (hl : l ≠ 0) :
    Tendsto (fun n : ℕ => thetaTerm (powerHermitian H n) l (w n)) atTop (𝓝 0) := by
  have hlnorm : 0 < ‖l‖ := norm_pos_iff.mpr hl
  have hlt : Real.exp (-a * ‖l‖ ^ 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos ha (sq_pos_of_pos hlnorm)]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hlt)
  filter_upwards [hw] with n hn
  rw [← Real.exp_nat_mul]
  convert! hbound n l (w n) hn using 1
  congr 1
  ring

omit [DiscreteTopology Λ] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V] in
theorem powerTerm_le_of_local_bound (a R : ℝ) (ha : 0 < a)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2))
    (n : ℕ) (hn : 0 < n) (l : Λ) (z : V) (hz : ‖z‖ ≤ R) :
    ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * ‖l‖ ^ 2) := by
  apply (hbound n l z hz).trans
  apply Real.exp_le_exp.mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := mul_nonneg (sub_nonneg.mpr hn') (mul_nonneg ha.le (sq_nonneg ‖l‖))
  nlinarith

omit [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem powerTheta_tendsto_of_local_bound (a R : ℝ) (ha : 0 < a)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2))
    (w : ℕ → V) (hw : ∀ᶠ n in atTop, ‖w n‖ ≤ R) :
    Tendsto (fun n : ℕ => theta (powerHermitian H n) Λ (w n)) atTop (𝓝 1) := by
  classical
  let : DiscreteTopology Λ.toIntSubmodule := inferInstanceAs (DiscreteTopology Λ)
  have hs0 : Summable (fun l : Λ => Real.exp (-a * ‖l‖ ^ 2 + 0 * ‖l‖)) :=
    AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_summable Λ.toIntSubmodule a 0 ha
  have hs : Summable (fun l : Λ => Real.exp (-a * ‖l‖ ^ 2)) := by
    simpa only [zero_mul, add_zero] using hs0
  have ht : ∀ l : Λ, Tendsto (fun n : ℕ => thetaTerm (powerHermitian H n) l (w n))
      atTop (𝓝 (if l = 0 then (1 : ℂ) else 0)) := by
    intro l
    by_cases hl : l = 0
    · simp only [hl, AddSubgroup.coe_zero, thetaTerm_zero, ↓reduceIte]
      exact tendsto_const_nhds
    · rw [ite_eq_right hl]
      exact powerTerm_tendsto_of_local_bound H Λ a R ha hbound w hw l hl
  have h := tendsto_tsum_of_dominated_convergence hs ht
    (show ∀ᶠ n : ℕ in atTop, ∀ l : Λ,
        ‖thetaTerm (powerHermitian H n) l (w n)‖ ≤ Real.exp (-a * ‖l‖ ^ 2) from by
      filter_upwards [eventually_ge_atTop 1, hw] with n hn hR l
      exact powerTerm_le_of_local_bound H Λ a R ha hbound n hn l (w n) hR)
  simpa only [theta, tsum_ite_eq] using h

def normalizedPowerDerivative (n : ℕ) (z : V) : V →L[ℂ] ℂ :=
  ∑' l : Λ, thetaTerm (powerHermitian H n) l z •
    ((-2 * (Real.pi : ℂ)) • (H l).toContinuousLinearMap)

theorem fderiv_powerTheta
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (z : V) :
    fderiv ℂ (theta (powerHermitian H n) Λ) z = (n : ℂ) • normalizedPowerDerivative H Λ n z := by
  rw [(theta_hasFDerivAt _ Λ (powerHermitian_positive H hpos n hn) z).fderiv,
    normalizedPowerDerivative, ← tsum_const_smul'']
  apply tsum_congr
  intro l
  ext v
  simp only [thetaTermDerivative, smul_apply, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap', powerHermitian_apply]
  ring

theorem normalizedPowerDerivative_tendsto_of_local_bound (a R : ℝ) (ha : 0 < a)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2))
    (w : ℕ → V) (hw : ∀ᶠ n in atTop, ‖w n‖ ≤ R) :
    Tendsto (fun n : ℕ => normalizedPowerDerivative H Λ n (w n)) atTop (𝓝 0) := by
  let : DiscreteTopology Λ.toIntSubmodule := inferInstanceAs (DiscreteTopology Λ)
  let K : ℝ := 2 * Real.pi * ‖hermitianBilin H‖
  have hs0 : Summable (fun l : Λ => ‖l‖ ^ 1 * Real.exp (-a * ‖l‖ ^ 2 + 0 * ‖l‖)) :=
    AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_poly_summable Λ.toIntSubmodule a 0 ha 1
  have hs : Summable (fun l : Λ => K * (‖l‖ * Real.exp (-a * ‖l‖ ^ 2))) := by
    simpa only [pow_one, zero_mul, add_zero] using hs0.mul_left K
  have ht (l : Λ) : Tendsto (fun n : ℕ => thetaTerm (powerHermitian H n) l (w n) •
      ((-2 * (Real.pi : ℂ)) • (H l).toContinuousLinearMap)) atTop (𝓝 (0 : V →L[ℂ] ℂ)) := by
    by_cases hl : l = 0
    · have hz : (-2 * (Real.pi : ℂ)) • (H (l : V)).toContinuousLinearMap =
          (0 : V →L[ℂ] ℂ) := by
        ext v
        simp [hl]
      have hzero (c : ℂ) : c • (0 : V →L[ℂ] ℂ) = 0 := by ext v; simp
      simp only [hz, hzero]
      exact tendsto_const_nhds
    · have h := (powerTerm_tendsto_of_local_bound H Λ a R ha hbound w hw l hl).smul_const
        ((-2 * (Real.pi : ℂ)) • (H l).toContinuousLinearMap)
      have hz : (0 : ℂ) • ((-2 * (Real.pi : ℂ)) • (H (l : V)).toContinuousLinearMap) =
          (0 : V →L[ℂ] ℂ) := by ext v; simp
      rw [hz] at h
      exact h
  have h := tendsto_tsum_of_dominated_convergence hs ht
    (show ∀ᶠ n : ℕ in atTop, ∀ l : Λ,
        ‖thetaTerm (powerHermitian H n) l (w n) •
          ((-2 * (Real.pi : ℂ)) • (H l).toContinuousLinearMap)‖ ≤
        K * (‖l‖ * Real.exp (-a * ‖l‖ ^ 2)) from by
      filter_upwards [eventually_ge_atTop 1, hw] with n hn hR l
      rw [norm_smul, norm_smul]
      have hc : ‖(-2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by simp
      rw [hc]
      calc
        _ ≤ Real.exp (-a * ‖l‖ ^ 2) * (2 * Real.pi * (‖hermitianBilin H‖ * ‖(l : V)‖)) := by
          gcongr
          · exact powerTerm_le_of_local_bound H Λ a R ha hbound n hn l (w n) hR
          · exact hermitian_linear_norm_le H l
        _ = _ := by dsimp [K]; ring)
  simpa only [normalizedPowerDerivative, tsum_zero] using h

end TangentEstimates

section TangentSeparation

open Filter _root_.Topology

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V] in
theorem centerFactor_hasFDerivAt (n : ℕ) (u z : V) :
    HasFDerivAt (centerFactor H n u)
      (centerFactor H n u z • (((n : ℂ) * (2 * (Real.pi : ℂ))) •
        (H u).toContinuousLinearMap)) z := by
  have h := (((((H u).toContinuousLinearMap.hasFDerivAt (x := z)).const_smul
    (2 * (Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * H u u)).const_smul (n : ℂ)).cexp
  convert! h using 1
  simp [centerFactor, smul_smul]

theorem centeredTheta_fderiv
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (n : ℕ) (hn : 0 < n) (u z v : V) :
    fderiv ℂ (centeredTheta H Λ n u) z v =
      centerFactor H n u z * (n : ℂ) *
        (theta (powerHermitian H n) Λ (z - u) * (2 * (Real.pi : ℂ) * H u v) +
          normalizedPowerDerivative H Λ n (z - u) v) := by
  have ht := ((powerTheta_differentiable H Λ hpos n hn) (z - u)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const u)
  have h := (centerFactor_hasFDerivAt H n u z).mul ht
  have he := congrArg (fun f : V →L[ℂ] ℂ => f v) h.fderiv
  change fderiv ℂ (centeredTheta H Λ n u) z v = _ at he
  rw [fderiv_powerTheta H Λ hpos n hn (z - u)] at he
  convert! he using 1
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    LinearMap.coe_toContinuousLinearMap']
  ring

def tangentSeparationExpression (n : ℕ) (a b z v : V) : ℂ :=
  theta (powerHermitian H n) Λ (z - a) * theta (powerHermitian H n) Λ (z - b) *
      (2 * (Real.pi : ℂ) * H (b - a) v) +
    theta (powerHermitian H n) Λ (z - a) * normalizedPowerDerivative H Λ n (z - b) v -
    theta (powerHermitian H n) Λ (z - b) * normalizedPowerDerivative H Λ n (z - a) v

theorem centeredTheta_derivative_determinant
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (n : ℕ) (hn : 0 < n) (a b z v : V) :
    centeredTheta H Λ n a z * fderiv ℂ (centeredTheta H Λ n b) z v -
        centeredTheta H Λ n b z * fderiv ℂ (centeredTheta H Λ n a) z v =
      centerFactor H n a z * centerFactor H n b z * (n : ℂ) *
        tangentSeparationExpression H Λ n a b z v := by
  rw [centeredTheta_fderiv H Λ hpos n hn b z v, centeredTheta_fderiv H Λ hpos n hn a z v]
  simp only [centeredTheta, tangentSeparationExpression, map_sub, LinearMap.sub_apply]
  ring

theorem normalizedPowerDerivative_apply_tendsto (a R : ℝ) (ha : 0 < a)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-a * (n : ℝ) * ‖l‖ ^ 2))
    (w : ℕ → V) (hw : ∀ᶠ n in atTop, ‖w n‖ ≤ R) (v : V) :
    Tendsto (fun n : ℕ => normalizedPowerDerivative H Λ n (w n) v) atTop (𝓝 0) := by
  have hc : Continuous (fun f : V →L[ℂ] ℂ => f v) := continuous_id.clm_apply continuous_const
  have h := hc.continuousAt.tendsto.comp
    (normalizedPowerDerivative_tendsto_of_local_bound H Λ a R ha hbound w hw)
  exact h

theorem tangentSeparationExpression_tendsto (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (hbound : ∀ (n : ℕ) (l : Λ) (z : V), ‖z‖ ≤ R →
      ‖thetaTerm (powerHermitian H n) l z‖ ≤ Real.exp (-c * (n : ℝ) * ‖l‖ ^ 2))
    (a b : ℕ → V) (z d v : V) (ha : Tendsto a atTop (𝓝 z))
    (hb : Tendsto b atTop (𝓝 (z + d))) (hd : ‖d‖ < R) :
    Tendsto (fun n : ℕ => tangentSeparationExpression H Λ n (a n) (b n) z v)
      atTop (𝓝 (2 * (Real.pi : ℂ) * H d v)) := by
  have hwa : Tendsto (fun n : ℕ => z - a n) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := z)).sub ha
  have hwb : Tendsto (fun n : ℕ => z - b n) atTop (𝓝 (-d)) := by
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using (tendsto_const_nhds (x := z)).sub hb
  have hba : Tendsto (fun n : ℕ => b n - a n) atTop (𝓝 d) := by
    simpa only [add_sub_cancel_left] using hb.sub ha
  have hwaR : ∀ᶠ n in atTop, ‖z - a n‖ ≤ R :=
    (hwa.norm.eventually (gt_mem_nhds (by simpa using hR))).mono (fun _ h => h.le)
  have hwbR : ∀ᶠ n in atTop, ‖z - b n‖ ≤ R :=
    (hwb.norm.eventually (gt_mem_nhds (by simpa only [norm_neg] using hd))).mono (fun _ h => h.le)
  have hta := powerTheta_tendsto_of_local_bound H Λ c R hc hbound _ hwaR
  have htb := powerTheta_tendsto_of_local_bound H Λ c R hc hbound _ hwbR
  have hda := normalizedPowerDerivative_apply_tendsto H Λ c R hc hbound _ hwaR v
  have hdb := normalizedPowerDerivative_apply_tendsto H Λ c R hc hbound _ hwbR v
  have hcH : Continuous (fun u : V => H u v) :=
    (hermitianBilin H).continuous.clm_apply continuous_const
  have hH := hcH.continuousAt.tendsto.comp hba
  have h := (((hta.mul htb).mul (hH.const_mul (2 * (Real.pi : ℂ)))).add (hta.mul hdb)).sub
    (htb.mul hda)
  simpa only [tangentSeparationExpression, Function.comp_apply, one_mul, mul_zero, add_zero, sub_zero] using h

variable [CompactSpace (V ⧸ Λ)]

/-- Two sections in one positive degree detect every specified nonzero tangent
vector; the first section is nonzero at the specified point. -/
theorem exists_centeredTheta_separating_tangent
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (p v : V) (hv : v ≠ 0) :
    ∃ (n : ℕ) (a b : V), 0 < n ∧ n • a ∈ Λ ∧ n • b ∈ Λ ∧
      centeredTheta H Λ n a p ≠ 0 ∧
      centeredTheta H Λ n a p * fderiv ℂ (centeredTheta H Λ n b) p v ≠
        centeredTheta H Λ n b p * fderiv ℂ (centeredTheta H Λ n a) p v := by
  obtain ⟨c, R, hc, hR, hbound⟩ := exists_local_power_bound H Λ hpos
  let r : ℝ := R / (2 * ‖v‖)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hr : 0 < r := by dsimp [r]; positivity
  let d : V := r • v
  have hd : ‖d‖ < R := by
    have he : ‖d‖ = R / 2 := by
      simp only [d, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [r]
      field_simp
    rw [he]
    linarith
  have hHdpos : 0 < (H d v).re := by
    change 0 < (hermitianBilin H (r • v) v).re
    rw [map_smul, smul_apply]
    change 0 < (r • H v v).re
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_pos hr (hpos v hv)
  have hHd : H d v ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hHdpos
    exact lt_irrefl _ hHdpos
  have hlimit : 2 * (Real.pi : ℂ) * H d v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hHd
  let a : ℕ → V := fun n => divisionApproximation Λ n p
  let b : ℕ → V := fun n => divisionApproximation Λ n (p + d)
  have ha : Tendsto a atTop (𝓝 p) := divisionApproximation_tendsto Λ p
  have hb : Tendsto b atTop (𝓝 (p + d)) := divisionApproximation_tendsto Λ (p + d)
  have hD := tangentSeparationExpression_tendsto H Λ c R hc hR hbound a b p d v ha hb hd
  have hwa : Tendsto (fun n : ℕ => p - a n) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := p)).sub ha
  have hwaR : ∀ᶠ n in atTop, ‖p - a n‖ ≤ R :=
    (hwa.norm.eventually (gt_mem_nhds (by simpa using hR))).mono (fun _ h => h.le)
  have ht := powerTheta_tendsto_of_local_bound H Λ c R hc hbound _ hwaR
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      tangentSeparationExpression H Λ n (a n) (b n) p v ≠ 0 ∧
      theta (powerHermitian H n) Λ (p - a n) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1, hD.eventually_ne hlimit, ht.eventually_ne one_ne_zero]
      with n hn hDn htn
    exact ⟨hn, hDn, htn⟩
  obtain ⟨n, hn, hDn, htn⟩ := hev.exists
  refine ⟨n, a n, b n, hn, divisionApproximation_mem Λ n hn p,
    divisionApproximation_mem Λ n hn (p + d),
    mul_ne_zero (centerFactor_ne_zero H n (a n) p) htn, ?_⟩
  intro he
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hprod := mul_ne_zero (mul_ne_zero (mul_ne_zero
    (centerFactor_ne_zero H n (a n) p) (centerFactor_ne_zero H n (b n) p)) hn') hDn
  apply hprod
  rw [← centeredTheta_derivative_determinant H Λ hpos n hn (a n) (b n) p v, he, sub_self]

theorem exists_sections_separating_tangent
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (p v : V) (hv : v ≠ 0) :
    ∃ (n : ℕ) (s t : V → ℂ), 0 < n ∧ Differentiable ℂ s ∧ Differentiable ℂ t ∧
      (∀ (l : Λ) z, s (z + l) = doubledAutomorphy H l z ^ n * s z) ∧
      (∀ (l : Λ) z, t (z + l) = doubledAutomorphy H l z ^ n * t z) ∧
      s p ≠ 0 ∧ s p * fderiv ℂ t p v ≠ t p * fderiv ℂ s p v := by
  obtain ⟨n, a, b, hn, ha, hb, hs, hsep⟩ := exists_centeredTheta_separating_tangent H Λ hpos p v hv
  exact ⟨n, centeredTheta H Λ n a, centeredTheta H Λ n b, hn,
    centeredTheta_differentiable H Λ hpos n hn a, centeredTheta_differentiable H Λ hpos n hn b,
    fun l z => centeredTheta_translation H hsym Λ hint n a z ha l,
    fun l z => centeredTheta_translation H hsym Λ hint n b z hb l, hs, hsep⟩

end TangentSeparation

section SmoothSections

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

theorem theta_contDiff_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) : ContDiff ℂ 1 (theta H Λ) := by
  obtain ⟨c, hc, hbound⟩ := hermitian_exists_lower_bound H hpos
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun z => ∑' l : Λ, thetaTermDerivative H l z, ?_, theta_hasFDerivAt H Λ hpos⟩
  apply continuous_iff_continuousAt.mpr
  intro z
  let R : ℝ := ‖z‖ + 1
  have hz : z ∈ Metric.ball (0 : V) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  have hterm (l : Λ) : Continuous (thetaTermDerivative H l) := by
    have ht : Continuous (thetaTerm H l) :=
      (show Differentiable ℂ (thetaTerm H l) from fun w =>
        (thetaTerm_hasFDerivAt H l w).differentiableAt).continuous
    exact ht.smul continuous_const
  have hcont := continuousOn_tsum (s := Metric.ball (0 : V) R) (fun l : Λ => (hterm l).continuousOn)
    (thetaDerivativeMajorant_summable H Λ c R hc)
    (fun l w hw => thetaTermDerivative_norm_le H Λ c R hbound l w
      (show ‖w‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hw).le)
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hz)

theorem powerTheta_contDiff_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) :
    ContDiff ℂ 1 (theta (powerHermitian H n) Λ) :=
  theta_contDiff_one _ Λ (powerHermitian_positive H hpos n hn)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V] in
theorem centerFactor_contDiff_one (n : ℕ) (u : V) : ContDiff ℂ 1 (centerFactor H n u) := by
  have hH : ContDiff ℂ 1 (H u) := (H u).toContinuousLinearMap.contDiff
  exact (((hH.const_smul (2 * (Real.pi : ℂ))).sub contDiff_const).const_smul (n : ℂ)).cexp

theorem centeredTheta_contDiff_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (u : V) :
    ContDiff ℂ 1 (centeredTheta H Λ n u) :=
  (centerFactor_contDiff_one H n u).mul
    ((powerTheta_contDiff_one H Λ hpos n hn).comp (contDiff_id.sub contDiff_const))

theorem thetaTriple_contDiff_one
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (a b : V) :
    ContDiff ℂ 1 (thetaTriple H Λ a b) :=
  (((theta_contDiff_one H Λ hpos).comp (contDiff_id.sub contDiff_const)).mul
    ((theta_contDiff_one H Λ hpos).comp (contDiff_id.sub contDiff_const))).mul
    ((theta_contDiff_one H Λ hpos).comp ((contDiff_id.add contDiff_const).add contDiff_const))

theorem peakTheta_contDiff_one [CompactSpace (V ⧸ Λ)]
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (n : ℕ) (hn : 0 < n) (p : V) :
    ContDiff ℂ 1 (peakTheta H Λ n p) := centeredTheta_contDiff_one H Λ hpos n hn _

end SmoothSections

/-- A continuously differentiable holomorphic function with the multiplier of
a specified power of the polarization. -/
structure ThetaSection (Λ : AddSubgroup V) (n : ℕ) where
  toFun : V → ℂ
  regular : ContDiff ℂ 1 toFun
  translates : ∀ (l : Λ) (z : V), toFun (z + l) = doubledAutomorphy H l z ^ n * toFun z

namespace ThetaSection

variable {H} {Λ : AddSubgroup V} {n m : ℕ}

instance : CoeFun (ThetaSection H Λ n) (fun _ => V → ℂ) := ⟨toFun⟩

theorem differentiable (s : ThetaSection H Λ n) : Differentiable ℂ s :=
  s.regular.differentiable (by norm_num)

theorem continuous (s : ThetaSection H Λ n) : Continuous s := s.regular.continuous

theorem continuous_fderiv (s : ThetaSection H Λ n) : Continuous (fderiv ℂ s) :=
  s.regular.continuous_fderiv (by norm_num)

def one : ThetaSection H Λ 0 where
  toFun _ := 1
  regular := contDiff_const
  translates _ _ := by simp

def mul (s : ThetaSection H Λ n) (t : ThetaSection H Λ m) : ThetaSection H Λ (n + m) where
  toFun z := s z * t z
  regular := s.regular.mul t.regular
  translates l z := by rw [s.translates, t.translates, pow_add]; ring

@[simp]
theorem mul_apply (s : ThetaSection H Λ n) (t : ThetaSection H Λ m) (z : V) :
    s.mul t z = s z * t z := rfl

def pow (s : ThetaSection H Λ n) (k : ℕ) : ThetaSection H Λ (n * k) where
  toFun z := s z ^ k
  regular := s.regular.pow k
  translates l z := by rw [s.translates, mul_pow, pow_mul]

@[simp]
theorem pow_apply (s : ThetaSection H Λ n) (k : ℕ) (z : V) : s.pow k z = s z ^ k := rfl

/-- One of the mixed cubic monomials, in the same degree as `s³`. -/
def squareMul (s t : ThetaSection H Λ n) : ThetaSection H Λ (n * 3) where
  toFun z := s z ^ 2 * t z
  regular := (s.regular.pow 2).mul t.regular
  translates l z := by
    rw [s.translates, t.translates]
    simp only [mul_pow, pow_mul]
    ring

@[simp]
theorem squareMul_apply (s t : ThetaSection H Λ n) (z : V) : s.squareMul t z = s z ^ 2 * t z := rfl

def add (s t : ThetaSection H Λ n) : ThetaSection H Λ n where
  toFun z := s z + t z
  regular := s.regular.add t.regular
  translates l z := by rw [s.translates, t.translates, mul_add]

def constMul (c : ℂ) (s : ThetaSection H Λ n) : ThetaSection H Λ n where
  toFun z := c * s z
  regular := contDiff_const.mul s.regular
  translates l z := by rw [s.translates]; ring

end ThetaSection

/-- Finite homogeneous coordinates with no common zero. Injectivity and
tangent separation are properties to prove, not fields of this structure. -/
structure FiniteSectionFamily (Λ : AddSubgroup V) where
  degree : ℕ
  sections : Finset (ThetaSection H Λ degree)
  nonzero : ∀ p : V, ∃ s ∈ sections, s p ≠ 0

namespace FiniteSectionFamily

variable {H} {Λ : AddSubgroup V}

def trivial : FiniteSectionFamily H Λ where
  degree := 0
  sections := {ThetaSection.one}
  nonzero _ := ⟨ThetaSection.one, Finset.mem_singleton_self _, one_ne_zero⟩

/-- Products of homogeneous coordinates combine two families into one. -/
noncomputable def mul (F G : FiniteSectionFamily H Λ) : FiniteSectionFamily H Λ := by
  classical
  exact
    { degree := F.degree + G.degree
      sections := (F.sections ×ˢ G.sections).image (fun st => st.1.mul st.2)
      nonzero := fun p => by
        obtain ⟨s, hs, hsp⟩ := F.nonzero p
        obtain ⟨t, ht, htp⟩ := G.nonzero p
        exact ⟨s.mul t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩,
          mul_ne_zero hsp htp⟩ }

theorem mul_mem (F G : FiniteSectionFamily H Λ) (s : ThetaSection H Λ F.degree)
    (hs : s ∈ F.sections) (t : ThetaSection H Λ G.degree) (ht : t ∈ G.sections) :
    s.mul t ∈ (F.mul G).sections := by
  classical
  exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩

def Separates (F : FiniteSectionFamily H Λ) (p q : V) : Prop :=
  ∃ s ∈ F.sections, ∃ t ∈ F.sections, s p * t q ≠ s q * t p

def Detects (F : FiniteSectionFamily H Λ) (p v : V) : Prop :=
  ∃ s ∈ F.sections, ∃ t ∈ F.sections, s p ≠ 0 ∧
    s p * fderiv ℂ t p v ≠ t p * fderiv ℂ s p v

end FiniteSectionFamily

section BackgroundFamilies

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]
  [CompactSpace (V ⧸ Λ)]

def tripleSection
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (ab : V × V) : ThetaSection H Λ (n * 3) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact
    { toFun := thetaTriple (powerHermitian H n) Λ ab.1 ab.2
      regular := thetaTriple_contDiff_one _ Λ (powerHermitian_positive H hpos n hn) ab.1 ab.2
      translates := fun l z => by
        rw [thetaTriple_translation _ Λ (powerHermitian_symm H hsym n)
          (powerHermitian_integral H Λ hint n), doubledAutomorphy_power, pow_mul] }

/-- Every positive degree has a cubed finite family without a common zero. -/
def cubicBackground
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) : FiniteSectionFamily H Λ := by
  classical
  let hex := exists_finite_thetaTriples (powerHermitian H n) Λ
    (powerHermitian_symm H hsym n) (powerHermitian_positive H hpos n hn)
    (powerHermitian_integral H Λ hint n)
  exact
    { degree := n * 3
      sections := hex.choose.image (tripleSection H Λ hsym hpos hint n hn)
      nonzero := fun p => by
        obtain ⟨ab, hab, hp⟩ := hex.choose_spec p
        exact ⟨tripleSection H Λ hsym hpos hint n hn ab, Finset.mem_image.mpr ⟨ab, hab, rfl⟩, hp⟩ }

end BackgroundFamilies

section Wronskians

def wronskian (s t : V → ℂ) (p v : V) : ℂ :=
  s p * fderiv ℂ t p v - t p * fderiv ℂ s p v

theorem wronskian_mul_right (s t g : V → ℂ) (p v : V)
    (hs : DifferentiableAt ℂ s p) (ht : DifferentiableAt ℂ t p) (hg : DifferentiableAt ℂ g p) :
    wronskian (s * g) (t * g) p v = g p ^ 2 * wronskian s t p v := by
  rw [wronskian, fderiv_mul ht hg, fderiv_mul hs hg]
  simp only [Pi.mul_apply, add_apply, smul_apply, smul_eq_mul, wronskian]
  ring

theorem wronskian_cubes (s t : V → ℂ) (p v : V)
    (hs : DifferentiableAt ℂ s p) (ht : DifferentiableAt ℂ t p) :
    wronskian (s ^ 3) (s ^ 2 * t) p v = s p ^ 4 * wronskian s t p v := by
  rw [wronskian, fderiv_mul (hs.pow 2) ht, fderiv_pow 2 hs, fderiv_pow 3 hs]
  simp only [Pi.mul_apply, Pi.pow_apply, add_apply, smul_apply, smul_eq_mul, wronskian]
  norm_num
  ring

end Wronskians

namespace FiniteSectionFamily

variable {H} {Λ : AddSubgroup V}

theorem detects_mul_left (F G : FiniteSectionFamily H Λ) (p v : V) (hF : F.Detects p v) :
    (F.mul G).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  refine ⟨s.mul g, mul_mem F G s hs g hg, t.mul g, mul_mem F G t ht g hg,
    mul_ne_zero hsp hgp, ?_⟩
  apply sub_ne_zero.mp
  change wronskian ((s : V → ℂ) * (g : V → ℂ)) ((t : V → ℂ) * (g : V → ℂ)) p v ≠ 0
  rw [wronskian_mul_right _ _ _ _ _ (s.differentiable p) (t.differentiable p) (g.differentiable p)]
  exact mul_ne_zero (pow_ne_zero 2 hgp) (sub_ne_zero.mpr hdet)

theorem separates_mul_left (F G : FiniteSectionFamily H Λ) (p q : V) (hF : F.Separates p q) :
    (F.mul G).Separates p q := by
  obtain ⟨s, hs, t, ht, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  by_cases hgq : g q = 0
  · obtain ⟨h, hh, hhq⟩ := G.nonzero q
    obtain ⟨a, ha, hap⟩ := F.nonzero p
    obtain ⟨b, hb, hbq⟩ := F.nonzero q
    refine ⟨a.mul g, mul_mem F G a ha g hg, b.mul h, mul_mem F G b hb h hh, ?_⟩
    simp only [ThetaSection.mul_apply, hgq, mul_zero, zero_mul]
    exact mul_ne_zero (mul_ne_zero hap hgp) (mul_ne_zero hbq hhq)
  · refine ⟨s.mul g, mul_mem F G s hs g hg, t.mul g, mul_mem F G t ht g hg, ?_⟩
    apply sub_ne_zero.mp
    have he : (s.mul g p * t.mul g q) - (s.mul g q * t.mul g p) =
        (g p * g q) * (s p * t q - s q * t p) := by simp only [ThetaSection.mul_apply]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hgp hgq) (sub_ne_zero.mpr hdet)

theorem isOpen_detects (F : FiniteSectionFamily H Λ) :
    IsOpen {pv : V × V | F.Detects pv.1 pv.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro pv hpv
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hpv
  have hcs : Continuous (fun pv : V × V => s pv.1) := s.continuous.comp continuous_fst
  have hct : Continuous (fun pv : V × V => t pv.1) := t.continuous.comp continuous_fst
  have hds : Continuous (fun pv : V × V => fderiv ℂ s pv.1 pv.2) :=
    (s.continuous_fderiv.comp continuous_fst).clm_apply continuous_snd
  have hdt : Continuous (fun pv : V × V => fderiv ℂ t pv.1 pv.2) :=
    (t.continuous_fderiv.comp continuous_fst).clm_apply continuous_snd
  filter_upwards [(isOpen_ne_fun hcs continuous_const).mem_nhds hsp,
    (isOpen_ne_fun (hcs.mul hdt) (hct.mul hds)).mem_nhds hdet] with x hx hxdet
  exact ⟨s, hs, t, ht, hx, hxdet⟩

theorem isOpen_separates (F : FiniteSectionFamily H Λ) :
    IsOpen {pq : V × V | F.Separates pq.1 pq.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro pq hpq
  obtain ⟨s, hs, t, ht, hdet⟩ := hpq
  have hc1 : Continuous (fun pq : V × V => s pq.1 * t pq.2) :=
    (s.continuous.comp continuous_fst).mul (t.continuous.comp continuous_snd)
  have hc2 : Continuous (fun pq : V × V => s pq.2 * t pq.1) :=
    (s.continuous.comp continuous_snd).mul (t.continuous.comp continuous_fst)
  filter_upwards [(isOpen_ne_fun hc1 hc2).mem_nhds hdet] with x hx
  exact ⟨s, hs, t, ht, hx⟩

end FiniteSectionFamily

section CubicFamilies

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]
  [CompactSpace (V ⧸ Λ)]

def cubicFamily
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (s t : ThetaSection H Λ n) : FiniteSectionFamily H Λ := by
  classical
  let F := cubicBackground H Λ hsym hpos hint n hn
  exact
    { degree := n * 3
      sections := {s.pow 3, t.pow 3, s.squareMul t, t.squareMul s} ∪ F.sections
      nonzero := fun p => by
        obtain ⟨u, hu, hup⟩ := F.nonzero p
        exact ⟨u, Finset.mem_union_right _ hu, hup⟩ }

open scoped Classical in
theorem cubicFamily_mem
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (s t : ThetaSection H Λ n) (u : ThetaSection H Λ (n * 3))
    (hu : u ∈ ({s.pow 3, t.pow 3, s.squareMul t, t.squareMul s} : Finset _)) :
    u ∈ (cubicFamily H Λ hsym hpos hint n hn s t).sections := by
  classical
  exact Finset.mem_union_left _ hu

theorem cubicFamily_separates
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (s t : ThetaSection H Λ n) (p q : V)
    (hdet : s p * t q ≠ s q * t p) :
    (cubicFamily H Λ hsym hpos hint n hn s t).Separates p q := by
  classical
  have hs := cubicFamily_mem H Λ hsym hpos hint n hn s t (s.pow 3) (by simp)
  have ht := cubicFamily_mem H Λ hsym hpos hint n hn s t (t.pow 3) (by simp)
  have hst := cubicFamily_mem H Λ hsym hpos hint n hn s t (s.squareMul t) (by simp)
  by_cases hsp : s p = 0
  · have hsq : s q ≠ 0 := by intro h; simp [hsp, h] at hdet
    have htp : t p ≠ 0 := by intro h; simp [hsp, h] at hdet
    refine ⟨s.pow 3, hs, t.pow 3, ht, ?_⟩
    simp only [ThetaSection.pow_apply, hsp, zero_pow (by omega : 3 ≠ 0), zero_mul]
    exact Ne.symm (mul_ne_zero (pow_ne_zero 3 hsq) (pow_ne_zero 3 htp))
  · by_cases hsq : s q = 0
    · have htq : t q ≠ 0 := by intro h; simp [hsq, h] at hdet
      refine ⟨s.pow 3, hs, t.pow 3, ht, ?_⟩
      simp only [ThetaSection.pow_apply, hsq, zero_pow (by omega : 3 ≠ 0), zero_mul]
      exact mul_ne_zero (pow_ne_zero 3 hsp) (pow_ne_zero 3 htq)
    · refine ⟨s.pow 3, hs, s.squareMul t, hst, ?_⟩
      apply sub_ne_zero.mp
      have he : s.pow 3 p * s.squareMul t q - s.pow 3 q * s.squareMul t p =
          (s p ^ 2 * s q ^ 2) * (s p * t q - s q * t p) := by
        simp only [ThetaSection.pow_apply, ThetaSection.squareMul_apply]
        ring
      rw [he]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsp) (pow_ne_zero 2 hsq)) (sub_ne_zero.mpr hdet)

theorem cubicFamily_detects
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (n : ℕ) (hn : 0 < n) (s t : ThetaSection H Λ n) (p v : V) (hsp : s p ≠ 0)
    (hdet : s p * fderiv ℂ t p v ≠ t p * fderiv ℂ s p v) :
    (cubicFamily H Λ hsym hpos hint n hn s t).Detects p v := by
  classical
  refine ⟨s.pow 3, cubicFamily_mem H Λ hsym hpos hint n hn s t _ (by simp),
    s.squareMul t, cubicFamily_mem H Λ hsym hpos hint n hn s t _ (by simp),
    pow_ne_zero 3 hsp, ?_⟩
  apply sub_ne_zero.mp
  change wronskian ((s : V → ℂ) ^ 3) ((s : V → ℂ) ^ 2 * (t : V → ℂ)) p v ≠ 0
  rw [wronskian_cubes _ _ _ _ (s.differentiable p) (t.differentiable p)]
  exact mul_ne_zero (pow_ne_zero 4 hsp) (sub_ne_zero.mpr hdet)

end CubicFamilies

namespace FiniteSectionFamily

variable {H} {Λ : AddSubgroup V}

theorem detects_mul_right (F G : FiniteSectionFamily H Λ) (p v : V) (hG : G.Detects p v) :
    (F.mul G).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hG
  obtain ⟨g, hg, hgp⟩ := F.nonzero p
  refine ⟨g.mul s, mul_mem F G g hg s hs, g.mul t, mul_mem F G g hg t ht,
    mul_ne_zero hgp hsp, ?_⟩
  apply sub_ne_zero.mp
  change wronskian ((g : V → ℂ) * (s : V → ℂ)) ((g : V → ℂ) * (t : V → ℂ)) p v ≠ 0
  rw [mul_comm (g : V → ℂ) (s : V → ℂ), mul_comm (g : V → ℂ) (t : V → ℂ),
    wronskian_mul_right _ _ _ _ _ (s.differentiable p) (t.differentiable p) (g.differentiable p)]
  exact mul_ne_zero (pow_ne_zero 2 hgp) (sub_ne_zero.mpr hdet)

theorem separates_mul_right (F G : FiniteSectionFamily H Λ) (p q : V) (hG : G.Separates p q) :
    (F.mul G).Separates p q := by
  obtain ⟨s, hs, t, ht, hdet⟩ := hG
  obtain ⟨g, hg, hgp⟩ := F.nonzero p
  by_cases hgq : g q = 0
  · obtain ⟨h, hh, hhq⟩ := F.nonzero q
    obtain ⟨a, ha, hap⟩ := G.nonzero p
    obtain ⟨b, hb, hbq⟩ := G.nonzero q
    refine ⟨g.mul a, mul_mem F G g hg a ha, h.mul b, mul_mem F G h hh b hb, ?_⟩
    simp only [ThetaSection.mul_apply, hgq, zero_mul]
    exact mul_ne_zero (mul_ne_zero hgp hap) (mul_ne_zero hhq hbq)
  · refine ⟨g.mul s, mul_mem F G g hg s hs, g.mul t, mul_mem F G g hg t ht, ?_⟩
    apply sub_ne_zero.mp
    have he : g.mul s p * g.mul t q - g.mul s q * g.mul t p =
        (g p * g q) * (s p * t q - s q * t p) := by simp only [ThetaSection.mul_apply]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hgp hgq) (sub_ne_zero.mpr hdet)

/-- Finitely many coordinate families can be combined while preserving every
point and tangent separation they already provide. -/
theorem exists_common_family (S : Finset (FiniteSectionFamily H Λ)) :
    ∃ F : FiniteSectionFamily H Λ,
      (∀ G ∈ S, ∀ p v : V, G.Detects p v → F.Detects p v) ∧
      (∀ G ∈ S, ∀ p q : V, G.Separates p q → F.Separates p q) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨trivial, by simp, by simp⟩
  | @insert G S hGS ih =>
    obtain ⟨F, hFd, hFs⟩ := ih
    refine ⟨G.mul F, ?_, ?_⟩
    · intro K hK p v hKd
      rcases Finset.mem_insert.mp hK with hEq | hKS
      · subst K
        exact FiniteSectionFamily.detects_mul_left G F p v hKd
      · exact detects_mul_right G F p v (hFd K hKS p v hKd)
    · intro K hK p q hKs
      rcases Finset.mem_insert.mp hK with hEq | hKS
      · subst K
        exact FiniteSectionFamily.separates_mul_left G F p q hKs
      · exact FiniteSectionFamily.separates_mul_right G F p q (hFs K hKS p q hKs)

theorem exists_detecting_on_compact (K : Set (V × V)) (hK : IsCompact K)
    (hcover : ∀ pv ∈ K, ∃ F : FiniteSectionFamily H Λ, F.Detects pv.1 pv.2) :
    ∃ F : FiniteSectionFamily H Λ, ∀ pv ∈ K, F.Detects pv.1 pv.2 := by
  classical
  have hcov : K ⊆ ⋃ F : FiniteSectionFamily H Λ, {pv | F.Detects pv.1 pv.2} := by
    intro pv hpv
    exact Set.mem_iUnion.mpr (hcover pv hpv)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun F : FiniteSectionFamily H Λ =>
    {pv | F.Detects pv.1 pv.2}) (fun F => F.isOpen_detects) hcov
  obtain ⟨F, hFd, _⟩ := exists_common_family S
  refine ⟨F, fun pv hpv => ?_⟩
  obtain ⟨G, hGS, hG⟩ := (show ∃ G ∈ S, G.Detects pv.1 pv.2 from by
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hS hpv)
  exact hFd G hGS pv.1 pv.2 hG

theorem exists_separating_on_compact (K : Set (V × V)) (hK : IsCompact K)
    (hcover : ∀ pq ∈ K, ∃ F : FiniteSectionFamily H Λ, F.Separates pq.1 pq.2) :
    ∃ F : FiniteSectionFamily H Λ, ∀ pq ∈ K, F.Separates pq.1 pq.2 := by
  classical
  have hcov : K ⊆ ⋃ F : FiniteSectionFamily H Λ, {pq | F.Separates pq.1 pq.2} := by
    intro pq hpq
    exact Set.mem_iUnion.mpr (hcover pq hpq)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun F : FiniteSectionFamily H Λ =>
    {pq | F.Separates pq.1 pq.2}) (fun F => F.isOpen_separates) hcov
  obtain ⟨F, _, hFs⟩ := exists_common_family S
  refine ⟨F, fun pq hpq => ?_⟩
  obtain ⟨G, hGS, hG⟩ := (show ∃ G ∈ S, G.Separates pq.1 pq.2 from by
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hS hpq)
  exact hFs G hGS pq.1 pq.2 hG

end FiniteSectionFamily

section FiniteSeparation

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]
  [CompactSpace (V ⧸ Λ)]

theorem exists_family_separating_points
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (p q : V) (hpq : q - p ∉ Λ) :
    ∃ F : FiniteSectionFamily H Λ, F.Separates p q := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨n, hn, hsep⟩ := (peakTheta_eventually_separates H Λ hsym hpos p q hpq).exists
  let s : ThetaSection H Λ n :=
    ⟨peakTheta H Λ n p, peakTheta_contDiff_one H Λ hpos n hn p,
      fun l z => peakTheta_translation H Λ hsym hint n hn p z l⟩
  let t : ThetaSection H Λ n :=
    ⟨peakTheta H Λ n q, peakTheta_contDiff_one H Λ hpos n hn q,
      fun l z => peakTheta_translation H Λ hsym hint n hn q z l⟩
  exact ⟨cubicFamily H Λ hsym hpos hint n hn s t,
    cubicFamily_separates H Λ hsym hpos hint n hn s t p q hsep⟩

theorem exists_family_detecting_tangent
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (p v : V) (hv : v ≠ 0) : ∃ F : FiniteSectionFamily H Λ, F.Detects p v := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨n, a, b, hn, ha, hb, hsp, hsep⟩ := exists_centeredTheta_separating_tangent H Λ hpos p v hv
  let s : ThetaSection H Λ n :=
    ⟨centeredTheta H Λ n a, centeredTheta_contDiff_one H Λ hpos n hn a,
      fun l z => centeredTheta_translation H hsym Λ hint n a z ha l⟩
  let t : ThetaSection H Λ n :=
    ⟨centeredTheta H Λ n b, centeredTheta_contDiff_one H Λ hpos n hn b,
      fun l z => centeredTheta_translation H hsym Λ hint n b z hb l⟩
  exact ⟨cubicFamily H Λ hsym hpos hint n hn s t,
    cubicFamily_detects H Λ hsym hpos hint n hn s t p v hsp hsep⟩

end FiniteSeparation

namespace ThetaSection

variable {H} {Λ : AddSubgroup V} {n : ℕ} [FiniteDimensional ℂ V]

theorem fderiv_translate (s : ThetaSection H Λ n) (l : Λ) (p v : V) :
    fderiv ℂ s (p + l) v = doubledAutomorphy H l p ^ n * fderiv ℂ s p v +
      s p * fderiv ℂ (fun z => doubledAutomorphy H l z ^ n) p v := by
  have he : (fun z : V => s (z + l)) =
      (fun z : V => doubledAutomorphy H l z ^ n) * (s : V → ℂ) := funext (s.translates l)
  have hd := congrArg (fun f : V → ℂ => fderiv ℂ f p v) he
  have ha : DifferentiableAt ℂ (fun z : V => doubledAutomorphy H l z ^ n) p :=
    ((doubledAutomorphy_differentiable H l).pow n) p
  rw [fderiv_comp_add_right, fderiv_mul ha (s.differentiable p)] at hd
  simpa only [add_apply, smul_apply, smul_eq_mul] using hd

theorem wronskian_translate (s t : ThetaSection H Λ n) (l : Λ) (p v : V) :
    wronskian s t (p + l) v = (doubledAutomorphy H l p ^ n) ^ 2 * wronskian s t p v := by
  rw [wronskian, s.translates, t.translates, s.fderiv_translate, t.fderiv_translate, wronskian]
  ring

end ThetaSection

namespace FiniteSectionFamily

variable {H} {Λ : AddSubgroup V}

theorem detects_of_smul (F : FiniteSectionFamily H Λ) (p v : V) (c : ℂ)
    (hF : F.Detects p (c • v)) : F.Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hF
  refine ⟨s, hs, t, ht, hsp, fun he => hdet ?_⟩
  simp only [map_smul, smul_eq_mul]
  linear_combination c * he

theorem detects_translate [FiniteDimensional ℂ V] (F : FiniteSectionFamily H Λ)
    (l : Λ) (p v : V) (hF : F.Detects p v) : F.Detects (p + l) v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hF
  refine ⟨s, hs, t, ht, ?_, ?_⟩
  · rw [s.translates]
    exact mul_ne_zero (pow_ne_zero _ (doubledAutomorphy_ne_zero H l p)) hsp
  · apply sub_ne_zero.mp
    change wronskian s t (p + l) v ≠ 0
    rw [ThetaSection.wronskian_translate]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (doubledAutomorphy_ne_zero H l p)))
      (sub_ne_zero.mpr hdet)

end FiniteSectionFamily

section FiniteImmersion

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]
  [CompactSpace (V ⧸ Λ)]

/-- One finite homogeneous-coordinate family detects every nonzero tangent
vector at every point, using compactness and lattice translation. -/
theorem exists_family_detecting_all_tangents
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∃ F : FiniteSectionFamily H Λ, ∀ (p v : V), v ≠ 0 → F.Detects p v := by
  let : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
  let K : Set (V × V) := Metric.closedBall (0 : V) (roundingBound Λ) ×ˢ Metric.sphere (0 : V) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  obtain ⟨F, hF⟩ := FiniteSectionFamily.exists_detecting_on_compact (H := H) (Λ := Λ) K hK (by
    intro pv hpv
    have hv : pv.2 ≠ 0 := by
      intro hv
      have h := hpv.2
      simp [hv] at h
    exact exists_family_detecting_tangent H Λ hsym hpos hint pv.1 pv.2 hv)
  refine ⟨F, fun p v hv => ?_⟩
  let l : Λ := roundToLattice Λ p
  let p₀ : V := p - l
  let v₀ : V := (‖v‖⁻¹ : ℂ) • v
  have hp₀ : p₀ ∈ Metric.closedBall (0 : V) (roundingBound Λ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using roundToLattice_norm_le Λ p
  have hv₀ : v₀ ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_smul_inv_norm hv
  have hdetect := hF (p₀, v₀) ⟨hp₀, hv₀⟩
  have hdetect' := F.detects_of_smul p₀ v (‖v‖⁻¹ : ℂ) hdetect
  have hshift := F.detects_translate l p₀ v hdetect'
  simpa only [p₀, sub_add_cancel] using hshift

end FiniteImmersion

namespace FiniteSectionFamily

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open Filter _root_.Topology

variable {H} {Λ : AddSubgroup V}

theorem sections_nonempty (F : FiniteSectionFamily H Λ) : F.sections.Nonempty := by
  obtain ⟨s, hs, _⟩ := F.nonzero 0
  exact ⟨s, hs⟩

def projectiveDimension (F : FiniteSectionFamily H Λ) : ℕ := F.sections.card - 1

noncomputable def indexEquiv (F : FiniteSectionFamily H Λ) :
    F.sections ≃ Fin (F.projectiveDimension + 1) := by
  classical
  apply Finset.equivFinOfCardEq
  have h := Finset.card_pos.mpr F.sections_nonempty
  dsimp [FiniteSectionFamily.projectiveDimension]
  omega

def coordinate (F : FiniteSectionFamily H Λ) (i : Fin (F.projectiveDimension + 1)) :
    ThetaSection H Λ F.degree := (F.indexEquiv.symm i).val

theorem coordinate_surjective (F : FiniteSectionFamily H Λ)
    (s : ThetaSection H Λ F.degree) (hs : s ∈ F.sections) : ∃ i, F.coordinate i = s := by
  refine ⟨F.indexEquiv ⟨s, hs⟩, ?_⟩
  simp [FiniteSectionFamily.coordinate]

def vector (F : FiniteSectionFamily H Λ) (p : V) : Fin (F.projectiveDimension + 1) → ℂ :=
  fun i => F.coordinate i p

theorem vector_ne_zero (F : FiniteSectionFamily H Λ) (p : V) : F.vector p ≠ 0 := by
  obtain ⟨s, hs, hsp⟩ := F.nonzero p
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  intro he
  have hz := congrFun he i
  change F.coordinate i p = 0 at hz
  rw [hi] at hz
  exact hsp hz

def projectiveLift (F : FiniteSectionFamily H Λ) (p : V) :
    Projectivization ℂ (Fin (F.projectiveDimension + 1) → ℂ) :=
  Projectivization.mk ℂ (F.vector p) (F.vector_ne_zero p)

def projectiveMap (F : FiniteSectionFamily H Λ) (q : V ⧸ Λ) :
    Projectivization ℂ (Fin (F.projectiveDimension + 1) → ℂ) :=
  F.projectiveLift (Quotient.out q)

theorem projectiveLift_translate (F : FiniteSectionFamily H Λ) (l : Λ) (p : V) :
    F.projectiveLift (p + l) = F.projectiveLift p := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨doubledAutomorphy H l p ^ F.degree, ?_⟩
  funext i
  exact ((F.coordinate i).translates l p).symm

theorem projectiveMap_lift (F : FiniteSectionFamily H Λ) (p : V) :
    F.projectiveMap (QuotientAddGroup.mk p) = F.projectiveLift p := by
  have hq : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk p : V ⧸ Λ)) : V ⧸ Λ) =
      QuotientAddGroup.mk p := Quotient.out_eq _
  have hl : Quotient.out (QuotientAddGroup.mk p : V ⧸ Λ) - p ∈ Λ :=
    QuotientAddGroup.eq_iff_sub_mem.mp hq
  let l : Λ := ⟨Quotient.out (QuotientAddGroup.mk p : V ⧸ Λ) - p, hl⟩
  have he : p + (l : V) = Quotient.out (QuotientAddGroup.mk p : V ⧸ Λ) := by dsimp [l]; abel
  simpa only [he, FiniteSectionFamily.projectiveMap] using F.projectiveLift_translate l p

theorem projectiveMap_continuous (F : FiniteSectionFamily H Λ) : Continuous F.projectiveMap := by
  apply (QuotientAddGroup.isQuotientMap_mk Λ).continuous_iff.mpr
  have hc : Continuous F.vector := continuous_pi (fun i => (F.coordinate i).continuous)
  have h := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (Fin (F.projectiveDimension + 1) → ℂ)).comp
    (hc.subtype_mk F.vector_ne_zero)
  convert! h using 1
  funext p
  exact F.projectiveMap_lift p

theorem projectiveMap_inPatch (F : FiniteSectionFamily H Λ)
    (i : Fin (F.projectiveDimension + 1)) (p : V) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (F.projectiveMap (QuotientAddGroup.mk p)) ↔ F.coordinate i p ≠ 0 := by
  rw [F.projectiveMap_lift]
  exact AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i _ _

def chart (F : FiniteSectionFamily H Λ) (i : Fin (F.projectiveDimension + 1)) (p : V) :
    Fin (F.projectiveDimension + 1) → ℂ := fun j => F.coordinate j p / F.coordinate i p

theorem projectiveMap_coordinates (F : FiniteSectionFamily H Λ)
    (i : Fin (F.projectiveDimension + 1)) (p : V) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (F.projectiveMap (QuotientAddGroup.mk p)) = F.chart i p := by
  rw [F.projectiveMap_lift]
  rfl

theorem chart_contDiffAt (F : FiniteSectionFamily H Λ)
    (i : Fin (F.projectiveDimension + 1)) (p : V) (hi : F.coordinate i p ≠ 0) :
    ContDiffAt ℂ 1 (F.chart i) p := by
  apply contDiffAt_pi.mpr
  intro j
  exact (F.coordinate j).regular.contDiffAt.div (F.coordinate i).regular.contDiffAt hi

theorem ratio_derivative_zero {n : ℕ} (s t : ThetaSection H Λ n) (p v : V) (hs : s p ≠ 0)
    (hD : fderiv ℂ (fun z => t z / s z) p v = 0) :
    s p * fderiv ℂ t p v = t p * fderiv ℂ s p v := by
  have he : ((fun z => t z / s z) * (s : V → ℂ)) =ᶠ[nhds p] (t : V → ℂ) := by
    filter_upwards [s.continuous.continuousAt.eventually_ne hs] with z hz
    exact div_mul_cancel₀ _ hz
  have hds : DifferentiableAt ℂ (fun z => t z / s z) p :=
    (t.regular.contDiffAt.div s.regular.contDiffAt hs).differentiableAt (by norm_num)
  have he' := congrArg (fun L : V →L[ℂ] ℂ => L v) he.fderiv_eq
  rw [fderiv_mul hds (s.differentiable p)] at he'
  simp only [add_apply, smul_apply, smul_eq_mul, hD, mul_zero, add_zero] at he'
  rw [← he']
  field_simp [hs]

theorem chart_fderiv_component (F : FiniteSectionFamily H Λ)
    (i j : Fin (F.projectiveDimension + 1)) (p v : V) (hi : F.coordinate i p ≠ 0) :
    fderiv ℂ (fun z => F.coordinate j z / F.coordinate i z) p v =
      (fderiv ℂ (F.chart i) p v) j := by
  have hd : DifferentiableAt ℂ (F.chart i) p := (F.chart_contDiffAt i p hi).differentiableAt (by norm_num)
  have he := fderiv_apply hd j
  exact congrArg (fun L : V →L[ℂ] ℂ => L v) he

theorem chart_fderiv_injective (F : FiniteSectionFamily H Λ) (p : V)
    (hF : ∀ v : V, v ≠ 0 → F.Detects p v)
    (i : Fin (F.projectiveDimension + 1)) (hi : F.coordinate i p ≠ 0) :
    Function.Injective (fderiv ℂ (F.chart i) p) := by
  have hker (v : V) (hv : fderiv ℂ (F.chart i) p v = 0) : v = 0 := by
    by_contra hv0
    obtain ⟨s, hs, t, ht, _, hdet⟩ := hF v hv0
    obtain ⟨j, hj⟩ := F.coordinate_surjective s hs
    obtain ⟨k, hk⟩ := F.coordinate_surjective t ht
    have hzero (a : Fin (F.projectiveDimension + 1)) :
        fderiv ℂ (fun z => F.coordinate a z / F.coordinate i z) p v = 0 := by
      rw [F.chart_fderiv_component i a p v hi, hv]
      rfl
    have hsj := ratio_derivative_zero (F.coordinate i) (F.coordinate j) p v hi (hzero j)
    have htk := ratio_derivative_zero (F.coordinate i) (F.coordinate k) p v hi (hzero k)
    rw [hj] at hsj
    rw [hk] at htk
    have he : F.coordinate i p * (s p * fderiv ℂ t p v - t p * fderiv ℂ s p v) = 0 := by
      linear_combination (s p) * htk - (t p) * hsj
    exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi))
  intro u v huv
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, huv, sub_self]

theorem projectiveMap_eq_of_not_separates (F : FiniteSectionFamily H Λ) (p q : V) :
    F.projectiveMap (QuotientAddGroup.mk p) = F.projectiveMap (QuotientAddGroup.mk q) ↔
      ¬F.Separates p q := by
  rw [F.projectiveMap_lift, F.projectiveMap_lift]
  rw [FiniteSectionFamily.projectiveLift, FiniteSectionFamily.projectiveLift, AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus.projectivization_mk_eq_iff_minors_eq]
  constructor
  · intro h hsep
    obtain ⟨s, hs, t, ht, hdet⟩ := hsep
    obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
    obtain ⟨j, hj⟩ := F.coordinate_surjective t ht
    have he := h i j
    change F.coordinate i p * F.coordinate j q = F.coordinate j p * F.coordinate i q at he
    rw [hi, hj] at he
    exact hdet (by simpa only [mul_comm] using he)
  · intro h i j
    by_contra he
    apply h
    refine ⟨F.coordinate i, (F.indexEquiv.symm i).property,
      F.coordinate j, (F.indexEquiv.symm j).property, ?_⟩
    change F.coordinate i p * F.coordinate j q ≠ F.coordinate j p * F.coordinate i q at he
    simpa only [mul_comm] using he

end FiniteSectionFamily

section LocalInjectivity

variable [FiniteDimensional ℂ V]

theorem locally_injective_of_injective_fderiv {N : ℕ} (f : V → Fin N → ℂ) (p : V)
    (hc : ContDiffAt ℂ 1 f p) (hi : Function.Injective (fderiv ℂ f p)) :
    ∃ U : Set V, IsOpen U ∧ p ∈ U ∧ Set.InjOn f U := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let L : V →L[ℂ] (Fin N → ℂ) := fderiv ℂ f p
  obtain ⟨g, hg⟩ := L.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let G : (Fin N → ℂ) →L[ℂ] V := g.toContinuousLinearMap
  have hGL : G.comp L = ContinuousLinearMap.id ℂ V := by
    ext v
    exact congrArg (fun m : V →ₗ[ℂ] V => m v) hg
  have hs := G.hasStrictFDerivAt.comp p (hc.hasStrictFDerivAt (by norm_num))
  change HasStrictFDerivAt (G ∘ f) (G.comp L) p at hs
  rw [hGL] at hs
  change HasStrictFDerivAt (G ∘ f) (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) p at hs
  let e := hs.toOpenPartialHomeomorph (G ∘ f)
  refine ⟨e.source, e.open_source, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro x hx y hy hxy
  apply e.injOn hx hy
  change G (f x) = G (f y)
  rw [hxy]

end LocalInjectivity

namespace FiniteSectionFamily

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {H} {Λ : AddSubgroup V} [FiniteDimensional ℂ V]

theorem projectiveMap_locally_injective (F : FiniteSectionFamily H Λ)
    (hF : ∀ p v : V, v ≠ 0 → F.Detects p v) (q : V ⧸ Λ) :
    ∃ U : Set (V ⧸ Λ), IsOpen U ∧ q ∈ U ∧ Set.InjOn F.projectiveMap U := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨s, hs, hsp⟩ := F.nonzero p
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  have hip : F.coordinate i p ≠ 0 := by rwa [hi]
  obtain ⟨W, hWo, hpW, hWi⟩ := locally_injective_of_injective_fderiv (F.chart i) p
    (F.chart_contDiffAt i p hip) (F.chart_fderiv_injective p (hF p) i hip)
  refine ⟨QuotientAddGroup.mk '' W, QuotientAddGroup.isOpenMap_coe _ hWo,
    ⟨p, hpW, rfl⟩, ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hchart : F.chart i a = F.chart i b := by
    rw [← F.projectiveMap_coordinates i a, ← F.projectiveMap_coordinates i b, hxy]
  exact congrArg QuotientAddGroup.mk (hWi ha hb hchart)

end FiniteSectionFamily

section GlobalEmbedding

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [DiscreteTopology Λ]
  [CompactSpace (V ⧸ Λ)]

/-- Compactness combines local injectivity and pair separation into a single
injective projective map whose affine differentials remain injective. -/
theorem exists_injective_immersive_family
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∃ F : FiniteSectionFamily H Λ, Function.Injective F.projectiveMap ∧
      ∀ p v : V, v ≠ 0 → F.Detects p v := by
  classical
  obtain ⟨F₀, hF₀⟩ := exists_family_detecting_all_tangents H Λ hsym hpos hint
  choose U hUo hUmem hUi using F₀.projectiveMap_locally_injective hF₀
  let W : Set ((V ⧸ Λ) × (V ⧸ Λ)) := ⋃ q : V ⧸ Λ, U q ×ˢ U q
  have hWo : IsOpen W := isOpen_iUnion (fun q => (hUo q).prod (hUo q))
  have hK : IsCompact Wᶜ := hWo.isClosed_compl.isCompact
  have hne (pq : (V ⧸ Λ) × (V ⧸ Λ)) (hpq : pq ∈ Wᶜ) : pq.1 ≠ pq.2 := by
    intro he
    apply hpq
    exact Set.mem_iUnion.mpr ⟨pq.1, hUmem pq.1, he ▸ hUmem pq.1⟩
  let A (G : FiniteSectionFamily H Λ) : Set ((V ⧸ Λ) × (V ⧸ Λ)) :=
    {pq | G.projectiveMap pq.1 ≠ G.projectiveMap pq.2}
  have hAo (G : FiniteSectionFamily H Λ) : IsOpen (A G) :=
    isOpen_ne_fun (G.projectiveMap_continuous.comp continuous_fst)
      (G.projectiveMap_continuous.comp continuous_snd)
  have hcover : Wᶜ ⊆ ⋃ G : FiniteSectionFamily H Λ, A G := by
    intro pq hpq
    obtain ⟨p, hp⟩ := QuotientAddGroup.mk_surjective pq.1
    obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective pq.2
    have hd : q - p ∉ Λ := by
      intro hd
      have he : (QuotientAddGroup.mk q : V ⧸ Λ) = QuotientAddGroup.mk p :=
        QuotientAddGroup.eq_iff_sub_mem.mpr hd
      rw [hp, hq] at he
      exact hne pq hpq he.symm
    obtain ⟨G, hG⟩ := exists_family_separating_points H Λ hsym hpos hint p q hd
    apply Set.mem_iUnion.mpr
    refine ⟨G, ?_⟩
    change G.projectiveMap pq.1 ≠ G.projectiveMap pq.2
    rw [← hp, ← hq]
    exact fun he => (G.projectiveMap_eq_of_not_separates p q).mp he hG
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover A hAo hcover
  obtain ⟨G, _, hGs⟩ := FiniteSectionFamily.exists_common_family S
  refine ⟨F₀.mul G, ?_, fun p v hv => F₀.detects_mul_left G p v (hF₀ p v hv)⟩
  intro x y hxy
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hFxy : F₀.projectiveMap (QuotientAddGroup.mk p) = F₀.projectiveMap (QuotientAddGroup.mk q) := by
    apply (F₀.projectiveMap_eq_of_not_separates p q).mpr
    intro hsep
    exact ((F₀.mul G).projectiveMap_eq_of_not_separates p q).mp hxy
      (F₀.separates_mul_left G p q hsep)
  by_cases hpq : (QuotientAddGroup.mk p, QuotientAddGroup.mk q) ∈ W
  · obtain ⟨a, hpa, hqa⟩ := Set.mem_iUnion.mp hpq
    exact hUi a hpa hqa hFxy
  · have hs := hS hpq
    obtain ⟨E, hES, hE⟩ := (show ∃ E ∈ S,
        E.projectiveMap (QuotientAddGroup.mk p) ≠ E.projectiveMap (QuotientAddGroup.mk q) from by
      simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, A] using hs)
    have hsep : E.Separates p q := by
      by_contra hnot
      exact hE ((E.projectiveMap_eq_of_not_separates p q).mpr hnot)
    exact False.elim (((F₀.mul G).projectiveMap_eq_of_not_separates p q).mp hxy
      (F₀.separates_mul_right G p q (hGs E hES p q hsep)))

/-- Positive integral Hermitian data give a closed holomorphic embedding with
injective coordinate differentials, exactly as required on the left of RiemannProjectivity. -/
theorem projective_embedding_of_positive_integral_hermitian
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∃ (n : ℕ) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧ ∀ p : V, ∃ i : Fin (n + 1),
        AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk p)) ∧
        DifferentiableAt ℂ (fun z : V =>
          AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk z))) p ∧
        Function.Injective (fderiv ℂ (fun z : V =>
          AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk z))) p) := by
  obtain ⟨F, hFi, hFd⟩ := exists_injective_immersive_family H Λ hsym hpos hint
  refine ⟨F.projectiveDimension, F.projectiveMap, F.projectiveMap_continuous.isClosedEmbedding hFi,
    fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := F.nonzero p
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  have hip : F.coordinate i p ≠ 0 := by rwa [hi]
  refine ⟨i, (F.projectiveMap_inPatch i p).mpr hip, ?_, ?_⟩
  · simp_rw [F.projectiveMap_coordinates]
    exact (F.chart_contDiffAt i p hip).differentiableAt (by norm_num)
  · simp_rw [F.projectiveMap_coordinates]
    exact F.chart_fderiv_injective p (hFd p) i hip

end GlobalEmbedding

section FubiniStudyAlgebra

variable {ι : Type*} [Fintype ι]

/-- The standard Hermitian Gram form of finitely many complex linear functionals. -/
def gramForm (A : V →ₗ[ℂ] (ι → ℂ)) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v => ∑ i, star (A u i) * A v i
      map_add' := by intro v w; simp [map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a v; simp [map_smul, Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro u v
    ext w
    simp [map_add, star_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a u
    ext v
    simp [map_smul, star_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem gramForm_apply (A : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    gramForm A u v = ∑ i, star (A u i) * A v i := rfl

theorem gramForm_symm (A : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    gramForm A v u = star (gramForm A u v) := by
  simp only [gramForm_apply, star_sum, star_mul, star_star, mul_comm]

def coordinateNormSq (w : ι → ℂ) : ℝ := ∑ i, Complex.normSq (w i)

theorem gramForm_self_re (A : V →ₗ[ℂ] (ι → ℂ)) (u : V) :
    (gramForm A u u).re = coordinateNormSq (A u) := by
  rw [gramForm_apply, Complex.re_sum, coordinateNormSq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem coordinateNormSq_pos (w : ι → ℂ) (hw : w ≠ 0) : 0 < coordinateNormSq w := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hw (funext h)
  obtain ⟨i, hi⟩ := hex
  exact (Finset.sum_pos_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w j))).mpr
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

theorem gramForm_self_pos (A : V →ₗ[ℂ] (ι → ℂ)) (u : V) (hu : A u ≠ 0) :
    0 < (gramForm A u u).re := by
  rw [gramForm_self_re]
  exact coordinateNormSq_pos (A u) hu

/-- Exterior products remove the vertical direction of homogeneous coordinates. -/
def horizontalDifferential (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) : V →ₗ[ℂ] (ι × ι → ℂ) where
  toFun u ij := w ij.1 * D u ij.2 - w ij.2 * D u ij.1
  map_add' := by intro u v; ext ij; simp [map_add]; ring
  map_smul' := by intro a u; ext ij; simp [map_smul]; ring

omit [Fintype ι] in
theorem horizontalDifferential_apply (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) (u : V) (i j : ι) :
    horizontalDifferential w D u (i, j) = w i * D u j - w j * D u i := rfl

/-- The Fubini--Study Hermitian form normalized so its imaginary part has
unit integral on a projective line. This is an algebraic pointwise definition. -/
def fubiniStudyForm (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  ((1 / (2 * Real.pi * coordinateNormSq w ^ 2) : ℝ) : ℂ) • gramForm (horizontalDifferential w D)

theorem fubiniStudyForm_apply (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    fubiniStudyForm w D u v =
      ((1 / (2 * Real.pi * coordinateNormSq w ^ 2) : ℝ) : ℂ) *
        gramForm (horizontalDifferential w D) u v := rfl

theorem fubiniStudyForm_symm (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    fubiniStudyForm w D v u = star (fubiniStudyForm w D u v) := by
  simp only [fubiniStudyForm_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [gramForm_symm (horizontalDifferential w D) u v]
  exact mul_comm _ _

theorem fubiniStudyForm_positive (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ))
    (hD : Function.Injective D) (i : ι) (hwi : w i ≠ 0) (hDi : ∀ u : V, D u i = 0)
    (u : V) (hu : u ≠ 0) : 0 < (fubiniStudyForm w D u u).re := by
  have hw : w ≠ 0 := by intro hw; exact hwi (congrFun hw i)
  have hDu : D u ≠ 0 := by
    intro h
    exact hu (hD (by simpa using h))
  have hex : ∃ j, D u j ≠ 0 := by
    by_contra! h
    exact hDu (funext h)
  obtain ⟨j, hj⟩ := hex
  have hhor : horizontalDifferential w D u ≠ 0 := by
    intro h
    have h' := congrFun h (i, j)
    change w i * D u j - w j * D u i = 0 at h'
    rw [hDi, mul_zero, sub_zero] at h'
    exact mul_ne_zero hwi hj h'
  have hc : 0 < 1 / (2 * Real.pi * coordinateNormSq w ^ 2) := by
    have hn := coordinateNormSq_pos w hw
    positivity
  rw [fubiniStudyForm_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos hc (gramForm_self_pos (horizontalDifferential w D) u hhor)

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem coordinateNormSq_smul (a : ℂ) (w : ι → ℂ) :
    coordinateNormSq (a • w) = Complex.normSq a * coordinateNormSq w := by
  simp only [coordinateNormSq, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]

theorem gramForm_smul_apply (a : ℂ) (A : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    gramForm (a • A) u v = (Complex.normSq a : ℂ) * gramForm A u v := by
  simp only [gramForm_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have ha : star a * a = (Complex.normSq a : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  calc
    _ = (star a * a) * (star (A u i) * A v i) := by ring
    _ = _ := by rw [ha]

omit [Fintype ι] in
theorem horizontalDifferential_gauge (a : ℂ) (w : ι → ℂ)
    (D : V →ₗ[ℂ] (ι → ℂ)) (b : V →ₗ[ℂ] ℂ) :
    horizontalDifferential (a • w) (a • D + b.smulRight w) =
      (a ^ 2) • horizontalDifferential w D := by
  ext u ij
  simp only [horizontalDifferential, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplying a local lift by a nonzero scalar function leaves the pulled-back
Hermitian form unchanged, including the vertical term in its derivative. -/
theorem fubiniStudyForm_gauge (a : ℂ) (ha : a ≠ 0) (w : ι → ℂ) (hw : w ≠ 0)
    (D : V →ₗ[ℂ] (ι → ℂ)) (b : V →ₗ[ℂ] ℂ) :
    fubiniStudyForm (a • w) (a • D + b.smulRight w) = fubiniStudyForm w D := by
  have hna : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  have hnw : coordinateNormSq w ≠ 0 := (coordinateNormSq_pos w hw).ne'
  have he : (1 / (2 * Real.pi * (Complex.normSq a * coordinateNormSq w) ^ 2)) *
      Complex.normSq a ^ 2 = 1 / (2 * Real.pi * coordinateNormSq w ^ 2) := by
    field_simp [hna, hnw, Real.pi_ne_zero]
  ext u v
  rw [fubiniStudyForm_apply, horizontalDifferential_gauge, gramForm_smul_apply,
    coordinateNormSq_smul, map_pow, ← mul_assoc, ← Complex.ofReal_mul, he, fubiniStudyForm_apply]

end FubiniStudyAlgebra

section BerryAlgebra
variable {ι : Type*} [Fintype ι]

def coordinatePairing (a b : ι → ℂ) : ℂ := ∑ i, star (a i) * b i

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem coordinatePairing_self (w : ι → ℂ) :
    coordinatePairing w w = (coordinateNormSq w : ℂ) := by
  simp only [coordinatePairing, coordinateNormSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.star_def, Complex.mul_conj]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem coordinatePairing_symm (a b : ι → ℂ) :
    coordinatePairing b a = star (coordinatePairing a b) := by
  simp only [coordinatePairing, star_sum, star_mul, star_star, mul_comm]

theorem gram_horizontalDifferential (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) (u v : V) :
    gramForm (horizontalDifferential w D) u v =
      2 * ((coordinateNormSq w : ℂ) * coordinatePairing (D u) (D v) -
        coordinatePairing (D u) w * coordinatePairing w (D v)) := by
  rw [gramForm_apply, ← coordinatePairing_self]
  simp only [Fintype.sum_prod_type, horizontalDifferential_apply, star_sub, star_mul,
    coordinatePairing, Finset.sum_mul, Finset.mul_sum]
  have hterm (i j : ι) :
      (star (D u j) * star (w i) - star (D u i) * star (w j)) *
        (w i * D v j - w j * D v i) =
      (star (w i) * w i) * (star (D u j) * D v j) +
      (star (w j) * w j) * (star (D u i) * D v i) -
      (star (D u j) * w j) * (star (w i) * D v i) -
      (star (D u i) * w i) * (star (w j) * D v j) := by ring
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (star (w j) * w j) * (star (D u i) * D v i)),
    Finset.sum_comm (f := fun i j => (star (D u j) * w j) * (star (w i) * D v i))]
  ring

/-- The real connection one-form of the unit tautological lift, in the same
normalization as `fubiniStudyForm`. -/
def berryConnection (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ)) (u : V) : ℝ :=
  (coordinatePairing w (D u)).im / (2 * Real.pi * coordinateNormSq w)

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem coordinatePairing_gauge (a b : ℂ) (w d : ι → ℂ) :
    coordinatePairing (a • w) (a • d + b • w) =
      (Complex.normSq a : ℂ) * coordinatePairing w d +
        star a * b * (coordinateNormSq w : ℂ) := by
  rw [← coordinatePairing_self]
  simp only [coordinatePairing, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    star_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have ha : star a * a = (Complex.normSq a : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]
    calc
      _ = (star a * a) * (star (w i) * d i) := by ring
      _ = _ := by rw [ha]
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem berryConnection_gauge (a : ℂ) (ha : a ≠ 0) (w : ι → ℂ) (hw : w ≠ 0)
    (D : V →ₗ[ℂ] (ι → ℂ)) (b : V →ₗ[ℂ] ℂ) (u : V) :
    berryConnection (a • w) (a • D + b.smulRight w) u =
      berryConnection w D u + (b u / a).im / (2 * Real.pi) := by
  have hna : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  have hnw : coordinateNormSq w ≠ 0 := (coordinateNormSq_pos w hw).ne'
  have hdiv : star a * b u = (Complex.normSq a : ℂ) * (b u / a) := by
    have hc : star a * a = (Complex.normSq a : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]
    rw [← hc]
    field_simp
  simp only [berryConnection, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]
  rw [coordinatePairing_gauge, coordinateNormSq_smul, hdiv]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, mul_zero, zero_add]
  field_simp

def berryDerivativeCandidate (w : ι → ℂ) (D : V →ₗ[ℂ] (ι → ℂ))
    (B : V → V → ι → ℂ) (u v : V) : ℝ :=
  (((coordinatePairing (D u) (D v) + coordinatePairing w (B u v)).im * coordinateNormSq w) -
    (coordinatePairing w (D v)).im * (2 * (coordinatePairing w (D u)).re)) /
      (2 * Real.pi * coordinateNormSq w ^ 2)

/-- The symmetric second derivative cancels from the curvature of the connection. -/
theorem berry_curvature_algebra (w : ι → ℂ) (hw : w ≠ 0) (D : V →ₗ[ℂ] (ι → ℂ))
    (B : V → V → ι → ℂ) (u v : V) (hB : B v u = B u v) :
    berryDerivativeCandidate w D B u v - berryDerivativeCandidate w D B v u =
      (fubiniStudyForm w D u v).im := by
  have hnw : coordinateNormSq w ≠ 0 := (coordinateNormSq_pos w hw).ne'
  rw [fubiniStudyForm_apply, gram_horizontalDifferential]
  simp only [berryDerivativeCandidate, hB]
  rw [coordinatePairing_symm (D u) (D v), coordinatePairing_symm w (D u)]
  have h2r : (2 : ℂ).re = 2 := rfl
  have h2i : (2 : ℂ).im = 0 := rfl
  simp only [Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    h2r, h2i]
  field_simp
  ring

end BerryAlgebra

section BerryCalculus
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem hasDerivAt_coordinatePairing {w d : ℝ → ι → ℂ} {w' d' : ι → ℂ} {t : ℝ}
    (hw : HasDerivAt w w' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun r => coordinatePairing (w r) (d r))
      (coordinatePairing w' (d t) + coordinatePairing (w t) d') t := by
  have hwi (i : ι) : HasDerivAt (fun r => w r i) (w' i) t :=
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t hw
  have hdi (i : ι) : HasDerivAt (fun r => d r i) (d' i) t :=
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t hd
  simpa only [coordinatePairing, Finset.sum_add_distrib, Pi.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hwi i).star.mul (hdi i)))

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem hasDerivAt_coordinateNormSq {w : ℝ → ι → ℂ} {w' : ι → ℂ} {t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun r => coordinateNormSq (w r)) (2 * (coordinatePairing (w t) w').re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_coordinatePairing hw hw)
  have he : (coordinatePairing w' (w t) + coordinatePairing (w t) w').re =
      2 * (coordinatePairing (w t) w').re := by
    rw [coordinatePairing_symm (w t) w']
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
    ring
  simpa only [Function.comp_def, Complex.reCLM_apply, coordinatePairing_self, Complex.ofReal_re, he] using h

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem hasDerivAt_berry_path {w d : ℝ → ι → ℂ} {w' d' : ι → ℂ} {t : ℝ}
    (hw : HasDerivAt w w' t) (hd : HasDerivAt d d' t) (hwt : w t ≠ 0) :
    HasDerivAt (fun r => (coordinatePairing (w r) (d r)).im /
      (2 * Real.pi * coordinateNormSq (w r)))
      (((coordinatePairing w' (d t) + coordinatePairing (w t) d').im * coordinateNormSq (w t) -
        (coordinatePairing (w t) (d t)).im * (2 * (coordinatePairing (w t) w').re)) /
        (2 * Real.pi * coordinateNormSq (w t) ^ 2)) t := by
  have hnw : coordinateNormSq (w t) ≠ 0 := (coordinateNormSq_pos (w t) hwt).ne'
  have hnum : HasDerivAt (fun r => (coordinatePairing (w r) (d r)).im)
      (coordinatePairing w' (d t) + coordinatePairing (w t) d').im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_coordinatePairing hw hd)
  have hden := (hasDerivAt_coordinateNormSq hw).const_mul (2 * Real.pi)
  convert! hnum.div hden (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnw) using 1
  field_simp

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

theorem berryConnection_hasDerivAt_line {f : V → ι → ℂ} {z : V}
    (hf : ContDiffAt ℂ 2 f z) (hz : f z ≠ 0) (u v : V) :
    HasDerivAt (fun t : ℝ => berryConnection (f (z + t • u))
      (fderiv ℂ f (z + t • u)).toLinearMap v)
      (berryDerivativeCandidate (f z) (fderiv ℂ f z).toLinearMap
        (fun a b => fderiv ℂ (fderiv ℂ f) z a b) u v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z)
  have hfirst := ((hf.differentiableAt (by norm_num)).hasFDerivAt.restrictScalars ℝ)
  have hw : HasDerivAt (fun t : ℝ => f (z + t • u)) (fderiv ℂ f z u) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using
      hfirst.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hsecond := (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.restrictScalars ℝ)
  have hD : HasDerivAt (fun t : ℝ => fderiv ℂ f (z + t • u))
      (fderiv ℂ (fderiv ℂ f) z u) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using
      hsecond.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hd : HasDerivAt (fun t : ℝ => fderiv ℂ f (z + t • u) v)
      (fderiv ℂ (fderiv ℂ f) z u v) 0 := by
    exact ((ContinuousLinearMap.apply ℂ (ι → ℂ) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hD
  simpa only [zero_smul, add_zero, berryConnection, berryDerivativeCandidate,
    ContinuousLinearMap.coe_coe] using
    hasDerivAt_berry_path hw hd (by simpa only [zero_smul, add_zero] using hz)

theorem berryConnection_curvature {f : V → ι → ℂ} {z : V}
    (hf : ContDiffAt ℂ 2 f z) (hz : f z ≠ 0) (u v : V) :
    deriv (fun t : ℝ => berryConnection (f (z + t • u))
      (fderiv ℂ f (z + t • u)).toLinearMap v) 0 -
    deriv (fun t : ℝ => berryConnection (f (z + t • v))
      (fderiv ℂ f (z + t • v)).toLinearMap u) 0 =
      (fubiniStudyForm (f z) (fderiv ℂ f z).toLinearMap u v).im := by
  rw [(berryConnection_hasDerivAt_line hf hz u v).deriv,
    (berryConnection_hasDerivAt_line hf hz v u).deriv]
  exact berry_curvature_algebra _ hz _ _ u v
    ((hf.isSymmSndFDerivAt (by norm_num)).eq v u)

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem coordinatePairing_continuousAt {X : Type*} [TopologicalSpace X]
    {w d : X → ι → ℂ} {x : X} (hw : ContinuousAt w x) (hd : ContinuousAt d x) :
    ContinuousAt (fun y => coordinatePairing (w y) (d y)) x :=
  tendsto_finsetSum _ (fun i _ => ((continuousAt_pi.mp hw) i).star.mul ((continuousAt_pi.mp hd) i))

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem coordinateNormSq_continuousAt {X : Type*} [TopologicalSpace X]
    {w : X → ι → ℂ} {x : X} (hw : ContinuousAt w x) :
    ContinuousAt (fun y => coordinateNormSq (w y)) x :=
  tendsto_finsetSum _ (fun i _ => Complex.continuous_normSq.continuousAt.comp ((continuousAt_pi.mp hw) i))

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem berryConnection_continuousAt {f : V → ι → ℂ} {z : V}
    (hf : ContDiffAt ℂ 1 f z) (hz : f z ≠ 0) (u : V) :
    ContinuousAt (fun y => berryConnection (f y) (fderiv ℂ f y).toLinearMap u) z := by
  have hD : ContinuousAt (fun y => fderiv ℂ f y u) z :=
    (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hn := coordinateNormSq_continuousAt hf.continuousAt
  have hnz : coordinateNormSq (f z) ≠ 0 := (coordinateNormSq_pos (f z) hz).ne'
  exact (Complex.continuous_im.continuousAt.comp
    (coordinatePairing_continuousAt hf.continuousAt hD)).div (continuousAt_const.mul hn)
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnz)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem berryDerivativeCandidate_continuousAt {f : V → ι → ℂ} {z : V}
    (hf : ContDiffAt ℂ 2 f z) (hz : f z ≠ 0) (u v : V) :
    ContinuousAt (fun y => berryDerivativeCandidate (f y) (fderiv ℂ f y).toLinearMap
      (fun a b => fderiv ℂ (fderiv ℂ f) y a b) u v) z := by
  have hD : ContinuousAt (fderiv ℂ f) z := hf.continuousAt_fderiv (by norm_num)
  have hB : ContinuousAt (fderiv ℂ (fderiv ℂ f)) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  have hDu : ContinuousAt (fun y => fderiv ℂ f y u) z := hD.clm_apply continuousAt_const
  have hDv : ContinuousAt (fun y => fderiv ℂ f y v) z := hD.clm_apply continuousAt_const
  have hBuv : ContinuousAt (fun y => fderiv ℂ (fderiv ℂ f) y u v) z :=
    (hB.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hn := coordinateNormSq_continuousAt hf.continuousAt
  have hnz : coordinateNormSq (f z) ≠ 0 := (coordinateNormSq_pos (f z) hz).ne'
  have hN := Complex.continuous_im.continuousAt.comp
    ((coordinatePairing_continuousAt hDu hDv).add
      (coordinatePairing_continuousAt hf.continuousAt hBuv))
  have hV := Complex.continuous_im.continuousAt.comp
    (coordinatePairing_continuousAt hf.continuousAt hDv)
  have hU := Complex.continuous_re.continuousAt.comp
    (coordinatePairing_continuousAt hf.continuousAt hDu)
  exact ((hN.mul hn).sub (hV.mul (continuousAt_const.mul hU))).div
    (continuousAt_const.mul (hn.pow 2))
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 2 hnz))

theorem berryConnection_hasDerivAt_affine {f : V → ι → ℂ} (z u v : V) (t : ℝ)
    (hf : ContDiffAt ℂ 2 f (z + t • u)) (hz : f (z + t • u) ≠ 0) :
    HasDerivAt (fun r : ℝ => berryConnection (f (z + r • u))
      (fderiv ℂ f (z + r • u)).toLinearMap v)
      (berryDerivativeCandidate (f (z + t • u)) (fderiv ℂ f (z + t • u)).toLinearMap
        (fun a b => fderiv ℂ (fderiv ℂ f) (z + t • u) a b) u v) t := by
  have hline : HasDerivAt (fun r : ℝ => z + r • u) u t := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id t).smul_const u).const_add z)
  have hfirst := ((hf.differentiableAt (by norm_num)).hasFDerivAt.restrictScalars ℝ)
  have hw : HasDerivAt (fun r : ℝ => f (z + r • u)) (fderiv ℂ f (z + t • u) u) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using
      hfirst.comp_hasDerivAt t hline
  have hsecond := (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.restrictScalars ℝ)
  have hD : HasDerivAt (fun r : ℝ => fderiv ℂ f (z + r • u))
      (fderiv ℂ (fderiv ℂ f) (z + t • u) u) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using
      hsecond.comp_hasDerivAt t hline
  have hd : HasDerivAt (fun r : ℝ => fderiv ℂ f (z + r • u) v)
      (fderiv ℂ (fderiv ℂ f) (z + t • u) u v) t :=
    ((ContinuousLinearMap.apply ℂ (ι → ℂ) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hD
  simpa only [berryConnection, berryDerivativeCandidate, ContinuousLinearMap.coe_coe] using
    hasDerivAt_berry_path hw hd hz

end BerryCalculus

section HolomorphicRegularity

open _root_.Complex _root_.Metric Set Filter _root_.Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_line_cauchy {f : V → F} {s : Set V} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (x v : V) {R : ℝ} (hR : 0 < R)
    (hsub : ∀ t : ℂ, ‖t‖ ≤ R → x + t • v ∈ s) :
    (∮ t in C(0, R), (1 / t ^ 2) • f (x + t • v)) =
      (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f x v := by
  have hline (t : ℂ) (ht : ‖t‖ ≤ R) :
      HasDerivAt (fun t : ℂ => f (x + t • v)) (fderiv ℂ f (x + t • v) v) t := by
    have hD := (hf.differentiableAt (hs.mem_nhds (hsub t ht))).hasFDerivAt
    simpa only [one_smul, Function.comp_def, id_eq] using
      hD.comp_hasDerivAt t (((hasDerivAt_id t).smul_const v).const_add x)
  have hc : DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) (closedBall 0 R) := by
    intro t ht
    exact (hline t (by simpa using ht)).differentiableAt.differentiableWithinAt
  have he := hc.deriv_eq_smul_circleIntegral hR
  have hd := (hline 0 (by simp [hR.le])).deriv
  simpa only [sub_zero, hd, zero_smul, add_zero] using he

theorem holomorphic_continuous_fderiv_apply {f : V → F} {s : Set V} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) {x : V} (hx : x ∈ s) (v : V) :
    ContinuousAt (fun y => fderiv ℂ f y v) x := by
  by_cases hv : v = 0
  · subst v
    simpa using (continuousAt_const : ContinuousAt (fun _ : V => (0 : F)) x)
  obtain ⟨e, he, hes⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let R : ℝ := e / (2 * ‖v‖)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hR : 0 < R := div_pos he (mul_pos (by norm_num) hvn)
  have hRv : R * ‖v‖ = e / 2 := by dsimp [R]; field_simp
  let U := ball x (e / 2)
  have hU : U ∈ 𝓝 x := ball_mem_nhds x (half_pos he)
  have hsub (y : V) (hy : y ∈ U) (t : ℂ) (ht : ‖t‖ ≤ R) : y + t • v ∈ s := by
    apply hes
    rw [mem_ball, dist_eq_norm]
    calc
      ‖y + t • v - x‖ = ‖(y - x) + t • v‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖t • v‖ := norm_add_le _ _
      _ < e / 2 + e / 2 := by
        have hyt : ‖y - x‖ < e / 2 := by simpa [U, dist_eq_norm] using hy
        have htv : ‖t • v‖ ≤ e / 2 := by rw [norm_smul, ← hRv]; gcongr
        linarith
      _ = e := by ring
  let g : U → ℝ → F := fun y t =>
    (circleMap 0 R t * Complex.I) • ((1 / circleMap 0 R t ^ 2) •
      f (y.val + circleMap 0 R t • v))
  have hgc : Continuous g.uncurry := by
    have hmap : Continuous (fun q : U × ℝ => q.1.val + circleMap 0 R q.2 • v) :=
      (continuous_subtype_val.comp continuous_fst).add
        (((continuous_circleMap 0 R).comp continuous_snd).smul continuous_const)
    have hfc := hf.continuousOn.comp_continuous hmap (fun q =>
      hsub q.1.val q.1.property (circleMap 0 R q.2) (by simp only [norm_circleMap_zero, abs_of_pos hR, le_refl]))
    have hinv : Continuous (fun q : U × ℝ => (1 : ℂ) / circleMap 0 R q.2 ^ 2) :=
      continuous_const.div (((continuous_circleMap 0 R).comp continuous_snd).pow 2)
        (fun q => pow_ne_zero 2 (circleMap_ne_center (c := 0) hR.ne' (θ := q.2)))
    exact (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const).smul
      (hinv.smul hfc)
  have hc : Continuous (fun y : U => ∫ t in (0 : ℝ)..2 * Real.pi, g y t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hgc _ _
  have heq (y : U) : (∫ t in (0 : ℝ)..2 * Real.pi, g y t) =
      (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y.val v := by
    simpa only [circleIntegral, deriv_circleMap, g] using
      holomorphic_line_cauchy hs hf y.val v hR (hsub y.val y.property)
  have hcc : Continuous (fun y : U => (2 * Real.pi * Complex.I : ℂ) •
      fderiv ℂ f y.val v) := hc.congr heq
  have hcf : Continuous (fun y : U => fderiv ℂ f y.val v) := by
    have h := hcc.const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹
    change Continuous (fun y : U => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ((2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y.val v)) at h
    simpa only [inv_smul_smul₀ Complex.two_pi_I_ne_zero] using h
  exact (continuousOn_iff_continuous_domRestrict.mpr hcf x (mem_of_mem_nhds hU)).continuousAt hU

theorem holomorphic_continuous_fderiv [FiniteDimensional ℂ V]
    {f : V → F} {s : Set V} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContinuousOn (fderiv ℂ f) s := by
  intro x hx
  exact (continuousAt_clm_apply.mpr (holomorphic_continuous_fderiv_apply hs hf hx)).continuousWithinAt

theorem holomorphic_contDiffOn_one [FiniteDimensional ℂ V]
    {f : V → F} {s : Set V} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℂ 1 f s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  exact ⟨hf, by simp, contDiffOn_zero.mpr (holomorphic_continuous_fderiv hs hf)⟩

open _root_.MeasureTheory
open scoped Interval

omit [CompleteSpace F] in
theorem hasFDerivAt_intervalIntegral_of_jointContinuous [FiniteDimensional ℂ V]
    {g : V → ℝ → F} {D : V → ℝ → V →L[ℂ] F} {s : Set V} (hs : IsOpen s)
    (hg : ContinuousOn g.uncurry (s ×ˢ Set.univ))
    (hD : ContinuousOn D.uncurry (s ×ˢ Set.univ))
    (hd : ∀ x ∈ s, ∀ t, HasFDerivAt (fun y => g y t) (D x t) x)
    {x : V} (hx : x ∈ s) (a b : ℝ) :
    HasFDerivAt (fun y => ∫ t in a..b, g y t) (∫ t in a..b, D x t) x := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  let K := closedBall x r ×ˢ Set.uIcc a b
  have hK : IsCompact K := (isCompact_closedBall x r).prod isCompact_uIcc
  have hKsub : K ⊆ s ×ˢ Set.univ := fun q hq => ⟨hrs hq.1, Set.mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hD.mono hKsub).norm
  have hbound (y : V) (hy : y ∈ closedBall x r) (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      ‖D y t‖ ≤ M := hM (Set.mem_image_of_mem
        (fun q : V × ℝ => ‖D q.1 q.2‖) (show (y, t) ∈ K from ⟨hy, ht⟩))
  have hgc (y : V) (hy : y ∈ s) : Continuous (g y) :=
    hg.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hy, Set.mem_univ _⟩)
  have hDc : Continuous (D x) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hx, Set.mem_univ _⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall x r) (bound := fun _ => M) (closedBall_mem_nhds x hr)
  · filter_upwards [hs.mem_nhds hx] with y hy
    exact (hgc y hy).aestronglyMeasurable
  · exact (hgc x hx).intervalIntegrable a b
  · exact hDc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t ht y hy => hbound y hy t (Set.uIoc_subset_uIcc ht))
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t _ y hy => hd y (hrs hy) t)

theorem holomorphic_differentiable_fderiv_apply [FiniteDimensional ℂ V]
    {f : V → F} {s : Set V} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {x : V} (hx : x ∈ s) (v : V) : DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  by_cases hv : v = 0
  · subst v
    simp
  obtain ⟨e, he, hes⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let R : ℝ := e / (2 * ‖v‖)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hR : 0 < R := div_pos he (mul_pos (by norm_num) hvn)
  have hRv : R * ‖v‖ = e / 2 := by dsimp [R]; field_simp
  let U := ball x (e / 2)
  have hU : U ∈ 𝓝 x := ball_mem_nhds x (half_pos he)
  have hsub (y : V) (hy : y ∈ U) (t : ℂ) (ht : ‖t‖ ≤ R) : y + t • v ∈ s := by
    apply hes
    rw [mem_ball, dist_eq_norm]
    calc
      ‖y + t • v - x‖ = ‖(y - x) + t • v‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖t • v‖ := norm_add_le _ _
      _ < e / 2 + e / 2 := by
        have hyt : ‖y - x‖ < e / 2 := by simpa [U, dist_eq_norm] using hy
        have htv : ‖t • v‖ ≤ e / 2 := by rw [norm_smul, ← hRv]; gcongr
        linarith
      _ = e := by ring
  let c : ℝ → ℂ := fun t => (circleMap 0 R t * Complex.I) * (1 / circleMap 0 R t ^ 2)
  have hc : Continuous c :=
    ((continuous_circleMap 0 R).mul continuous_const).mul
      (continuous_const.div ((continuous_circleMap 0 R).pow 2)
        (fun t => pow_ne_zero 2 (circleMap_ne_center (c := 0) hR.ne' (θ := t))))
  let g : V → ℝ → F := fun y t => c t • f (y + circleMap 0 R t • v)
  let D : V → ℝ → V →L[ℂ] F := fun y t => c t • fderiv ℂ f (y + circleMap 0 R t • v)
  have hmap : Continuous (fun q : V × ℝ => q.1 + circleMap 0 R q.2 • v) :=
    continuous_fst.add (((continuous_circleMap 0 R).comp continuous_snd).smul continuous_const)
  have hmaps : Set.MapsTo (fun q : V × ℝ => q.1 + circleMap 0 R q.2 • v)
      (U ×ˢ Set.univ) s := fun q hq => hsub q.1 hq.1 _
        (by simp only [norm_circleMap_zero, abs_of_pos hR, le_refl])
  have hgc : ContinuousOn g.uncurry (U ×ˢ Set.univ) :=
    (hc.comp continuous_snd).continuousOn.smul (hf.continuousOn.comp hmap.continuousOn hmaps)
  have hDc : ContinuousOn D.uncurry (U ×ˢ Set.univ) :=
    (hc.comp continuous_snd).continuousOn.smul
      ((holomorphic_continuous_fderiv hs hf).comp hmap.continuousOn hmaps)
  have hd (y : V) (hy : y ∈ U) (t : ℝ) : HasFDerivAt (fun y => g y t) (D y t) y := by
    have hyt := hsub y hy (circleMap 0 R t)
      (by simp only [norm_circleMap_zero, abs_of_pos hR, le_refl])
    have hyf := (hf.differentiableAt (hs.mem_nhds hyt)).hasFDerivAt
    exact ((hasFDerivAt_comp_add_right _).mpr hyf).const_smul (c t)
  have hint := hasFDerivAt_intervalIntegral_of_jointContinuous isOpen_ball hgc hDc hd
    (mem_of_mem_nhds hU) 0 (2 * Real.pi)
  have heq (y : V) (hy : y ∈ U) : (∫ t in (0 : ℝ)..2 * Real.pi, g y t) =
      (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y v := by
    simpa only [circleIntegral, deriv_circleMap, g, c, mul_smul] using
      holomorphic_line_cauchy hs hf y v hR (hsub y hy)
  have heq' : (fun y => (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y v) =ᶠ[𝓝 x]
      fun y => ∫ t in (0 : ℝ)..2 * Real.pi, g y t := by
    filter_upwards [hU] with y hy using (heq y hy).symm
  have hdiff := (hint.differentiableAt.congr_of_eventuallyEq heq').const_smul
    (2 * Real.pi * Complex.I : ℂ)⁻¹
  change DifferentiableAt ℂ (fun y => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ((2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y v)) x at hdiff
  simpa only [inv_smul_smul₀ Complex.two_pi_I_ne_zero] using hdiff

theorem holomorphic_differentiable_fderiv [FiniteDimensional ℂ V]
    {f : V → F} {s : Set V} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fderiv ℂ f) s := by
  let e : (V →L[ℂ] F) ≃L[ℂ] (Fin (Module.finrank ℂ V) → F) :=
    ((ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).arrowCongr
      (1 : F ≃L[ℂ] F)).trans (ContinuousLinearEquiv.piRing _)
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  apply e.comp_differentiableAt_iff.mp
  apply differentiableAt_pi.mpr
  intro i
  exact holomorphic_differentiable_fderiv_apply hs hf hx _

theorem holomorphic_contDiffOn_two [FiniteDimensional ℂ V]
    {f : V → F} {s : Set V} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℂ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  exact ⟨hf, by simp, holomorphic_contDiffOn_one hs (holomorphic_differentiable_fderiv hs hf)⟩

end HolomorphicRegularity

section ProjectivePullback

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open Filter _root_.Topology

variable {ι : Type*} [Fintype ι]
variable (p : V → Projectivization ℂ (ι → ℂ))

def projectivePullbackChart (i : ι) (z : V) : ι → ℂ := AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (p z)

variable (hp : Continuous p)

include hp

omit [NormedSpace ℂ V] [Fintype ι] in
theorem projective_patch_eventually (i : ι) (z : V) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) :
    ∀ᶠ w in 𝓝 z, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p w) :=
  ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hp).mem_nhds hi

omit hp [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] in
theorem projective_chart_transition (i j : ι) (z : V)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z)) :
    projectivePullbackChart p i z =
      projectivePullbackChart p i z j • projectivePullbackChart p j z := by
  have hn := (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (p z) hi).mp hj
  ext k
  change AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k (p z) = AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j (p z) * AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j k (p z)
  rw [AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i j k (p z) hi]
  field_simp

theorem projective_chart_differentiableAt (z : V)
    (hz : ∃ j, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p j) z)
    (i : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) :
    DifferentiableAt ℂ (projectivePullbackChart p i) z := by
  obtain ⟨j, hj, hd⟩ := hz
  have hn : projectivePullbackChart p j z i ≠ 0 :=
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero j i (p z) hj).mp hi
  have hdi : DifferentiableAt ℂ (fun w => projectivePullbackChart p j w i) z :=
    (differentiableAt_pi.mp hd) i
  have he : projectivePullbackChart p i =ᶠ[𝓝 z]
      fun w => (projectivePullbackChart p j w i)⁻¹ • projectivePullbackChart p j w := by
    filter_upwards [projective_patch_eventually p hp j z hj] with w hw
    ext k
    change AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k (p w) = (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j i (p w))⁻¹ * AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j k (p w)
    rw [AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula j i k (p w) hw, div_eq_mul_inv, mul_comm]
  exact ((hdi.inv hn).smul hd).congr_of_eventuallyEq he

omit [Fintype ι] in
theorem projective_chart_fderiv_self (i : ι) (z : V) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z))
    (hd : DifferentiableAt ℂ (projectivePullbackChart p i) z) (u : V) :
    fderiv ℂ (projectivePullbackChart p i) z u i = 0 := by
  have he : (fun w => projectivePullbackChart p i w i) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
    filter_upwards [projective_patch_eventually p hp i z hi] with w hw
    exact hw
  have hf := he.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_apply hd i] at hf
  simpa using congrArg (fun L : V →L[ℂ] ℂ => L u) hf

theorem projective_chart_fderiv_transition (i j : ι) (z : V)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z))
    (hdi : DifferentiableAt ℂ (projectivePullbackChart p i) z)
    (hdj : DifferentiableAt ℂ (projectivePullbackChart p j) z) :
    fderiv ℂ (projectivePullbackChart p i) z =
      projectivePullbackChart p i z j • fderiv ℂ (projectivePullbackChart p j) z +
        (fderiv ℂ (fun w => projectivePullbackChart p i w j) z).smulRight
          (projectivePullbackChart p j z) := by
  have he : projectivePullbackChart p i =ᶠ[𝓝 z]
      fun w => projectivePullbackChart p i w j • projectivePullbackChart p j w := by
    filter_upwards [projective_patch_eventually p hp i z hi,
      projective_patch_eventually p hp j z hj] with w hwi hwj
    exact projective_chart_transition p i j w hwi hwj
  rw [he.fderiv_eq]
  exact fderiv_smul ((differentiableAt_pi.mp hdi) j) hdj

theorem projective_fubiniStudy_chart_independent (i j : ι) (z : V)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z))
    (hdi : DifferentiableAt ℂ (projectivePullbackChart p i) z)
    (hdj : DifferentiableAt ℂ (projectivePullbackChart p j) z) :
    fubiniStudyForm (projectivePullbackChart p i z)
      (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap =
    fubiniStudyForm (projectivePullbackChart p j z)
      (fderiv ℂ (projectivePullbackChart p j) z).toLinearMap := by
  let a := projectivePullbackChart p i z j
  let w := projectivePullbackChart p j z
  let D := (fderiv ℂ (projectivePullbackChart p j) z).toLinearMap
  let b := (fderiv ℂ (fun x => projectivePullbackChart p i x j) z).toLinearMap
  have hw : w ≠ 0 := AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero j w hj
  have ha : a ≠ 0 := (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (p z) hi).mp hj
  have hD : (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap =
      a • D + b.smulRight w := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (projective_chart_fderiv_transition p hp i j z hi hj hdi hdj)
  calc
    _ = fubiniStudyForm (a • w) (a • D + b.smulRight w) :=
      congrArg₂ fubiniStudyForm (projective_chart_transition p i j z hi hj) hD
    _ = _ := fubiniStudyForm_gauge a ha w hw D b

omit hp in
/-- The pullback of the normalized Fubini--Study form, computed in any available
projective chart. Chart independence is proved for holomorphic maps below. -/
def projectiveFubiniStudy (z : V) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  let i := Classical.choose (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p z))
  fubiniStudyForm (projectivePullbackChart p i z)
    (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap

omit hp in
theorem projectiveFubiniStudy_symm (z u v : V) :
    projectiveFubiniStudy p z v u = star (projectiveFubiniStudy p z u v) :=
  fubiniStudyForm_symm _ _ u v

theorem projectiveFubiniStudy_eq_chart (z : V)
    (hz : ∃ j, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p j) z)
    (i : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) :
    projectiveFubiniStudy p z = fubiniStudyForm (projectivePullbackChart p i z)
      (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap := by
  let j := Classical.choose (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p z))
  have hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z) := Classical.choose_spec (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p z))
  exact projective_fubiniStudy_chart_independent p hp j i z hj hi
    (projective_chart_differentiableAt p hp z hz j hj)
    (projective_chart_differentiableAt p hp z hz i hi)

theorem projectiveFubiniStudy_positive (z : V)
    (hz : ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p i) z ∧
      Function.Injective (fderiv ℂ (projectivePullbackChart p i) z))
    (u : V) (hu : u ≠ 0) : 0 < (projectiveFubiniStudy p z u u).re := by
  obtain ⟨i, hi, hd, hD⟩ := hz
  rw [projectiveFubiniStudy_eq_chart p hp z ⟨i, hi, hd⟩ i hi]
  have hwi : projectivePullbackChart p i z i = 1 := hi
  exact fubiniStudyForm_positive _ _ hD i (by rw [hwi]; exact one_ne_zero)
    (projective_chart_fderiv_self p hp i z hi hd) u hu

theorem projectiveFubiniStudy_periodic (a : V) (ha : ∀ z, p (z + a) = p z)
    (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧
      DifferentiableAt ℂ (projectivePullbackChart p i) z) (z : V) :
    projectiveFubiniStudy p (z + a) = projectiveFubiniStudy p z := by
  obtain ⟨i, hi, _⟩ := hhol z
  have hia : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + a)) := by rwa [ha]
  rw [projectiveFubiniStudy_eq_chart p hp (z + a) (hhol (z + a)) i hia,
    projectiveFubiniStudy_eq_chart p hp z (hhol z) i hi]
  have he : (fun w => projectivePullbackChart p i (w + a)) = projectivePullbackChart p i := by
    funext w
    exact congrArg (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i) (ha w)
  have hD := congrArg (fun g : V → (ι → ℂ) => fderiv ℂ g z) he
  rw [fderiv_comp_add_right] at hD
  rw [hD]
  exact congrArg (fun w => fubiniStudyForm w
    (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap) (congrFun he z)

theorem projective_chart_contDiffOn_one [FiniteDimensional ℂ V]
    (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧
      DifferentiableAt ℂ (projectivePullbackChart p i) z) (i : ι) :
    ContDiffOn ℂ 1 (projectivePullbackChart p i) {z | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)} := by
  apply holomorphic_contDiffOn_one ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hp)
  intro z hz
  exact (projective_chart_differentiableAt p hp z (hhol z) i hz).differentiableWithinAt

theorem projective_chart_contDiffOn_two [FiniteDimensional ℂ V]
    (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧
      DifferentiableAt ℂ (projectivePullbackChart p i) z) (i : ι) :
    ContDiffOn ℂ 2 (projectivePullbackChart p i) {z | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)} := by
  apply holomorphic_contDiffOn_two ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hp)
  intro z hz
  exact (projective_chart_differentiableAt p hp z (hhol z) i hz).differentiableWithinAt

theorem projectiveFubiniStudy_continuous [FiniteDimensional ℂ V]
    (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧
      DifferentiableAt ℂ (projectivePullbackChart p i) z) (u v : V) :
    Continuous (fun z => projectiveFubiniStudy p z u v) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i, hi, _⟩ := hhol z
  let c := projectivePullbackChart p i
  have hpatch : IsOpen {w | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p w)} :=
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hp
  have hc : ContinuousAt c z :=
    (projective_chart_differentiableAt p hp z (hhol z) i hi).continuousAt
  have hD : ContinuousAt (fderiv ℂ c) z := by
    apply (holomorphic_continuous_fderiv hpatch _ z hi).continuousAt (hpatch.mem_nhds hi)
    intro w hw
    exact (projective_chart_differentiableAt p hp w (hhol w) i hw).differentiableWithinAt
  have hnorm : ContinuousAt (fun w => coordinateNormSq (c w)) z :=
    tendsto_finsetSum _ (fun j _ => Complex.continuous_normSq.continuousAt.comp
      ((continuousAt_pi.mp hc) j))
  have hne : coordinateNormSq (c z) ≠ 0 :=
    (coordinateNormSq_pos (c z) (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero i (c z) hi)).ne'
  have hscale : ContinuousAt (fun w =>
      ((1 / (2 * Real.pi * coordinateNormSq (c w) ^ 2) : ℝ) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.div
      (continuousAt_const.mul (hnorm.pow 2)) (mul_ne_zero
        (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 2 hne)))
  have hh (a : V) (j k : ι) : ContinuousAt (fun w =>
      c w j * fderiv ℂ c w a k - c w k * fderiv ℂ c w a j) z := by
    exact (((continuousAt_pi.mp hc) j).mul ((continuousAt_pi.mp (hD.clm_apply continuousAt_const)) k)).sub
      (((continuousAt_pi.mp hc) k).mul ((continuousAt_pi.mp (hD.clm_apply continuousAt_const)) j))
  have hfs : ContinuousAt (fun w => fubiniStudyForm (c w) (fderiv ℂ c w).toLinearMap u v) z := by
    apply hscale.mul
    apply tendsto_finsetSum
    intro jk _
    exact (hh u jk.1 jk.2).star.mul (hh v jk.1 jk.2)
  apply hfs.congr_of_eventuallyEq
  filter_upwards [projective_patch_eventually p hp i z hi] with w hw
  exact congrArg (fun H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => H u v)
    (projectiveFubiniStudy_eq_chart p hp w (hhol w) i hw)

omit hp in
def projectiveBerryConnection (i : ι) (z u : V) : ℝ :=
  berryConnection (projectivePullbackChart p i z)
    (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap u

theorem projectiveBerryConnection_change (i j : ι) (z u : V)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p z))
    (hdi : DifferentiableAt ℂ (projectivePullbackChart p i) z)
    (hdj : DifferentiableAt ℂ (projectivePullbackChart p j) z) :
    projectiveBerryConnection p i z u = projectiveBerryConnection p j z u +
      (fderiv ℂ (fun w => projectivePullbackChart p i w j) z u /
        projectivePullbackChart p i z j).im / (2 * Real.pi) := by
  let a := projectivePullbackChart p i z j
  let w := projectivePullbackChart p j z
  let D := (fderiv ℂ (projectivePullbackChart p j) z).toLinearMap
  let b := (fderiv ℂ (fun x => projectivePullbackChart p i x j) z).toLinearMap
  have hw : w ≠ 0 := AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero j w hj
  have ha : a ≠ 0 := (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (p z) hi).mp hj
  have hD : (fderiv ℂ (projectivePullbackChart p i) z).toLinearMap =
      a • D + b.smulRight w := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (projective_chart_fderiv_transition p hp i j z hi hj hdi hdj)
  calc
    _ = berryConnection (a • w) (a • D + b.smulRight w) u :=
      congrArg₂ (fun w D => berryConnection w D u) (projective_chart_transition p i j z hi hj) hD
    _ = _ := berryConnection_gauge a ha w hw D b u

theorem projectiveBerryConnection_continuousAt [FiniteDimensional ℂ V]
    (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧
      DifferentiableAt ℂ (projectivePullbackChart p i) z) (i : ι) (z u : V)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z)) : ContinuousAt (fun w => projectiveBerryConnection p i w u) z := by
  have hpatch : {w | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p w)} ∈ 𝓝 z := projective_patch_eventually p hp i z hi
  exact berryConnection_continuousAt ((projective_chart_contDiffOn_one p hp hhol i).contDiffAt hpatch)
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero i (projectivePullbackChart p i z) hi) u

omit hp in
theorem projectiveBerryConnection_periodic (a : V) (ha : ∀ z, p (z + a) = p z) (i : ι) (z u : V) :
    projectiveBerryConnection p i (z + a) u = projectiveBerryConnection p i z u := by
  have he : (fun w => projectivePullbackChart p i (w + a)) = projectivePullbackChart p i := by
    funext w
    exact congrArg (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i) (ha w)
  have hD := congrArg (fun g : V → (ι → ℂ) => fderiv ℂ g z) he
  rw [fderiv_comp_add_right] at hD
  unfold projectiveBerryConnection
  rw [hD, congrFun he z]

end ProjectivePullback

section TorusPullback

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable (Λ : AddSubgroup V) {ι : Type*} [Fintype ι]
variable (f : V ⧸ Λ → Projectivization ℂ (ι → ℂ))

def torusFubiniStudy (q : V ⧸ Λ) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  projectiveFubiniStudy (fun z => f (QuotientAddGroup.mk z)) (Quotient.out q)

variable (hf : Continuous f)
  (hhol : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
    DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

include hf hhol

theorem torusFubiniStudy_lift (z : V) :
    torusFubiniStudy Λ f (QuotientAddGroup.mk z) =
      projectiveFubiniStudy (fun w => f (QuotientAddGroup.mk w)) z := by
  let a := Quotient.out (QuotientAddGroup.mk z : V ⧸ Λ) - z
  have ha : a ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq _)
  have hper (w : V) : f (QuotientAddGroup.mk (w + a)) = f (QuotientAddGroup.mk w) := by
    apply congrArg f
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [add_sub_cancel_left] using ha
  have he : z + a = Quotient.out (QuotientAddGroup.mk z : V ⧸ Λ) := by dsimp [a]; abel
  simpa only [he, torusFubiniStudy, Function.comp_def] using
    projectiveFubiniStudy_periodic _ (hf.comp QuotientAddGroup.continuous_mk) a hper hhol z

omit hf hhol in
theorem torusFubiniStudy_symm (q : V ⧸ Λ) (u v : V) :
    torusFubiniStudy Λ f q v u = star (torusFubiniStudy Λ f q u v) :=
  projectiveFubiniStudy_symm _ _ u v

omit hhol in
theorem torusFubiniStudy_positive
    (himm : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z))
    (q : V ⧸ Λ) (u : V) (hu : u ≠ 0) : 0 < (torusFubiniStudy Λ f q u u).re :=
  projectiveFubiniStudy_positive _ (hf.comp QuotientAddGroup.continuous_mk)
    (Quotient.out q) (himm (Quotient.out q)) u hu

theorem torusFubiniStudy_continuous [FiniteDimensional ℂ V] (u v : V) :
    Continuous (fun q => torusFubiniStudy Λ f q u v) := by
  apply (QuotientAddGroup.isQuotientMap_mk Λ).continuous_iff.mpr
  have hc := projectiveFubiniStudy_continuous _ (hf.comp QuotientAddGroup.continuous_mk) hhol u v
  convert! hc using 1
  funext z
  exact congrArg (fun H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => H u v) (torusFubiniStudy_lift Λ f hf hhol z)

end TorusPullback

section HermitianAveraging

open _root_.MeasureTheory
variable {T : Type*} [MeasurableSpace T]
variable (μ : Measure T) (K : T → V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
  (hK : ∀ u v, Integrable (fun q => K q u v) μ)

/-- Averaging a family of Hermitian forms, using its scalar coefficients. -/
def averageHermitian : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun v := ∫ q, K q u v ∂μ
      map_add' := by
        intro v w
        simp only [map_add]
        exact integral_add (hK u v) (hK u w)
      map_smul' := by
        intro a v
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul a _ }
  map_add' := by
    intro u v
    ext w
    simp only [map_add, LinearMap.add_apply]
    exact integral_add (hK u w) (hK v w)
  map_smul' := by
    intro a u
    ext v
    change (∫ q, K q (a • u) v ∂μ) = star a * ∫ q, K q u v ∂μ
    have he (q : T) : K q (a • u) v = star a * K q u v := by simp
    simp_rw [he]
    exact integral_const_mul (star a) (fun q => K q u v)

theorem averageHermitian_apply (u v : V) :
    averageHermitian μ K hK u v = ∫ q, K q u v ∂μ := rfl

theorem averageHermitian_symm (hsym : ∀ q u v, K q v u = star (K q u v)) (u v : V) :
    averageHermitian μ K hK v u = star (averageHermitian μ K hK u v) := by
  calc
    _ = ∫ q, star (K q u v) ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall (fun q => hsym q u v))
    _ = _ := integral_conj

theorem averageHermitian_positive [IsProbabilityMeasure μ]
    (hpos : ∀ q u, u ≠ 0 → 0 < (K q u u).re) (u : V) (hu : u ≠ 0) :
    0 < (averageHermitian μ K hK u u).re := by
  have hre : (∫ q, K q u u ∂μ).re = ∫ q, (K q u u).re ∂μ := (integral_re (hK u u)).symm
  rw [averageHermitian_apply, hre]
  have hr : Integrable (fun q => (K q u u).re) μ := (hK u u).re
  rw [integral_pos_iff_support_of_nonneg (fun q => (hpos q u hu).le) hr]
  have hs : Function.support (fun q => (K q u u).re) = Set.univ := by
    ext q
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos q u hu).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

end HermitianAveraging

open _root_.MeasureTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

def normalizedAddHaar (T : Type*) [AddGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] : Measure T :=
  Measure.addHaarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts T)

instance normalizedAddHaar_probability (T : Type*) [AddGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] :
    IsProbabilityMeasure (normalizedAddHaar T) := ⟨Measure.addHaarMeasure_self⟩

instance normalizedAddHaar_invariant (T : Type*) [AddGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] :
    (normalizedAddHaar T).IsAddLeftInvariant := by unfold normalizedAddHaar; infer_instance

variable [FiniteDimensional ℂ V] (Λ : AddSubgroup V) [CompactSpace (V ⧸ Λ)]
  [MeasurableSpace (V ⧸ Λ)] [BorelSpace (V ⧸ Λ)] {ι : Type*} [Fintype ι]
  (f : V ⧸ Λ → Projectivization ℂ (ι → ℂ)) (hf : Continuous f)
  (hhol : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
    DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

include hf hhol in
theorem torusFubiniStudy_integrable (u v : V) :
    Integrable (fun q => torusFubiniStudy Λ f q u v) (normalizedAddHaar (V ⧸ Λ)) :=
  (torusFubiniStudy_continuous Λ f hf hhol u v).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

/-- The constant Hermitian form obtained by averaging projective curvature over
the torus with its normalized translation-invariant measure. -/
def averagedProjectiveForm : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  averageHermitian (normalizedAddHaar (V ⧸ Λ)) (torusFubiniStudy Λ f)
    (torusFubiniStudy_integrable Λ f hf hhol)

theorem averagedProjectiveForm_apply (u v : V) :
    averagedProjectiveForm Λ f hf hhol u v =
      ∫ q, torusFubiniStudy Λ f q u v ∂ normalizedAddHaar (V ⧸ Λ) := rfl

theorem averagedProjectiveForm_symm (u v : V) :
    averagedProjectiveForm Λ f hf hhol v u = star (averagedProjectiveForm Λ f hf hhol u v) :=
  averageHermitian_symm _ _ _ (torusFubiniStudy_symm Λ f) u v

theorem averagedProjectiveForm_positive
    (himm : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z))
    (u : V) (hu : u ≠ 0) : 0 < (averagedProjectiveForm Λ f hf hhol u u).re :=
  averageHermitian_positive _ _ _ (torusFubiniStudy_positive Λ f hf himm) u hu

theorem averagedProjectiveForm_translate (a : V ⧸ Λ) (u v : V) :
    (∫ q, torusFubiniStudy Λ f (a + q) u v ∂ normalizedAddHaar (V ⧸ Λ)) =
      averagedProjectiveForm Λ f hf hhol u v := by
  rw [averagedProjectiveForm_apply]
  exact integral_add_left_eq_self (μ := normalizedAddHaar (V ⧸ Λ))
    (fun q => torusFubiniStudy Λ f q u v) a

end

section

open _root_.MeasureTheory Set Filter _root_.Topology

theorem exp_integral_logarithmicDerivative {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) (hne : ∀ t ∈ Icc a b, g t ≠ 0) :
    Complex.exp (∫ t in a..b, g' t / g t) = g b / g a := by
  let h : ℝ → ℂ := fun t => g' t / g t
  have hc : ContinuousOn h (Icc a b) := hg'.div hg hne
  have hi : IntervalIntegrable h volume a b := hc.intervalIntegrable_of_Icc hab
  let F : ℝ → ℂ := fun t => ∫ r in a..t, h r
  have hFc : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : a ∈ uIcc a b)
  have hFd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F (h t) t := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1.le, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2.le
    exact intervalIntegral.integral_hasDerivAt_right (hi.mono_set hsub)
      ⟨Icc a b, Icc_mem_nhds ht.1 ht.2, hc.aestronglyMeasurable measurableSet_Icc⟩
      ((hc t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2))
  let k : ℝ → ℂ := fun t => Complex.exp (-F t) * g t
  have hkc : ContinuousOn k (Icc a b) :=
    (Complex.continuous_exp.comp_continuousOn hFc.neg).mul hg
  have hkd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt k (0 : ℂ) t := by
    have hn := hne t ⟨ht.1.le, ht.2.le⟩
    have he : (Complex.exp (-F t) * -(h t)) * g t + Complex.exp (-F t) * g' t = 0 := by
      dsimp [h]
      field_simp
      ring
    convert! ((hFd t ht).neg.cexp.mul (hd t ht)) using 1
    exact he.symm
  have hk := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hkc hkd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
  have hka : k a = g a := by simp [k, F]
  have hkb : Complex.exp (-F b) * g b = g a := by
    simpa only [intervalIntegral.integral_zero, hka, sub_eq_zero, k] using hk.symm
  have hgb : g b = Complex.exp (F b) * g a := by
    have he := congrArg (fun z : ℂ => Complex.exp (F b) * z) hkb
    simpa only [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul] using he
  change Complex.exp (F b) = g b / g a
  rw [hgb, mul_div_cancel_right₀ _ (hne a ⟨le_rfl, hab⟩)]

def complexPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem complexPhase_exp (z : ℂ) : complexPhase (Complex.exp z) = Complex.exp (z.im * Complex.I) := by
  rw [complexPhase, Complex.norm_exp]
  have he : Complex.exp z = Complex.exp (z.re : ℂ) * Complex.exp (z.im * Complex.I) := by
    rw [← Complex.exp_add, Complex.re_add_im]
  rw [he, ← Complex.ofReal_exp]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Real.exp_pos z.re).ne')

theorem complexPhase_div (a b : ℂ) : complexPhase (a / b) = complexPhase a / complexPhase b := by
  simp only [complexPhase, norm_div, Complex.ofReal_div]
  ring

theorem exp_integral_im_logarithmicDerivative {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) (hne : ∀ t ∈ Icc a b, g t ≠ 0) :
    Complex.exp ((∫ t in a..b, (g' t / g t).im : ℝ) * Complex.I) =
      complexPhase (g b) / complexPhase (g a) := by
  have hi : IntervalIntegrable (fun t => g' t / g t) volume a b :=
    (hg'.div hg hne).intervalIntegrable_of_Icc hab
  have him : (∫ t in a..b, g' t / g t).im = ∫ t in a..b, (g' t / g t).im := by
    exact (Complex.imCLM.intervalIntegral_comp_comm hi).symm
  have he := congrArg complexPhase (exp_integral_logarithmicDerivative hab hg hg' hd hne)
  rwa [complexPhase_exp, complexPhase_div, him] at he

def connectionTransport (α : ℝ → ℝ) (a b : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * ∫ t in a..b, α t : ℝ) * Complex.I)

theorem connectionTransport_ne_zero (α : ℝ → ℝ) (a b : ℝ) :
    connectionTransport α a b ≠ 0 := Complex.exp_ne_zero _

theorem complexPhase_ne_zero {z : ℂ} (hz : z ≠ 0) : complexPhase z ≠ 0 :=
  div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.mpr hz)

theorem complexPhase_mul (a b : ℂ) : complexPhase (a * b) = complexPhase a * complexPhase b := by
  simp only [complexPhase, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

theorem connectionTransport_change {α β : ℝ → ℝ} {g g' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hβ : IntervalIntegrable β volume a b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) (hne : ∀ t ∈ Icc a b, g t ≠ 0)
    (hchange : ∀ t ∈ Icc a b, α t = β t + (g' t / g t).im / (2 * Real.pi)) :
    connectionTransport α a b = connectionTransport β a b * complexPhase (g b) / complexPhase (g a) := by
  have hi : IntervalIntegrable (fun t => (g' t / g t).im) volume a b :=
    (Complex.continuous_im.comp_continuousOn (hg'.div hg hne)).intervalIntegrable_of_Icc hab
  have hα : (∫ t in a..b, α t) = (∫ t in a..b, β t) +
      (∫ t in a..b, (g' t / g t).im) / (2 * Real.pi) := by
    calc
      _ = ∫ t in a..b, (β t + (g' t / g t).im / (2 * Real.pi)) :=
        intervalIntegral.integral_congr (fun t ht => hchange t (by simpa [uIcc_of_le hab] using ht))
      _ = _ := by
        rw [intervalIntegral.integral_add hβ (hi.div_const _)]
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_mul_const]
  rw [connectionTransport, hα]
  have he (r s : ℝ) : ((2 * Real.pi * (r + s / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I + (s : ℂ) * Complex.I := by
    have hreal : 2 * Real.pi * (r + s / (2 * Real.pi)) = 2 * Real.pi * r + s := by
      field_simp
    rw [hreal, Complex.ofReal_add]
    ring
  rw [he, Complex.exp_add, exp_integral_im_logarithmicDerivative hab hg hg' hd hne, mul_div_assoc]
  rfl

theorem connectionTransport_rectangle {A B : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hAb : IntervalIntegrable (fun s => A s c) volume a b)
    (hAt : IntervalIntegrable (fun s => A s d) volume a b)
    (hBl : IntervalIntegrable (B a) volume c d) (hBr : IntervalIntegrable (B b) volume c d) :
    Complex.exp ((2 * Real.pi * ((∫ t in c..d, B b t - B a t) -
      ∫ s in a..b, A s d - A s c) : ℝ) * Complex.I) =
      connectionTransport (fun s => A s c) a b * connectionTransport (B b) c d /
        (connectionTransport (fun s => A s d) a b * connectionTransport (B a) c d) := by
  rw [intervalIntegral.integral_sub hBr hBl, intervalIntegral.integral_sub hAt hAb]
  unfold connectionTransport
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem rectangle_normalization_cancel (h₀ h₁ v₀ v₁ a b c d : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ((h₀ * b / a) * (v₁ * d / b)) / ((h₁ * d / c) * (v₀ * c / a)) =
      (h₀ * v₁) / (h₁ * v₀) := by
  by_cases hh : h₁ = 0
  · simp [hh]
  by_cases hv : v₀ = 0
  · simp [hv]
  field_simp

theorem rectangle_integral_swap {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hF : ContinuousOn F.uncurry (Icc a b ×ˢ Icc c d)) :
    (∫ s in a..b, ∫ t in c..d, F s t) = ∫ t in c..d, ∫ s in a..b, F s t := by
  have hi : Integrable F.uncurry ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd] using
    integral_integral_swap hi

theorem rectangle_stokes {A B As Bt : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hAs : ContinuousOn As.uncurry (Icc a b ×ˢ Icc c d))
    (hBt : ContinuousOn Bt.uncurry (Icc a b ×ˢ Icc c d))
    (hA : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, HasDerivAt (A s) (As s t) t)
    (hB : ∀ t ∈ Icc c d, ∀ s ∈ Icc a b, HasDerivAt (fun r => B r t) (Bt s t) s) :
    (∫ s in a..b, ∫ t in c..d, (Bt s t - As s t)) =
      (∫ t in c..d, (B b t - B a t)) - ∫ s in a..b, (A s d - A s c) := by
  have hAsc (s : ℝ) (hs : s ∈ Icc a b) : ContinuousOn (As s) (Icc c d) :=
    hAs.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  have hBtc (s : ℝ) (hs : s ∈ Icc a b) : ContinuousOn (Bt s) (Icc c d) :=
    hBt.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  have hBts (t : ℝ) (ht : t ∈ Icc c d) : ContinuousOn (fun s => Bt s t) (Icc a b) :=
    hBt.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, ht⟩)
  have hFTC_A (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ t in c..d, As s t) = A s d - A s c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hA s hs t (by simpa [uIcc_of_le hcd] using ht))
      ((hAsc s hs).intervalIntegrable_of_Icc hcd)
  have hFTC_B (t : ℝ) (ht : t ∈ Icc c d) :
      (∫ s in a..b, Bt s t) = B b t - B a t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hB t ht s (by simpa [uIcc_of_le hab] using hs))
      ((hBts t ht).intervalIntegrable_of_Icc hab)
  have hAsc_int : IntervalIntegrable (fun s => ∫ t in c..d, As s t) volume a b := by
    have hi : Integrable As.uncurry ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
      rw [Measure.prod_restrict]
      exact (hAs.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    simpa only [intervalIntegral.integral_of_le hcd, Function.uncurry, IntegrableOn] using hi.integral_prod_left
  have hBtc_int : IntervalIntegrable (fun s => ∫ t in c..d, Bt s t) volume a b := by
    have hi : Integrable Bt.uncurry ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
      rw [Measure.prod_restrict]
      exact (hBt.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    simpa only [intervalIntegral.integral_of_le hcd, Function.uncurry, IntegrableOn] using hi.integral_prod_left
  calc
    _ = ∫ s in a..b, ((∫ t in c..d, Bt s t) - ∫ t in c..d, As s t) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
      exact intervalIntegral.integral_sub ((hBtc s hs').intervalIntegrable_of_Icc hcd)
        ((hAsc s hs').intervalIntegrable_of_Icc hcd)
    _ = (∫ s in a..b, ∫ t in c..d, Bt s t) - ∫ s in a..b, ∫ t in c..d, As s t :=
      intervalIntegral.integral_sub hBtc_int hAsc_int
    _ = _ := by
      rw [rectangle_integral_swap hab hcd hBt]
      congr 1
      · apply intervalIntegral.integral_congr
        intro t ht
        exact hFTC_B t (by simpa [uIcc_of_le hcd] using ht)
      · apply intervalIntegral.integral_congr
        intro s hs
        exact hFTC_A s (by simpa [uIcc_of_le hab] using hs)

section LocalStokes
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {ι : Type*} [Fintype ι]

theorem berryConnection_stokes_rectangle (f : V → ι → ℂ) (z u v : V) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, ContDiffAt ℂ 2 f (z + s • u + t • v))
    (hne : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, f (z + s • u + t • v) ≠ 0) :
    (∫ s in a..b, ∫ t in c..d, (fubiniStudyForm (f (z + s • u + t • v))
      (fderiv ℂ f (z + s • u + t • v)).toLinearMap u v).im) =
    (∫ t in c..d, berryConnection (f (z + b • u + t • v))
      (fderiv ℂ f (z + b • u + t • v)).toLinearMap v -
      berryConnection (f (z + a • u + t • v))
        (fderiv ℂ f (z + a • u + t • v)).toLinearMap v) -
    ∫ s in a..b, berryConnection (f (z + s • u + d • v))
      (fderiv ℂ f (z + s • u + d • v)).toLinearMap u -
      berryConnection (f (z + s • u + c • v))
        (fderiv ℂ f (z + s • u + c • v)).toLinearMap u := by
  let A (s t : ℝ) := berryConnection (f (z + s • u + t • v))
    (fderiv ℂ f (z + s • u + t • v)).toLinearMap u
  let B (s t : ℝ) := berryConnection (f (z + s • u + t • v))
    (fderiv ℂ f (z + s • u + t • v)).toLinearMap v
  let D (r w : V) (s t : ℝ) := berryDerivativeCandidate (f (z + s • u + t • v))
    (fderiv ℂ f (z + s • u + t • v)).toLinearMap
    (fun e g => fderiv ℂ (fderiv ℂ f) (z + s • u + t • v) e g) r w
  have hmap : Continuous (fun q : ℝ × ℝ => z + q.1 • u + q.2 • v) := by fun_prop
  have hDc (r w : V) : ContinuousOn (D r w).uncurry (Icc a b ×ˢ Icc c d) := by
    intro q hq
    exact ((berryDerivativeCandidate_continuousAt (hf q.1 hq.1 q.2 hq.2)
      (hne q.1 hq.1 q.2 hq.2) r w).comp
        (f := fun q : ℝ × ℝ => z + q.1 • u + q.2 • v) (x := q)
          hmap.continuousAt).continuousWithinAt
  have hAd (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc c d) :
      HasDerivAt (A s) (D v u s t) t :=
    berryConnection_hasDerivAt_affine (z + s • u) v u t (hf s hs t ht) (hne s hs t ht)
  have hBd (t : ℝ) (ht : t ∈ Icc c d) (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun r => B r t) (D u v s t) s := by
    have he (r : ℝ) : z + t • v + r • u = z + r • u + t • v := by abel
    have hfs : ContDiffAt ℂ 2 f (z + t • v + s • u) := by rw [he]; exact hf s hs t ht
    have hns : f (z + t • v + s • u) ≠ 0 := by rw [he]; exact hne s hs t ht
    simpa only [he, B, D] using berryConnection_hasDerivAt_affine (z + t • v) u v s hfs hns
  have he := rectangle_stokes hab hcd (hDc v u) (hDc u v) hAd hBd
  change _ = (∫ t in c..d, B b t - B a t) - ∫ s in a..b, A s d - A s c
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc c d := by simpa [uIcc_of_le hcd] using ht
  exact (berry_curvature_algebra _ (hne s hs' t ht') _ _ u v
    (((hf s hs' t ht').isSymmSndFDerivAt (by norm_num)).eq v u)).symm

end LocalStokes

def gridPoint (n i : ℕ) : ℝ := (i : ℝ) / n

theorem gridPoint_mem_unitInterval (n i : ℕ) (hn : 0 < n) (hi : i ≤ n) :
    OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i ∈ Icc (0 : ℝ) 1 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Nat.cast_nonneg i) hnr.le
  · exact (div_le_one hnr).mpr (by exact_mod_cast hi)

theorem gridPoint_step (n i : ℕ) : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1) - OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i = 1 / (n : ℝ) := by
  simp only [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem gridPoint_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i ≤ OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j :=
  div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg n)

theorem exists_grid_subordinate {ι : Sort*} (U : ι → Set (ℝ × ℝ))
    (hU : ∀ i, IsOpen (U i)) (hcover : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ ⋃ i, U i) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ j < n, ∃ k,
      Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) ×ˢ
        Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)) ⊆ U k := by
  obtain ⟨δ, hδ, hδU⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc) hU hcover
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  let n := N + 1
  have hn : 0 < n := Nat.succ_pos N
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hN
  refine ⟨n, hn, fun i hi j hj => ?_⟩
  obtain ⟨k, hk⟩ := hδU (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i, OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j)
    ⟨gridPoint_mem_unitInterval n i hn hi.le, gridPoint_mem_unitInterval n j hn hj.le⟩
  refine ⟨k, fun q hq => hk ?_⟩
  have hdist (i : ℕ) (s : ℝ) (hs : s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1))) :
      dist s (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have hstep := gridPoint_step n i
    linarith [hs.2]
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨hdist i q.1 hq.1, hdist j q.2 hq.2⟩

theorem grid_boundary_cancel {G : Type*} [CommGroup G] (H V : ℕ → ℕ → G) (n : ℕ)
    (hH : ∀ i < n, H i n = H i 0) (hV : ∀ j < n, V n j = V 0 j) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n,
      H i j * V (i + 1) j / (H i (j + 1) * V i j)) = 1 := by
  have he (i j : ℕ) : H i j * V (i + 1) j / (H i (j + 1) * V i j) =
      (V (i + 1) j / V i j) * (H i j / H i (j + 1)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  simp_rw [he, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i j => V (i + 1) j / V i j)]
  have hv (j : ℕ) : (∏ i ∈ Finset.range n, V (i + 1) j / V i j) = V n j / V 0 j :=
    Finset.prod_range_div (fun i => V i j) n
  have hh (i : ℕ) : (∏ j ∈ Finset.range n, H i j / H i (j + 1)) = H i 0 / H i n :=
    Finset.prod_range_div' (fun j => H i j) n
  simp_rw [hv, hh]
  have hVp : (∏ j ∈ Finset.range n, V n j / V 0 j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [hV j (Finset.mem_range.mp hj)]
    exact div_self' _
  have hHp : (∏ i ∈ Finset.range n, H i 0 / H i n) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [hH i (Finset.mem_range.mp hi)]
    exact div_self' _
  rw [hVp, hHp, one_mul]

theorem rectangle_iterated_integrable {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hF : ContinuousOn F.uncurry (Icc a b ×ˢ Icc c d)) :
    IntervalIntegrable (fun s => ∫ t in c..d, F s t) volume a b := by
  have hi : Integrable F.uncurry ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [intervalIntegral.integral_of_le hcd, Function.uncurry, IntegrableOn] using hi.integral_prod_left

theorem gridCell_subset_unitInterval (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) ⊆ Icc (0 : ℝ) 1 :=
  Icc_subset_Icc (gridPoint_mem_unitInterval n i hn hi.le).1
    (gridPoint_mem_unitInterval n (i + 1) hn (Nat.succ_le_iff.mpr hi)).2

theorem rectangle_integral_grid_sum {F : ℝ → ℝ → ℝ} (n : ℕ) (hn : 0 < n)
    (hF : ContinuousOn F.uncurry (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      ∫ s in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1), ∫ t in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1), F s t) =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F s t := by
  have hmono (i : ℕ) : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i ≤ OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1) := gridPoint_mono n (Nat.le_succ i)
  have hzero : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0 = 0 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint]
  have hone : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n n = 1 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint, hn.ne']
  have hslice (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContinuousOn (F s) (Icc (0 : ℝ) 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  have hint (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) :
      IntervalIntegrable (fun s => ∫ t in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1), F s t)
        volume (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) :=
    rectangle_iterated_integrable (hmono i) (hmono j)
      (hF.mono (Set.prod_mono (gridCell_subset_unitInterval n i hn hi) (gridCell_subset_unitInterval n j hn hj)))
  have hinner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (∑ j ∈ Finset.range n, ∫ t in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1), F s t) =
        ∫ t in (0 : ℝ)..1, F s t := by
    have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n)
      (n := n) (fun j hj => ((hslice s hs).mono (gridCell_subset_unitInterval n j hn hj)).intervalIntegrable_of_Icc (hmono j))
    simpa only [hzero, hone] using he
  calc
    _ = ∑ i ∈ Finset.range n, ∫ s in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1),
        ∑ j ∈ Finset.range n, ∫ t in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1), F s t := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (intervalIntegral.integral_finsetSum (fun j hj => hint i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj))).symm
    _ = ∑ i ∈ Finset.range n, ∫ s in OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i.._root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1), ∫ t in (0 : ℝ)..1, F s t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply intervalIntegral.integral_congr
      intro s hs
      apply hinner
      apply gridCell_subset_unitInterval n i hn (Finset.mem_range.mp hi)
      simpa only [uIcc_of_le (hmono i)] using hs
    _ = _ := by
      have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n) (n := n)
        (fun i hi => rectangle_iterated_integrable (hmono i) (by norm_num : (0 : ℝ) ≤ 1)
          (hF.mono (Set.prod_mono (gridCell_subset_unitInterval n i hn hi) Set.Subset.rfl)))
      simpa only [hzero, hone] using he

theorem complex_prod_range_div (f : ℕ → ℂ) (n : ℕ) (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ i ∈ Finset.range n, f (i + 1) / f i) = f n / f 0 := by
  induction n with
  | zero => simp [hf 0 le_rfl]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hf i (Nat.le_trans hi (Nat.le_succ n)))]
    have hn := hf n (Nat.le_succ n)
    have h0 := hf 0 (Nat.zero_le _)
    field_simp

theorem complex_prod_range_div_rev (f : ℕ → ℂ) (n : ℕ) (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ i ∈ Finset.range n, f i / f (i + 1)) = f 0 / f n := by
  have h := complex_prod_range_div (fun i => (f i)⁻¹) n (fun i hi => inv_ne_zero (hf i hi))
  simpa only [inv_div_inv] using h

theorem complex_grid_boundary_cancel (H V : ℕ → ℕ → ℂ) (n : ℕ)
    (hHn : ∀ i < n, ∀ j ≤ n, H i j ≠ 0) (hVn : ∀ i ≤ n, ∀ j < n, V i j ≠ 0)
    (hH : ∀ i < n, H i n = H i 0) (hV : ∀ j < n, V n j = V 0 j) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n,
      H i j * V (i + 1) j / (H i (j + 1) * V i j)) = 1 := by
  have he (i j : ℕ) : H i j * V (i + 1) j / (H i (j + 1) * V i j) =
      (V (i + 1) j / V i j) * (H i j / H i (j + 1)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [he, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i j => V (i + 1) j / V i j)]
  have hVp : (∏ j ∈ Finset.range n, ∏ i ∈ Finset.range n, V (i + 1) j / V i j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [complex_prod_range_div (fun i => V i j) n (fun i hi => hVn i hi j hj'), hV j hj']
    exact div_self (hVn 0 (Nat.zero_le n) j hj')
  have hHp : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, H i j / H i (j + 1)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [complex_prod_range_div_rev (fun j => H i j) n (hHn i hi'), hH i hi']
    exact div_self (hHn i hi' 0 (Nat.zero_le n))
  rw [hVp, hHp, one_mul]

section ProjectiveGridCover

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*}

/-- A fine rectangular subdivision with a projective chart containing each
closed cell. It records only the finite open-cover data. -/
structure ProjectiveGridCover (p : V → Projectivization ℂ (ι → ℂ)) (z u v : V) (n : ℕ) where
  positive : 0 < n
  chart : ℕ → ℕ → ι
  inPatch : ∀ i < n, ∀ j < n, ∀ s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)),
    ∀ t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (chart i j) (p (z + s • u + t • v))

theorem exists_projectiveGridCover (p : V → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
    (z u v : V) : ∃ n : ℕ, Nonempty (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover p z u v n) := by
  classical
  let U (i : ι) : Set (ℝ × ℝ) := {q | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + q.1 • u + q.2 • v))}
  have hmap : Continuous (fun q : ℝ × ℝ => z + q.1 • u + q.2 • v) := by fun_prop
  have hU (i : ι) : IsOpen (U i) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage (hp.comp hmap)
  have hcover : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ ⋃ i, U i := by
    intro q _
    obtain ⟨i, hi⟩ := AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p (z + q.1 • u + q.2 • v))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨n, hn, hc⟩ := exists_grid_subordinate U hU hcover
  let d := Classical.choose (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p z))
  let C (i j : ℕ) : ι := if hi : i < n then
    if hj : j < n then Classical.choose (hc i hi j hj) else d else d
  refine ⟨n, ⟨{ positive := hn, chart := C, inPatch := ?_ }⟩⟩
  intro i hi j hj s hs t ht
  simp only [C, dite_eq_left hi, dite_eq_left hj]
  exact (Classical.choose_spec (hc i hi j hj))
    (show (s, t) ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) ×ˢ
      Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)) from ⟨hs, ht⟩)

namespace ProjectiveGridCover
variable {p : V → Projectivization ℂ (ι → ℂ)} {z u v : V} {n : ℕ}
  (C : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover p z u v n)

def clamp (_C : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover p z u v n) (j : ℕ) : ℕ := min j (n - 1)

theorem clamp_lt (j : ℕ) : C.clamp j < n := by
  have hn := C.positive
  dsimp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover.clamp]
  omega

theorem gridPoint_mem_clamped_cell (j : ℕ) (hj : j ≤ n) :
    OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (C.clamp j)) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (C.clamp j + 1)) := by
  have hn := C.positive
  constructor
  · apply gridPoint_mono n
    exact Nat.min_le_left _ _
  · apply gridPoint_mono n
    dsimp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover.clamp]
    omega

theorem horizontal_inPatch (i : ℕ) (hi : i < n) (j : ℕ) (hj : j ≤ n)
    (s : ℝ) (hs : s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1))) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart i (C.clamp j)) (p (z + s • u + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v)) :=
  C.inPatch i hi (C.clamp j) (C.clamp_lt j) s hs (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (C.gridPoint_mem_clamped_cell j hj)

theorem vertical_inPatch (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < n)
    (t : ℝ) (ht : t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1))) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart (C.clamp i) j) (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u + t • v)) :=
  C.inPatch (C.clamp i) (C.clamp_lt i) j hj (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i)
    (C.gridPoint_mem_clamped_cell i hi) t ht

end ProjectiveGridCover
end ProjectiveGridCover

section ProjectiveReference

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
variable {ι : Type*}

def projectiveReference (P : Projectivization ℂ (ι → ℂ)) : ι → ℂ :=
  AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates (Classical.choose (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch P)) P

theorem projectiveReference_coordinate_ne_zero (P : Projectivization ℂ (ι → ℂ)) (i : ι)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i P) : projectiveReference P i ≠ 0 :=
  (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero _ i P (Classical.choose_spec (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch P))).mp hi

theorem projectiveReference_factor (P : Projectivization ℂ (ι → ℂ)) (i j : ι)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i P) : projectiveReference P j = projectiveReference P i * AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i P j := by
  let k := Classical.choose (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch P)
  have hk : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch k P := Classical.choose_spec (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch P)
  have hn : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio k i P ≠ 0 := (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero k i P hk).mp hi
  change AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio k j P = AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio k i P * AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j P
  rw [AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula k i j P hk]
  field_simp

def projectiveVertexPhase (P : Projectivization ℂ (ι → ℂ)) (i : ι) : ℂ :=
  complexPhase (projectiveReference P i)

theorem projectiveVertexPhase_ne_zero (P : Projectivization ℂ (ι → ℂ)) (i : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i P) :
    projectiveVertexPhase P i ≠ 0 :=
  complexPhase_ne_zero (projectiveReference_coordinate_ne_zero P i hi)

theorem projectiveVertexPhase_change (P : Projectivization ℂ (ι → ℂ)) (i j : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i P) :
    projectiveVertexPhase P j = projectiveVertexPhase P i * complexPhase (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i P j) := by
  rw [projectiveVertexPhase, projectiveReference_factor P i j hi, complexPhase_mul]
  rfl

end ProjectiveReference

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Fintype ι] (p : V → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p i) z)

def projectiveEdgeTransport (i : ι) (z u : V) (a b : ℝ) : ℂ :=
  connectionTransport (fun t => projectiveBerryConnection p i (z + t • u) u) a b

include hp hhol

omit [FiniteDimensional ℂ V] in
theorem projective_chart_scalar_affine_hasDerivAt (i j : ι) (z u : V) (t : ℝ)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + t • u))) :
    HasDerivAt (fun r : ℝ => projectivePullbackChart p i (z + r • u) j)
      (fderiv ℂ (fun w => projectivePullbackChart p i w j) (z + t • u) u) t := by
  have hd := (differentiableAt_pi.mp
    (projective_chart_differentiableAt p hp _ (hhol _) i hi)) j
  have hline : HasDerivAt (fun r : ℝ => z + r • u) u t := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id t).smul_const u).const_add z)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using
    (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hline

theorem projectiveEdgeTransport_change (i j : ι) (z u : V) {a b : ℝ} (hab : a ≤ b)
    (hi : ∀ t ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + t • u)))
    (hj : ∀ t ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p (z + t • u))) :
    projectiveEdgeTransport p i z u a b = projectiveEdgeTransport p j z u a b *
      complexPhase (projectivePullbackChart p i (z + b • u) j) /
        complexPhase (projectivePullbackChart p i (z + a • u) j) := by
  let g : ℝ → ℂ := fun t => projectivePullbackChart p i (z + t • u) j
  let g' : ℝ → ℂ := fun t => fderiv ℂ (fun w => projectivePullbackChart p i w j) (z + t • u) u
  have hline : Continuous (fun t : ℝ => z + t • u) := by fun_prop
  have hβ : ContinuousOn (fun t => projectiveBerryConnection p j (z + t • u) u) (Icc a b) := by
    intro t ht
    exact ((projectiveBerryConnection_continuousAt p hp hhol j _ u (hj t ht)).comp
      (f := fun r : ℝ => z + r • u) (x := t) hline.continuousAt).continuousWithinAt
  have hgd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g (g' t) t :=
    projective_chart_scalar_affine_hasDerivAt p hp hhol i j z u t (hi t ht)
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hgd t ht).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Icc a b) := by
    intro t ht
    have hs : ContDiffAt ℂ 1 (fun w => projectivePullbackChart p i w j) (z + t • u) :=
      (contDiffAt_pi.mp ((projective_chart_contDiffOn_one p hp hhol i).contDiffAt
        (projective_patch_eventually p hp i _ (hi t ht)))) j
    exact (((hs.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).comp
      (f := fun r : ℝ => z + r • u) (x := t) hline.continuousAt).continuousWithinAt
  have hgn (t : ℝ) (ht : t ∈ Icc a b) : g t ≠ 0 :=
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j _ (hi t ht)).mp (hj t ht)
  apply connectionTransport_change hab (hβ.intervalIntegrable_of_Icc hab) hgc hg'c
    (fun t ht => hgd t ⟨ht.1.le, ht.2.le⟩) hgn
  intro t ht
  exact projectiveBerryConnection_change p hp i j _ u (hi t ht) (hj t ht)
    (projective_chart_differentiableAt p hp _ (hhol _) i (hi t ht))
    (projective_chart_differentiableAt p hp _ (hhol _) j (hj t ht))

omit hp hhol in
def normalizedProjectiveEdgeTransport (i : ι) (z u : V) (a b : ℝ) : ℂ :=
  projectiveEdgeTransport p i z u a b * projectiveVertexPhase (p (z + b • u)) i /
    projectiveVertexPhase (p (z + a • u)) i

omit hp hhol [FiniteDimensional ℂ V] [IsScalarTower ℝ ℂ V] in
theorem normalizedProjectiveEdgeTransport_ne_zero (i : ι) (z u : V) (a b : ℝ)
    (ha : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + a • u))) (hb : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + b • u))) :
    normalizedProjectiveEdgeTransport p i z u a b ≠ 0 :=
  div_ne_zero (mul_ne_zero (connectionTransport_ne_zero _ _ _)
    (projectiveVertexPhase_ne_zero _ i hb)) (projectiveVertexPhase_ne_zero _ i ha)

theorem normalizedProjectiveEdgeTransport_chart_independent (i j : ι) (z u : V) {a b : ℝ}
    (hab : a ≤ b) (hi : ∀ t ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + t • u)))
    (hj : ∀ t ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (p (z + t • u))) :
    normalizedProjectiveEdgeTransport p i z u a b = normalizedProjectiveEdgeTransport p j z u a b := by
  have hia := hi a ⟨le_rfl, hab⟩
  have hib := hi b ⟨hab, le_rfl⟩
  have hva := projectiveVertexPhase_ne_zero _ i hia
  have hga : complexPhase (projectivePullbackChart p i (z + a • u) j) ≠ 0 :=
    complexPhase_ne_zero ((AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j _ hia).mp (hj a ⟨le_rfl, hab⟩))
  unfold normalizedProjectiveEdgeTransport
  rw [projectiveEdgeTransport_change p hp hhol i j z u hab hi hj,
    projectiveVertexPhase_change _ i j hib, projectiveVertexPhase_change _ i j hia]
  change _ = _ * (projectiveVertexPhase (p (z + b • u)) i *
    complexPhase (projectivePullbackChart p i (z + b • u) j)) /
      (projectiveVertexPhase (p (z + a • u)) i * complexPhase (projectivePullbackChart p i (z + a • u) j))
  field_simp

omit [IsScalarTower ℝ ℂ V] in
theorem projectiveBerryConnection_affine_integrable (i : ι) (z u : V) {a b : ℝ}
    (hab : a ≤ b) (hi : ∀ t ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + t • u))) :
    IntervalIntegrable (fun t => projectiveBerryConnection p i (z + t • u) u) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have hline : Continuous (fun r : ℝ => z + r • u) := by fun_prop
  exact ((projectiveBerryConnection_continuousAt p hp hhol i _ u (hi t ht)).comp
    (f := fun r : ℝ => z + r • u) (x := t) hline.continuousAt).continuousWithinAt

omit hp hhol [FiniteDimensional ℂ V] [IsScalarTower ℝ ℂ V] in
theorem normalizedProjectiveEdgeTransport_periodic (l : V) (hl : ∀ w, p (w + l) = p w)
    (i : ι) (z u : V) (a b : ℝ) :
    normalizedProjectiveEdgeTransport p i (z + l) u a b = normalizedProjectiveEdgeTransport p i z u a b := by
  have hx (t : ℝ) : z + l + t • u = (z + t • u) + l := by abel
  have hE : projectiveEdgeTransport p i (z + l) u a b = projectiveEdgeTransport p i z u a b := by
    apply congrArg (fun α => connectionTransport α a b)
    funext t
    rw [hx]
    exact projectiveBerryConnection_periodic p l hl i _ u
  unfold normalizedProjectiveEdgeTransport
  rw [hE, hx, hx, hl, hl]

omit hp hhol in
def projectiveCurvatureRectangle (z u v : V) (a b c d : ℝ) : ℝ :=
  ∫ s in a..b, ∫ t in c..d, (projectiveFubiniStudy p (z + s • u + t • v) u v).im

theorem projectiveCurvatureRectangle_local_stokes (i : ι) (z u v : V) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hi : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + s • u + t • v))) :
    projectiveCurvatureRectangle p z u v a b c d =
      (∫ t in c..d, projectiveBerryConnection p i (z + b • u + t • v) v -
        projectiveBerryConnection p i (z + a • u + t • v) v) -
      ∫ s in a..b, projectiveBerryConnection p i (z + s • u + d • v) u -
        projectiveBerryConnection p i (z + s • u + c • v) u := by
  have hf (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc c d) :
      ContDiffAt ℂ 2 (projectivePullbackChart p i) (z + s • u + t • v) :=
    (projective_chart_contDiffOn_two p hp hhol i).contDiffAt
      (projective_patch_eventually p hp i _ (hi s hs t ht))
  have hn (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc c d) :
      projectivePullbackChart p i (z + s • u + t • v) ≠ 0 :=
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero i _ (hi s hs t ht)
  unfold projectiveBerryConnection projectiveCurvatureRectangle
  rw [← berryConnection_stokes_rectangle (projectivePullbackChart p i) z u v hab hcd hf hn]
  apply intervalIntegral.integral_congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  exact congrArg (fun H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => (H u v).im)
    (projectiveFubiniStudy_eq_chart p hp _ (hhol _) i
      (hi s (by simpa [uIcc_of_le hab] using hs) t (by simpa [uIcc_of_le hcd] using ht)))

theorem projectiveCurvatureRectangle_holonomy (i : ι) (z u v : V) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hi : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + s • u + t • v))) :
    Complex.exp ((2 * Real.pi * projectiveCurvatureRectangle p z u v a b c d : ℝ) * Complex.I) =
      normalizedProjectiveEdgeTransport p i (z + c • v) u a b *
        normalizedProjectiveEdgeTransport p i (z + b • u) v c d /
          (normalizedProjectiveEdgeTransport p i (z + d • v) u a b *
            normalizedProjectiveEdgeTransport p i (z + a • u) v c d) := by
  have he (s t : ℝ) : z + t • v + s • u = z + s • u + t • v := by abel
  have hbottom : ∀ s ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + c • v + s • u)) := by
    intro s hs
    rw [he]
    exact hi s hs c ⟨le_rfl, hcd⟩
  have htop : ∀ s ∈ Icc a b, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p (z + d • v + s • u)) := by
    intro s hs
    rw [he]
    exact hi s hs d ⟨hcd, le_rfl⟩
  have hAb : IntervalIntegrable (fun s => projectiveBerryConnection p i (z + s • u + c • v) u) volume a b := by
    simpa only [he] using projectiveBerryConnection_affine_integrable p hp hhol i (z + c • v) u hab hbottom
  have hAt : IntervalIntegrable (fun s => projectiveBerryConnection p i (z + s • u + d • v) u) volume a b := by
    simpa only [he] using projectiveBerryConnection_affine_integrable p hp hhol i (z + d • v) u hab htop
  have hBl := projectiveBerryConnection_affine_integrable p hp hhol i (z + a • u) v hcd
    (hi a ⟨le_rfl, hab⟩)
  have hBr := projectiveBerryConnection_affine_integrable p hp hhol i (z + b • u) v hcd
    (hi b ⟨hab, le_rfl⟩)
  have hraw : Complex.exp ((2 * Real.pi * projectiveCurvatureRectangle p z u v a b c d : ℝ) * Complex.I) =
      projectiveEdgeTransport p i (z + c • v) u a b * projectiveEdgeTransport p i (z + b • u) v c d /
        (projectiveEdgeTransport p i (z + d • v) u a b * projectiveEdgeTransport p i (z + a • u) v c d) := by
    rw [projectiveCurvatureRectangle_local_stokes p hp hhol i z u v hab hcd hi]
    simpa only [projectiveEdgeTransport, he] using connectionTransport_rectangle
      (A := fun s t => projectiveBerryConnection p i (z + s • u + t • v) u)
      (B := fun s t => projectiveBerryConnection p i (z + s • u + t • v) v)
      (a := a) (b := b) (c := c) (d := d) hAb hAt hBl hBr
  rw [hraw]
  symm
  unfold normalizedProjectiveEdgeTransport
  simp_rw [he]
  exact rectangle_normalization_cancel _ _ _ _ _ _ _ _
    (projectiveVertexPhase_ne_zero _ i (hi a ⟨le_rfl, hab⟩ c ⟨le_rfl, hcd⟩))
    (projectiveVertexPhase_ne_zero _ i (hi b ⟨hab, le_rfl⟩ c ⟨le_rfl, hcd⟩))
    (projectiveVertexPhase_ne_zero _ i (hi a ⟨le_rfl, hab⟩ d ⟨hcd, le_rfl⟩))
    (projectiveVertexPhase_ne_zero _ i (hi b ⟨hab, le_rfl⟩ d ⟨hcd, le_rfl⟩))

end

section
open _root_.MeasureTheory Set Filter _root_.Topology OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

namespace ProjectiveGridCover
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Fintype ι] {p : V → Projectivization ℂ (ι → ℂ)}
  {z u v : V} {n : ℕ} (C : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ProjectiveGridCover p z u v n)

def horizontalTransport (i j : ℕ) : ℂ :=
  normalizedProjectiveEdgeTransport p (C.chart i (C.clamp j)) (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v) u
    (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1))

def verticalTransport (i j : ℕ) : ℂ :=
  normalizedProjectiveEdgeTransport p (C.chart (C.clamp i) j) (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u) v
    (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1))

omit [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem horizontalTransport_ne_zero (i : ℕ) (hi : i < n) (j : ℕ) (hj : j ≤ n) :
    C.horizontalTransport i j ≠ 0 := by
  have hm := gridPoint_mono n (Nat.le_succ i)
  apply normalizedProjectiveEdgeTransport_ne_zero
  · have he : z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u = z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v := by abel
    rw [he]
    exact C.horizontal_inPatch i hi j hj _ ⟨le_rfl, hm⟩
  · have he : z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1) • u =
        z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1) • u + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v := by abel
    rw [he]
    exact C.horizontal_inPatch i hi j hj _ ⟨hm, le_rfl⟩

omit [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem verticalTransport_ne_zero (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < n) :
    C.verticalTransport i j ≠ 0 := by
  have hm := gridPoint_mono n (Nat.le_succ j)
  exact normalizedProjectiveEdgeTransport_ne_zero p _ _ _ _ _
    (C.vertical_inPatch i hi j hj _ ⟨le_rfl, hm⟩)
    (C.vertical_inPatch i hi j hj _ ⟨hm, le_rfl⟩)

variable (hp : Continuous p)
  (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p i) z)
include hp hhol

theorem horizontalTransport_eq_of_inPatch (i : ℕ) (hi : i < n) (j : ℕ) (hj : j ≤ n) (k : ι)
    (hk : ∀ s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch k (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v + s • u))) :
    C.horizontalTransport i j = normalizedProjectiveEdgeTransport p k (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v) u
      (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) := by
  apply normalizedProjectiveEdgeTransport_chart_independent p hp hhol _ k _ _
    (gridPoint_mono n (Nat.le_succ i)) _ hk
  intro s hs
  have he : z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v + s • u = z + s • u + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j • v := by abel
  rw [he]
  exact C.horizontal_inPatch i hi j hj s hs

theorem verticalTransport_eq_of_inPatch (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < n) (k : ι)
    (hk : ∀ t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch k (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u + t • v))) :
    C.verticalTransport i j = normalizedProjectiveEdgeTransport p k (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i • u) v
      (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)) :=
  normalizedProjectiveEdgeTransport_chart_independent p hp hhol _ k _ _
    (gridPoint_mono n (Nat.le_succ j)) (C.vertical_inPatch i hi j hj) hk

theorem cell_holonomy (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) :
    Complex.exp ((2 * Real.pi * projectiveCurvatureRectangle p z u v
      (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)) : ℝ) * Complex.I) =
      C.horizontalTransport i j * C.verticalTransport (i + 1) j /
        (C.horizontalTransport i (j + 1) * C.verticalTransport i j) := by
  have him := gridPoint_mono n (Nat.le_succ i)
  have hjm := gridPoint_mono n (Nat.le_succ j)
  have hph (t : ℝ) (ht : t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1))) :
      ∀ s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)), AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart i j) (p (z + t • v + s • u)) := by
    intro s hs
    have he : z + t • v + s • u = z + s • u + t • v := by abel
    rw [he]
    exact C.inPatch i hi j hj s hs t ht
  rw [C.horizontalTransport_eq_of_inPatch hp hhol i hi j hj.le (C.chart i j) (hph _ ⟨le_rfl, hjm⟩),
    C.horizontalTransport_eq_of_inPatch hp hhol i hi (j + 1) (Nat.succ_le_iff.mpr hj)
      (C.chart i j) (hph _ ⟨hjm, le_rfl⟩),
    C.verticalTransport_eq_of_inPatch hp hhol (i + 1) (Nat.succ_le_iff.mpr hi) j hj
      (C.chart i j) (C.inPatch i hi j hj _ ⟨him, le_rfl⟩),
    C.verticalTransport_eq_of_inPatch hp hhol i hi.le j hj
      (C.chart i j) (C.inPatch i hi j hj _ ⟨le_rfl, him⟩)]
  exact projectiveCurvatureRectangle_holonomy p hp hhol (C.chart i j) z u v him hjm (C.inPatch i hi j hj)

theorem horizontalTransport_periodic (hv : ∀ w, p (w + v) = p w) (i : ℕ) (hi : i < n) :
    C.horizontalTransport i n = C.horizontalTransport i 0 := by
  have hzero : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0 = 0 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint]
  have hone : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n n = 1 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint, C.positive.ne']
  have hbase (s : ℝ) (hs : s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1))) :
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart i 0) (p (z + s • u)) := by
    have hm := gridPoint_mono n (Nat.zero_le 1)
    have h := C.inPatch i hi 0 C.positive s hs (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0) ⟨le_rfl, hm⟩
    simpa only [hzero, zero_smul, add_zero] using h
  have hb : ∀ s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart i 0) (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0 • v + s • u)) := by
    simpa only [hzero, zero_smul, add_zero] using hbase
  have ht : ∀ s ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart i 0) (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n n • v + s • u)) := by
    intro s hs
    rw [hone, one_smul, show z + v + s • u = (z + s • u) + v by abel, hv]
    exact hbase s hs
  rw [C.horizontalTransport_eq_of_inPatch hp hhol i hi n le_rfl (C.chart i 0) ht,
    C.horizontalTransport_eq_of_inPatch hp hhol i hi 0 (Nat.zero_le n) (C.chart i 0) hb]
  simp only [hzero, hone, zero_smul, one_smul, add_zero]
  exact normalizedProjectiveEdgeTransport_periodic p v hv _ z u _ _

theorem verticalTransport_periodic (hu : ∀ w, p (w + u) = p w) (j : ℕ) (hj : j < n) :
    C.verticalTransport n j = C.verticalTransport 0 j := by
  have hzero : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0 = 0 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint]
  have hone : OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n n = 1 := by simp [OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint, C.positive.ne']
  have hbase (t : ℝ) (ht : t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1))) :
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart 0 j) (p (z + t • v)) := by
    have hm := gridPoint_mono n (Nat.zero_le 1)
    have h := C.inPatch 0 C.positive j hj (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0) ⟨le_rfl, hm⟩ t ht
    simpa only [hzero, zero_smul, add_zero] using h
  have hl : ∀ t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart 0 j) (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n 0 • u + t • v)) := by
    simpa only [hzero, zero_smul, add_zero] using hbase
  have hr : ∀ t ∈ Icc (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (C.chart 0 j) (p (z + OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n n • u + t • v)) := by
    intro t ht
    rw [hone, one_smul, show z + u + t • v = (z + t • v) + u by abel, hu]
    exact hbase t ht
  rw [C.verticalTransport_eq_of_inPatch hp hhol n le_rfl j hj (C.chart 0 j) hr,
    C.verticalTransport_eq_of_inPatch hp hhol 0 (Nat.zero_le n) j hj (C.chart 0 j) hl]
  simp only [hzero, hone, zero_smul, one_smul, add_zero]
  exact normalizedProjectiveEdgeTransport_periodic p u hu _ z v _ _

end ProjectiveGridCover

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Fintype ι] (p : V → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ z, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p z) ∧ DifferentiableAt ℂ (projectivePullbackChart p i) z)

include hp hhol

theorem projectiveCurvatureRectangle_exp_eq_one (z u v : V)
    (hu : ∀ w, p (w + u) = p w) (hv : ∀ w, p (w + v) = p w) :
    Complex.exp ((2 * Real.pi * projectiveCurvatureRectangle p z u v 0 1 0 1 : ℝ) * Complex.I) = 1 := by
  obtain ⟨n, ⟨C⟩⟩ := exists_projectiveGridCover p hp z u v
  let R (i j : ℕ) := projectiveCurvatureRectangle p z u v
    (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n i) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (i + 1)) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n j) (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.gridPoint n (j + 1))
  have hprod : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n,
      Complex.exp ((2 * Real.pi * R i j : ℝ) * Complex.I)) = 1 := by
    calc
      _ = ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n,
          C.horizontalTransport i j * C.verticalTransport (i + 1) j /
            (C.horizontalTransport i (j + 1) * C.verticalTransport i j) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro j hj
        exact C.cell_holonomy hp hhol i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      _ = 1 := complex_grid_boundary_cancel C.horizontalTransport C.verticalTransport n
        C.horizontalTransport_ne_zero C.verticalTransport_ne_zero
        (C.horizontalTransport_periodic hp hhol hv) (C.verticalTransport_periodic hp hhol hu)
  have hmap : Continuous (fun q : ℝ × ℝ => z + q.1 • u + q.2 • v) := by fun_prop
  have hc : Continuous (fun q : ℝ × ℝ => (projectiveFubiniStudy p (z + q.1 • u + q.2 • v) u v).im) :=
    Complex.continuous_im.comp ((projectiveFubiniStudy_continuous p hp hhol u v).comp hmap)
  have hsum : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, R i j) =
      projectiveCurvatureRectangle p z u v 0 1 0 1 := by
    exact rectangle_integral_grid_sum n C.positive hc.continuousOn
  have hexp : Complex.exp ((2 * Real.pi * (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, R i j) : ℝ) * Complex.I) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, Complex.exp ((2 * Real.pi * R i j : ℝ) * Complex.I) := by
    simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [← hsum, hexp, hprod]

/-- Every lattice parallelogram has an integer period of the pulled-back
normalized projective curvature. The proof uses local Stokes and edge cancellation. -/
theorem projectiveCurvatureRectangle_integral (z u v : V)
    (hu : ∀ w, p (w + u) = p w) (hv : ∀ w, p (w + v) = p w) :
    ∃ m : ℤ, projectiveCurvatureRectangle p z u v 0 1 0 1 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (projectiveCurvatureRectangle_exp_eq_one p hp hhol z u v hu hv)
  refine ⟨m, ?_⟩
  have him := congrArg Complex.im hm
  have h2r : (2 : ℂ).re = 2 := rfl
  have h2i : (2 : ℂ).im = 0 := rfl
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, mul_one, add_zero, sub_zero, h2r, h2i] at him
  nlinarith [Real.pi_pos]

end

section
open _root_.MeasureTheory Set Filter _root_.Topology

theorem continuous_integer_valued_constant {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] [Nonempty T] {P : T → ℝ} (hP : Continuous P)
    (hInt : ∀ q, ∃ m : ℤ, P q = (m : ℝ)) : ∃ m : ℤ, ∀ q, P q = (m : ℝ) := by
  choose m hm using hInt
  have hmc : Continuous m := Real.isClosedEmbedding_intCast.isEmbedding.isInducing.continuous_iff.mpr (by
    change Continuous (fun q => (m q : ℝ))
    exact hP.congr hm)
  let q₀ : T := Classical.arbitrary T
  refine ⟨m q₀, fun q => ?_⟩
  rw [hm q, (inferInstance : PreconnectedSpace T).constant hmc (x := q) (y := q₀)]

theorem integral_intervalIntegral_swap_compact {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [IsFiniteMeasure μ] {g : T → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : Continuous g.uncurry) :
    (∫ q, (∫ t in a..b, g q t) ∂μ) = ∫ t in a..b, ∫ q, g q t ∂μ := by
  have hi₀ : IntegrableOn g.uncurry (univ ×ˢ Icc a b) (μ.prod volume) :=
    hg.continuousOn.integrableOn_compact (isCompact_univ.prod isCompact_Icc)
  have hi : Integrable g.uncurry (μ.prod (volume.restrict (Ioc a b))) := by
    have hi₁ := hi₀.mono_set (Set.prod_mono Set.Subset.rfl Ioc_subset_Icc_self)
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hi₁
  simpa only [intervalIntegral.integral_of_le hab] using integral_integral_swap hi

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
  [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
  (μ : Measure T) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
  (k : T → ℝ) (hk : Continuous k) (A B : ℝ → T) (hA : Continuous A) (hB : Continuous B)

def translatedRectangleAverage (q : T) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, k (A s + B t + q)

include hk hA hB

omit [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T] in
theorem translatedRectangleAverage_continuous : Continuous (translatedRectangleAverage k A B) := by
  have h1 : Continuous (fun r : (T × ℝ) × ℝ => k (A r.1.2 + B r.2 + r.1.1)) := by fun_prop
  have h2 : Continuous (fun q : T × ℝ => ∫ t in (0 : ℝ)..1, k (A q.2 + B t + q.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h1 _ _
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h2 _ _

theorem integral_translatedRectangleAverage :
    (∫ q, translatedRectangleAverage k A B q ∂μ) = ∫ q, k q ∂μ := by
  have h1 : Continuous (fun r : (T × ℝ) × ℝ => k (A r.1.2 + B r.2 + r.1.1)) := by fun_prop
  have h2 : Continuous (fun q : T × ℝ => ∫ t in (0 : ℝ)..1, k (A q.2 + B t + q.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h1 _ _
  have h3 (s : ℝ) : Continuous (fun q : T × ℝ => k (A s + B q.2 + q.1)) := by fun_prop
  unfold translatedRectangleAverage
  rw [integral_intervalIntegral_swap_compact μ
    (g := fun q s => ∫ t in (0 : ℝ)..1, k (A s + B t + q)) (by norm_num : (0 : ℝ) ≤ 1) h2]
  calc
    _ = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ∫ q, k (A s + B t + q) ∂μ := by
      apply intervalIntegral.integral_congr
      intro s _
      exact integral_intervalIntegral_swap_compact μ (by norm_num) (h3 s)
    _ = _ := by
      simp_rw [integral_add_left_eq_self (μ := μ) k]
      simp

theorem integral_integer_of_translatedRectangleAverage [PreconnectedSpace T]
    (hInt : ∀ q, ∃ m : ℤ, translatedRectangleAverage k A B q = (m : ℝ)) :
    ∃ m : ℤ, (∫ q, k q ∂μ) = (m : ℝ) := by
  obtain ⟨m, hm⟩ := continuous_integer_valued_constant
    (translatedRectangleAverage_continuous k hk A B hA hB) hInt
  refine ⟨m, ?_⟩
  rw [← integral_translatedRectangleAverage μ k hk A B hA hB]
  simp_rw [hm]
  simp

end

open _root_.MeasureTheory OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

section IntegralAverage
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)]
  [MeasurableSpace (V ⧸ Λ)] [BorelSpace (V ⧸ Λ)] {ι : Type*} [Fintype ι]
  (f : V ⧸ Λ → Projectivization ℂ (ι → ℂ)) (hf : Continuous f)
  (hhol : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
    DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

theorem averagedProjectiveForm_integral (u : V) (hu : u ∈ Λ) (v : V) (hv : v ∈ Λ) :
    ∃ m : ℤ, (averagedProjectiveForm Λ f hf hhol u v).im = (m : ℝ) := by
  let : ConnectedSpace (V ⧸ Λ) :=
    (QuotientAddGroup.mk_surjective : Function.Surjective (QuotientAddGroup.mk : V → V ⧸ Λ)).connectedSpace
      QuotientAddGroup.continuous_mk
  let k : V ⧸ Λ → ℝ := fun q => (torusFubiniStudy Λ f q u v).im
  let A : ℝ → V ⧸ Λ := fun s => QuotientAddGroup.mk (s • u)
  let B : ℝ → V ⧸ Λ := fun t => QuotientAddGroup.mk (t • v)
  have hk : Continuous k := Complex.continuous_im.comp (torusFubiniStudy_continuous Λ f hf hhol u v)
  have hA : Continuous A := QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const)
  have hB : Continuous B := QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const)
  let p : V → Projectivization ℂ (ι → ℂ) := fun w => f (QuotientAddGroup.mk w)
  have hp : Continuous p := hf.comp QuotientAddGroup.continuous_mk
  have hpu (w : V) : p (w + u) = p w := by
    apply congrArg f
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [add_sub_cancel_left] using hu
  have hpv (w : V) : p (w + v) = p w := by
    apply congrArg f
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [add_sub_cancel_left] using hv
  have hInt (q : V ⧸ Λ) : ∃ m : ℤ, translatedRectangleAverage k A B q = (m : ℝ) := by
    let z := Quotient.out q
    obtain ⟨m, hm⟩ := projectiveCurvatureRectangle_integral p hp hhol z u v hpu hpv
    refine ⟨m, ?_⟩
    have he : translatedRectangleAverage k A B q = projectiveCurvatureRectangle p z u v 0 1 0 1 := by
      apply intervalIntegral.integral_congr
      intro s _
      apply intervalIntegral.integral_congr
      intro t _
      have hq : A s + B t + q = (QuotientAddGroup.mk (z + s • u + t • v) : V ⧸ Λ) := by
        have hout : (QuotientAddGroup.mk z : V ⧸ Λ) = q := Quotient.out_eq q
        calc
          _ = QuotientAddGroup.mk (s • u + t • v + z) := by rw [← hout]; rfl
          _ = _ := congrArg QuotientAddGroup.mk (by abel)
      change (torusFubiniStudy Λ f (A s + B t + q) u v).im =
        (projectiveFubiniStudy p (z + s • u + t • v) u v).im
      rw [hq]
      exact congrArg (fun H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => (H u v).im)
        (torusFubiniStudy_lift Λ f hf hhol _)
    exact he.trans hm
  obtain ⟨m, hm⟩ := integral_integer_of_translatedRectangleAverage
    (normalizedAddHaar (V ⧸ Λ)) k hk A B hA hB hInt
  refine ⟨m, ?_⟩
  rw [averagedProjectiveForm_apply]
  have him : (∫ q, torusFubiniStudy Λ f q u v ∂ normalizedAddHaar (V ⧸ Λ)).im =
      ∫ q, k q ∂ normalizedAddHaar (V ⧸ Λ) :=
    (integral_im (torusFubiniStudy_integrable Λ f hf hhol u v)).symm
  exact him.trans hm

end IntegralAverage

/-- A closed holomorphic projective immersion yields the positive integral
Hermitian form required in RiemannProjectivity, by averaging its projective curvature. -/
theorem positive_integral_hermitian_of_projective_embedding
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)]
    (n : ℕ) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Topology.IsClosedEmbedding f)
    (himm : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)) :
    ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      (∀ u v : V, H v u = star (H u v)) ∧
      (∀ u : V, u ≠ 0 → 0 < (H u u).re) ∧
      (∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) := by
  let : NormedSpace ℝ V := NormedSpace.complexToReal
  let : IsScalarTower ℝ ℂ V := inferInstance
  borelize (V ⧸ Λ)
  have hhol : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z := by
    intro z
    obtain ⟨i, hi, hd, _⟩ := himm z
    exact ⟨i, hi, hd⟩
  refine ⟨averagedProjectiveForm Λ f hf.continuous hhol,
    averagedProjectiveForm_symm Λ f hf.continuous hhol,
    averagedProjectiveForm_positive Λ f hf.continuous hhol himm, ?_⟩
  exact averagedProjectiveForm_integral Λ f hf.continuous hhol

end Construction

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Existence of a closed holomorphic embedding of `V / Λ`
into finite-dimensional complex projective space. -/
def IsProjectiveComplexTorus (Λ : AddSubgroup V) : Prop :=
  ∃ (n : ℕ) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ)),
    Topology.IsClosedEmbedding f ∧
    ∀ z : V, ∃ i : Fin (n + 1),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

/-- The Riemann projectivity criterion, with precisely the hypotheses and
conclusion of the committed RiemannProjectivity specification. -/
theorem riemann_projectivity_criterion [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)] :
    IsProjectiveComplexTorus V Λ ↔
      ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
        (∀ u v : V, H v u = star (H u v)) ∧
        (∀ u : V, u ≠ 0 → 0 < (H u u).re) ∧
        (∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ)) := by
  constructor
  · rintro ⟨n, f, hf, himm⟩
    exact OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.positive_integral_hermitian_of_projective_embedding Λ n f hf himm
  · rintro ⟨H, hsym, hpos, hint⟩
    exact OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projective_embedding_of_positive_integral_hermitian H Λ hsym hpos hint

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion
