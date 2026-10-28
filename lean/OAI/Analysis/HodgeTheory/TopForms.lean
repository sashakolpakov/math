import OAI.Analysis.HodgeTheory.Pure
import OAI.Analysis.HodgeTheory.Integration
import OAI.Analysis.HodgeTheory.Wedge
import OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Top Forms -/

namespace OAI.Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing

noncomputable section

/-!
PolarizedPairing: integration of canonical-bundle pairings.

For pure `(n,0)` and `(0,n)` forms, write their chart expressions as
`a dz₁ ∧... ∧ dzₙ` and `b dbar(z₁) ∧... ∧ dbar(zₙ)`. Their wedge has
coefficient `i^(-n²) 2^n a b` in the complex-oriented real volume.
We integrate these coefficients using a finite subordinate partition of
unity and ordinary Lebesgue measure on `ℂ^n`. This implements the missing
pairing only on these pure types; it is not a general differential-form
wedge API. The pure-type reconstruction is proved in `Pure`.
-/

open scoped _root_.Manifold ContDiff _root_.Topology BigOperators
open Set Function Filter _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {n : ℕ}

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E

/-- A chart's contribution to the canonical-bundle integral. -/
def topPairingIntegrand (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (α β : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) : (Fin n → ℂ) → ℂ :=
  Integration.Constructions.PolarizedPairing.chartCutoff (chartAt E i.val) (D.partition i)
    (fun y => Wedge.Constructions.PolarizedPairing.topWedgeCoefficient (n := n)
      (α.val.inChart (chartAt E i.val) y b)
      (β.val.inChart (chartAt E i.val) y b)) ∘ b.equivFun.symm

/-- Integral of the pure `(n,0)`--`(0,n)` wedge pairing, defined in charts. -/
def topPairingWith (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (α β : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) : ℂ :=
  ∑ i : D.centers, ∫ y, topPairingIntegrand D b α β i y

/-- The real chart density obtained when the second form is the conjugate. -/
def topNormDensity (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) : (Fin n → ℂ) → ℝ :=
  Integration.Constructions.PolarizedPairing.chartCutoff (chartAt E i.val) (D.partition i)
    (fun y => Complex.normSq (form.val.inChart (chartAt E i.val) y b)) ∘ b.equivFun.symm

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem chartCoefficient_continuousOn (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (b : Module.Basis (Fin n) ℂ E) (x : M) :
    ContinuousOn (fun y => form.val.inChart (chartAt E x) y b) (chartAt E x).target := by
  have hc : ContinuousOn (form.val.inChart (chartAt E x)) (chartAt E x).target := by
    simpa [DifferentialForms.Manifold.Algebra.manifoldFormChartDomain] using
      (form.smooth (chartAt E x) (chart_mem_atlas E x)).continuousOn
  exact (continuous_eval_const (b : Fin n → E)).comp_continuousOn hc

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
theorem topNormDensity_continuous (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) :
    Continuous (topNormDensity D b form i) := by
  apply (Integration.Constructions.PolarizedPairing.chartCutoff_continuous (chartAt E i.val) (D.partition i)
    (D.partition i).contMDiff.continuous (D.subordinate i) _
    (Complex.continuous_normSq.comp_continuousOn
      (chartCoefficient_continuousOn form b i.val))).comp
  exact b.equivFun.symm.continuous_of_finiteDimensional

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
theorem topNormDensity_hasCompactSupport (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) :
    HasCompactSupport (topNormDensity D b form i) :=
  (Integration.Constructions.PolarizedPairing.chartCutoff_hasCompactSupport (chartAt E i.val) (D.partition i)
    (D.subordinate i) _).comp_isClosedEmbedding
      b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem topNormDensity_nonneg (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) (y : Fin n → ℂ) :
    0 ≤ topNormDensity D b form i y := by
  dsimp [topNormDensity, Integration.Constructions.PolarizedPairing.chartCutoff]
  simp only [Set.indicator]
  split_ifs
  · exact mul_nonneg (D.partition.nonneg i _) (Complex.normSq_nonneg _)
  · exact le_rfl

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem topPairingIntegrand_conjugate (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (i : D.centers) (y : Fin n → ℂ) :
    topPairingIntegrand D b form (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form) i y =
      (Complex.I ^ (n * n))⁻¹ * (2 : ℂ) ^ n * (topNormDensity D b form i y : ℂ) := by
  classical
  dsimp [topPairingIntegrand, topNormDensity, Integration.Constructions.PolarizedPairing.chartCutoff]
  simp only [Set.indicator]
  split_ifs with hy
  · have hc : (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form).val.inChart (chartAt E i.val)
        (b.equivFun.symm y) b =
        star (form.val.inChart (chartAt E i.val) (b.equivFun.symm y) b) := rfl
    rw [hc]
    simp only [Wedge.Constructions.PolarizedPairing.topWedgeCoefficient_eq, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_mul]
    ring
  · simp

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem topPairingWith_conjugate (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Complex.I ^ (n * n) * topPairingWith D b form (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form) =
      ((2 : ℝ) ^ n * ∑ i : D.centers, ∫ y, topNormDensity D b form i y : ℝ) := by
  classical
  simp only [topPairingWith]
  simp_rw [topPairingIntegrand_conjugate]
  simp only [integral_const_mul, integral_complex_ofReal]
  rw [← Finset.mul_sum]
  have hi : Complex.I ^ (n * n) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hi, one_mul]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_sum]

omit [FiniteDimensional ℂ E] [T2Space M] [CompactSpace M] in
theorem topNormDensity_some_positive (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (htype : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 form.val) (hne : form ≠ 0) :
    ∃ (i : D.centers) (y : Fin n → ℂ), 0 < topNormDensity D b form i y := by
  classical
  have hx : ∃ x : M, form x ≠ 0 := by
    by_contra! h
    apply hne
    apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    exact h
  obtain ⟨x, hx⟩ := hx
  obtain ⟨i, hi⟩ := D.partition.exists_pos_of_mem (mem_univ x)
  have hxs : x ∈ (chartAt E i.val).source :=
    D.subordinate i (subset_tsupport _ (ne_of_gt hi))
  have hyt : (chartAt E i.val) x ∈ (chartAt E i.val).target :=
    (chartAt E i.val).map_source hxs
  have hlocal : form.val.inChart (chartAt E i.val) ((chartAt E i.val) x) ≠ 0 := by
    intro hz
    apply hx
    ext v
    have he := congrArg (fun f : E [⋀^Fin n]→L[ℝ] ℂ =>
      f (fun j => DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (chartAt E i.val) (chart_mem_atlas E i.val) x hxs (v j))) hz
    rw [form.val.inChart_at (chartAt E i.val) (chart_mem_atlas E i.val) x hxs] at he
    simp only [ContinuousLinearEquiv.symm_apply_apply] at he
    convert he using 1
  have hb := Pure.Constructions.PolarizedPairing.pure_basis_value_ne_zero _
    (htype (chartAt E i.val) (chart_mem_atlas E i.val) _ hyt) b hlocal
  refine ⟨i, b.equivFun ((chartAt E i.val) x), ?_⟩
  simpa only [topNormDensity, Function.comp_apply, LinearEquiv.symm_apply_apply,
    Integration.Constructions.PolarizedPairing.chartCutoff, Set.indicator_of_mem hyt, (chartAt E i.val).left_inv hxs, smul_eq_mul]
    using mul_pos hi (Complex.normSq_pos.mpr hb)

omit [FiniteDimensional ℂ E] [T2Space M] in
theorem topNormDensity_integral_sum_pos (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (htype : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 form.val) (hne : form ≠ 0) :
    0 < ∑ i : D.centers, ∫ y, topNormDensity D b form i y := by
  classical
  obtain ⟨i, y, hy⟩ := topNormDensity_some_positive D b form htype hne
  apply (Finset.sum_pos_iff_of_nonneg
    (fun j _ => integral_nonneg (topNormDensity_nonneg D b form j))).mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact (topNormDensity_continuous D b form i).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (topNormDensity_hasCompactSupport D b form i) (topNormDensity_nonneg D b form i)
    (ne_of_gt hy)

omit [FiniteDimensional ℂ E] [T2Space M] in
/-- Strict positivity is proved for every finite subordinate chart partition. -/
theorem topPairingWith_positive (D : Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (htype : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 form.val) (hne : form ≠ 0) :
    let z := topPairingWith D b form (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form)
    (Complex.I ^ (n * n) * z).im = 0 ∧
      0 < (Complex.I ^ (n * n) * z).re ∧ z ≠ 0 := by
  dsimp only
  have hp : 0 < (2 : ℝ) ^ n * ∑ i : D.centers, ∫ y, topNormDensity D b form i y :=
    mul_pos (pow_pos (by norm_num) n) (topNormDensity_integral_sum_pos D b form htype hne)
  have he := topPairingWith_conjugate D b form
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    rfl
  · rw [he]
    exact hp
  · intro hz
    rw [hz, mul_zero] at he
    have hr := congrArg Complex.re he
    exact (ne_of_gt hp) hr.symm

/-- A fixed coordinate construction of the canonical-bundle pairing.
The left and right arguments are used at types `(n,0)` and `(0,n)`;
the positivity theorem below supplies the former and conjugates it for
the latter. -/
def complexOrientedTopPairing (hdim : Module.finrank ℂ E = n)
    (α β : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) : ℂ :=
  topPairingWith (Integration.Constructions.PolarizedPairing.canonicalChartPartition E M)
    ((Module.finBasis ℂ E).reindex (finCongr hdim)) α β

end

end OAI.Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing
