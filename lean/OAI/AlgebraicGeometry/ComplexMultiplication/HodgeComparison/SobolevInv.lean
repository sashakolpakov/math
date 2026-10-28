import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy

/-! # Sobolev Inv -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction

noncomputable section

section

/-! Weak Dirichlet solvability on the actual completed Sobolev space of a compact domain. -/

open _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def supportedH1Gradient (b : OrthonormalBasis ι ℝ E) (K : Set E) :
    SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℂ] PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)) :=
  (FourierEnergy.CM.Construction.sobolevNormalizedGradient b).comp (SobolevIs.CM.Construction.supportedH1Coordinates K).subtypeL

/-- The genuine completed-space energy problem is uniquely solvable on a compact domain. -/
theorem dirichlet_functional_weak_existsUnique [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (hK : IsCompact K) (ℓ : SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℂ] ℂ) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      inner ℂ (supportedH1Gradient b K u) (supportedH1Gradient b K v) = ℓ v := by
  apply CompactEnergy.CM.Construction.graphEnergy_weak_existsUnique (SobolevIs.CM.Construction.supportedH1Embedding K) (supportedH1Gradient b K)
    (SobolevIs.CM.Construction.supportedH1Embedding_isCompact hK)
    ((FourierEnergy.CM.Construction.sobolevNormalizedGradient_injective b).comp Subtype.val_injective)
  intro u v
  exact FourierEnergy.CM.Construction.sobolev_graph_inner b u.val v.val

/-- In particular every L² forcing term has a unique weak solution of the normalized Poisson
equation. The gradient here is the ordinary gradient divided by 2π, up to a unit complex factor. -/
theorem dirichlet_l2_weak_existsUnique [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (hK : IsCompact K) (f : Lp ℂ 2 (volume : Measure E)) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      inner ℂ (supportedH1Gradient b K u) (supportedH1Gradient b K v) =
        inner ℂ f (SobolevIs.CM.Construction.supportedH1Embedding K v) :=
  dirichlet_functional_weak_existsUnique b hK ((innerSL ℂ f).comp (SobolevIs.CM.Construction.supportedH1Embedding K))

/-- The unnormalized weak Poisson equation, expressed through actual distributional derivatives. -/
theorem dirichlet_poisson_weak_existsUnique [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (hK : IsCompact K) (f : Lp ℂ 2 (volume : Measure E)) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      ∑ i, inner ℂ (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u.val) (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) v.val) =
        inner ℂ f (SobolevIs.CM.Construction.supportedH1Embedding K v) := by
  let a : ℂ := (((2 * Real.pi) ^ 2 : ℝ) : ℂ)
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let ℓ : SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℂ] ℂ := (innerSL ℂ f).comp (SobolevIs.CM.Construction.supportedH1Embedding K)
  obtain ⟨u, hu, huniq⟩ := dirichlet_functional_weak_existsUnique b hK (a⁻¹ • ℓ)
  refine ⟨u, ?_, ?_⟩
  · intro v
    rw [FourierEnergy.CM.Construction.sobolev_derivative_energy]
    change a * inner ℂ (supportedH1Gradient b K u) (supportedH1Gradient b K v) = ℓ v
    rw [hu]
    change a * (a⁻¹ * ℓ v) = ℓ v
    rw [mul_inv_cancel_left₀ ha]
  · intro u' hu'
    apply huniq
    intro v
    apply mul_left_cancel₀ ha
    change a * inner ℂ (supportedH1Gradient b K u') (supportedH1Gradient b K v) =
      a * (a⁻¹ * ℓ v)
    rw [mul_inv_cancel_left₀ ha]
    exact (FourierEnergy.CM.Construction.sobolev_derivative_energy b u'.val v.val).symm.trans (hu' v)

end

section

/-! Weak-derivative characterizations and multiplication by smooth cutoff functions. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memSobolev_finset_sum {ι : Type*} (S : Finset ι) {s : ℝ} {f : ι → 𝓢'(E, F)}
    (hf : ∀ i ∈ S, MemSobolev s 2 (f i)) : MemSobolev s 2 (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero E F s 2
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- One additional Sobolev order is equivalent to controlling all first weak derivatives. -/
theorem memSobolev_succ_iff_derivatives {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (s : ℝ) (u : 𝓢'(E, F)) :
    MemSobolev (s + 1) 2 u ↔ MemSobolev s 2 u ∧ ∀ i, MemSobolev s 2 (∂_{b i} u) := by
  constructor
  · intro hu
    refine ⟨hu.mono (by linarith), ?_⟩
    intro i
    have h := hu.lineDerivOp (m := b i)
    simpa only [add_sub_cancel_right] using h
  · rintro ⟨hu, hd⟩
    have hΔ : MemSobolev (s - 1) 2 (Δ u) := by
      rw [TemperedDistribution.laplacian_eq_sum b]
      exact memSobolev_finset_sum Finset.univ (fun i _ => (hd i).lineDerivOp)
    have h := EllipticLocal.CM.Construction.laplacian_sobolev_regularity (hu.mono (by linarith : s - 1 ≤ s)) hΔ
    rwa [show s - 1 + 2 = s + 1 by ring] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartz_cutoff_leibniz (g φ : 𝓢(E, ℂ)) (m : E) :
    ∂_{m} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{m} g : 𝓢(E, ℂ)) φ +
        SchwartzMap.smulLeftCLM ℂ g (∂_{m} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{m} g : 𝓢(E, ℂ)).hasTemperateGrowth]
  rw [SchwartzMap.smulLeftCLM_apply g.hasTemperateGrowth,
    fderiv_fun_smul g.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Leibniz's rule for actual distributional multiplication by a Schwartz cutoff. -/
theorem distribution_cutoff_leibniz (g : 𝓢(E, ℂ)) (m : E) (u : 𝓢'(E, F)) :
    ∂_{m} (smulLeftCLM F g u) =
      smulLeftCLM F (∂_{m} g : 𝓢(E, ℂ)) u + smulLeftCLM F g (∂_{m} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply, add_apply, map_neg,
    schwartz_cutoff_leibniz, map_add]
  abel

theorem memSobolev_zero_schwartz_cutoff (g : 𝓢(E, ℂ)) {u : 𝓢'(E, F)}
    (hu : MemSobolev 0 2 u) : MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨f, rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  refine ⟨(g.memLp_top (volume : Measure E)).toLp g • f, ?_⟩
  exact (Lp.toTemperedDistribution_smul_eq g.hasTemperateGrowth (g.memLp_top volume) f).symm

/-- Smooth Schwartz cutoffs preserve every nonnegative integer Sobolev order. -/
theorem memSobolev_nat_schwartz_cutoff (n : ℕ) (g : 𝓢(E, ℂ)) {u : 𝓢'(E, F)}
    (hu : MemSobolev (n : ℝ) 2 u) : MemSobolev (n : ℝ) 2 (smulLeftCLM F g u) := by
  induction n generalizing g u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_schwartz_cutoff g hu
  | succ n ih =>
    have hparts := (memSobolev_succ_iff_derivatives (stdOrthonormalBasis ℝ E) (n : ℝ) u).mp
      (by simpa only [Nat.cast_succ] using hu)
    rw [Nat.cast_succ]
    apply (memSobolev_succ_iff_derivatives (stdOrthonormalBasis ℝ E) (n : ℝ) _).mpr
    refine ⟨ih g hparts.1, ?_⟩
    intro i
    rw [distribution_cutoff_leibniz]
    exact (ih (∂_{stdOrthonormalBasis ℝ E i} g) hparts.1).add (ih g (hparts.2 i))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The commutator of the actual Laplacian with a cutoff has only first derivatives of u. -/
theorem distribution_cutoff_laplacian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u) +
      ∑ i, (smulLeftCLM F (∂_{b i} (∂_{b i} g) : 𝓢(E, ℂ)) u +
        smulLeftCLM F (∂_{b i} g : 𝓢(E, ℂ)) (∂_{b i} u) +
          smulLeftCLM F (∂_{b i} g : 𝓢(E, ℂ)) (∂_{b i} u)) := by
  simp only [TemperedDistribution.laplacian_eq_sum b, distribution_cutoff_leibniz,
    LineDeriv.lineDerivOp_add, map_sum, Finset.sum_add_distrib]
  abel

/-- Local elliptic gain after cutting off: one derivative of u and the cutoff forcing control
two derivatives of the cutoff solution. -/
theorem cutoff_elliptic_step (n : ℕ) (g : 𝓢(E, ℂ)) {u : 𝓢'(E, F)}
    (hu : MemSobolev ((n : ℝ) + 1) 2 u)
    (hforcing : MemSobolev (n : ℝ) 2 (smulLeftCLM F g (Δ u))) :
    MemSobolev ((n : ℝ) + 2) 2 (smulLeftCLM F g u) := by
  let b := stdOrthonormalBasis ℝ E
  have hp := (memSobolev_succ_iff_derivatives b (n : ℝ) u).mp hu
  have hcut := memSobolev_nat_schwartz_cutoff n g hp.1
  apply EllipticLocal.CM.Construction.laplacian_sobolev_regularity hcut
  rw [distribution_cutoff_laplacian b]
  apply hforcing.add
  apply memSobolev_finset_sum Finset.univ
  intro i _
  exact ((memSobolev_nat_schwartz_cutoff n (∂_{b i} (∂_{b i} g)) hp.1).add
    (memSobolev_nat_schwartz_cutoff n (∂_{b i} g) (hp.2 i))).add
      (memSobolev_nat_schwartz_cutoff n (∂_{b i} g) (hp.2 i))

end

/-! Continuous representatives obtained from the genuine Fourier and Sobolev comparison. -/

open _root_.MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap BoundedContinuousFunction ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The actual distribution represented by a bounded continuous function. -/
def boundedFunctionDistribution (f : E →ᵇ F) : 𝓢'(E, F) :=
  ((f.memLp_top.toLp f : Lp F ⊤ (volume : Measure E)) : 𝓢'(E, F))

theorem boundedFunctionDistribution_apply (f : E →ᵇ F) (φ : 𝓢(E, ℂ)) :
    boundedFunctionDistribution f φ = ∫ x, φ x • f x := by
  rw [boundedFunctionDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [f.memLp_top.coeFn_toLp (μ := (volume : Measure E))] with x hx
  rw [hx]

/-- The inverse Fourier integral of an L¹ function represents its distributional inverse transform. -/
theorem l1_fourierInv_distribution (v : Lp F 1 (volume : Measure E)) :
    boundedFunctionDistribution (Real.Lp.fourierTransformInv v) = 𝓕⁻ (v : 𝓢'(E, F)) := by
  ext φ
  rw [boundedFunctionDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (f := (φ : E → ℂ)) (g := (v : E → F)) (L := -innerₗ E)
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    Real.continuous_fourierChar
    (by change Continuous (fun p : E × E => -inner ℝ p.1 p.2); fun_prop)
    φ.integrable (L1.integrable_coeFn v)
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y
    change -inner ℝ y x = -inner ℝ x y
    rw [real_inner_comm]
  rw [hflip] at h
  change (∫ x : E, (𝓕⁻ (φ : E → ℂ)) x • v x) =
    ∫ x : E, φ x • (𝓕⁻ (v : E → F)) x at h
  simpa only [Real.Lp.fourierTransformInv_apply, SchwartzMap.fourierInv_coe] using h.symm

/-- Sobolev order greater than half the real dimension has a bounded continuous representative. -/
theorem sobolev_exists_boundedContinuous {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) :
    ∃ f : E →ᵇ F, boundedFunctionDistribution f = u := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  rw [l1_fourierInv_distribution, ← hv, fourierInv_fourier_eq]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction
