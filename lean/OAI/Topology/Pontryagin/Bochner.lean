import OAI.Topology.Pontryagin.PositiveType
import OAI.Topology.Pontryagin.UnitizationSpectrum
import OAI.Topology.Pontryagin.FourierDense
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Bochner -/

namespace OAI.Topology.Pontryagin.Bochner.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# Bochner's theorem

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
proves **Bochner's theorem**: every continuous function `φ: G → ℂ` of positive type is the
Fourier–Stieltjes transform of a unique finite positive regular measure `σ` on the Pontryagin
dual,

`φ x = ∫ χ, χ x ∂σ`.

The proof follows the positive-functional/Gelfand route (no GNS construction, no spectral
theorem, no Krein–Milman):

1. `posPairing μ hφ hφc F = ∫ x, F x * φ x ∂μ` is a continuous linear functional on `L¹(G)`
 with `‖posPairing F‖ ≤ (φ 1).re * ‖F‖`, conjugate-symmetric for the star involution
 (`posPairing_L1star`) and nonnegative on star-squares
 (`posPairing_star_mul_self_nonneg`, from
 `IsPositiveType.integral_mconv_mstar_mul_nonneg` by density).
2. The sesquilinear form `B X Y = posPairing (X⋆ * Y)` satisfies the Cauchy–Schwarz
 inequality (`norm_posPairing_mul_sq_le`), by the classical discriminant argument.
3. An approximate-identity argument upgrades this to
 `‖posPairing F‖² ≤ (φ 1).re * (posPairing (F⋆ * F)).re` (`norm_posPairing_sq_le`).
4. Iterating along the powers `P^(2^n)` of `P = F⋆ * F` and invoking the Gelfand spectral
 radius formula (`L1G.exists_norm_npow_rpow_le`) yields the fundamental bound
 `‖posPairing F‖ ≤ (φ 1).re * ‖𝓕F‖_∞` (`norm_posPairing_le_fourier`).
5. Hence `posPairing` descends along the Fourier transform to a continuous linear functional
 `bochnerCLM` on `C₀(Ĝ, ℂ)` (using the density `dense_ccFourierSubalgebra`), which is
 star-compatible (`bochnerCLM_star`) and positive (`bochnerCLM_nonneg`, by a square-root
 trick).
6. Riesz–Markov–Kakutani (`RealRMK.rieszMeasure`) represents the real part of `bochnerCLM`
 by a regular measure `bochnerMeasure0`, which is finite (`bochnerMeasure0_isFiniteMeasure`)
 with total mass at most `(φ 1).re`, and `bochnerCLM u = ∫ u ∂(bochnerMeasure0)` for all
 `u ∈ C₀(Ĝ, ℂ)` (`bochnerCLM_eq_integral`).
7. Testing against continuous compactly supported functions and using the Fubini identity
 `integral_fourierTransform_cc` identifies `φ` with `x ↦ conj (∫ χ, χ x ∂bochnerMeasure0)`;
 pushing the measure forward by inversion of the dual group finishes the proof.

## Main results

* `IsPositiveType.exists_bochner_measure`: **Bochner's theorem** (existence);
* `IsPositiveType.bochner_measure_unique`: uniqueness of the representing measure;
* `IsPositiveType.bochner_measure_mass`: the total mass of the representing measure is
 `(φ 1).re`;
* `bochnerCLM` with `bochnerCLM_ccFourierC0`: the positive functional on `C₀(Ĝ, ℂ)` induced
 by `φ`, agreeing with `∫ x, f x * φ x ∂μ` on Fourier transforms of `C_c` functions;
* `norm_posPairing_le_fourier`: the fundamental spectral bound;
* `IsCompact.exists_nhds_one_forall_norm_char_sub_one_le`: equicontinuity of compact sets of
 characters;
* `ZeroAtInftyContinuousMap.exists_hasCompactSupport_norm_sub_le`: density of compactly
 supported functions in `C₀`.
-/

open Filter Function Set _root_.Topology _root_.PontryaginDual
open scoped ComplexConjugate ComplexOrder ENNReal NNReal ZeroAtInfty CompactlySupported

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

-- `show` is used pervasively to beta-reduce integrands and to cross the definitional equality
-- between the type synonym `L1G μ` and `Lp ℂ 1 μ`.

/-! ### Density of compactly supported functions in `C₀` -/

section C0Density

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- **Compactly supported functions are dense in `C₀`**: every `u ∈ C₀(X, ℂ)` is within `ε`
of an element of `C₀(X, ℂ)` with compact support. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.ZeroAtInftyContinuousMap.exists_hasCompactSupport_norm_sub_le (u : C₀(X, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : C₀(X, ℂ), HasCompactSupport ⇑w ∧ ‖w - u‖ ≤ ε := by
  -- a compact set outside which `u` is small
  have hsmall : {x : X | ‖u x‖ < ε} ∈ Filter.cocompact X := by
    have h1 : Tendsto ⇑u (Filter.cocompact X) (nhds 0) := u.zero_at_infty'
    have h2 := h1 (Metric.ball_mem_nhds (0 : ℂ) hε)
    refine Filter.mem_of_superset h2 fun x hx => ?_
    simpa [Metric.mem_ball, dist_zero_right] using hx
  obtain ⟨K₀, hK₀comp, hK₀sub⟩ := Filter.mem_cocompact.mp hsmall
  -- a Urysohn bump equal to `1` on `K₀`
  obtain ⟨ψ, hψ1, -, hψs, hψ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK₀comp isClosed_empty (Set.disjoint_empty K₀)
  have hwc : Continuous fun x => ((ψ x : ℝ) : ℂ) * u x :=
    (Complex.continuous_ofReal.comp ψ.continuous).mul (map_continuous u)
  have hws : HasCompactSupport fun x => ((ψ x : ℝ) : ℂ) * u x := by
    refine hψs.mono fun x hx => ?_
    simp only [mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0, Complex.ofReal_zero, zero_mul])
  refine ⟨⟨⟨fun x => ((ψ x : ℝ) : ℂ) * u x, hwc⟩, hws.is_zero_at_infty⟩, hws, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hε.le).mpr fun x => ?_
  show ‖((ψ x : ℝ) : ℂ) * u x - u x‖ ≤ ε
  by_cases hx : x ∈ K₀
  · have h1 : ψ x = 1 := hψ1 hx
    rw [h1, Complex.ofReal_one, one_mul, sub_self, norm_zero]
    exact hε.le
  · have hxs : ‖u x‖ < ε := hK₀sub hx
    have hb : ‖((ψ x : ℝ) : ℂ) * u x - u x‖ = ‖((ψ x - 1 : ℝ) : ℂ)‖ * ‖u x‖ := by
      rw [← norm_mul]
      congr 1
      push_cast
      ring
    have h01 := hψ01 x
    have hle1 : ‖((ψ x - 1 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [h01.1, h01.2], by linarith [h01.1, h01.2]⟩
    calc ‖((ψ x : ℝ) : ℂ) * u x - u x‖
        = ‖((ψ x - 1 : ℝ) : ℂ)‖ * ‖u x‖ := hb
      _ ≤ 1 * ε := mul_le_mul hle1 hxs.le (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end C0Density

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### Equicontinuity of compact sets of characters -/

section Equicontinuity

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- **Equicontinuity of a compact set of characters**: for a compact set `Q` of characters
and `ε > 0` there is a neighborhood `W` of `1` in `G` on which every `χ ∈ Q` is uniformly
within `ε` of `1`. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.IsCompact.exists_nhds_one_forall_norm_char_sub_one_le
    {Q : Set (PontryaginDual G)} (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ nhds (1 : G), ∀ χ ∈ Q, ∀ x ∈ W, ‖(χ x : ℂ) - 1‖ ≤ ε := by
  obtain ⟨C, hCcomp, hCnhds⟩ := exists_compact_mem_nhds (1 : G)
  have hrpos : 0 < min (ε / 2) Real.pi := lt_min (by linarith) Real.pi_pos
  set N : Set (PontryaginDual G) :=
    {ψ | ∀ x ∈ C, ‖(ψ x : ℂ) - 1‖ < min (ε / 2) Real.pi} with hNdef
  have hN : N ∈ nhds (1 : PontryaginDual G) :=
    DualPolars.PontryaginDual.eventually_uniform_arc hCcomp hrpos (min_le_right _ _)
  have hUχ : ∀ χ₀ : PontryaginDual G,
      (fun χ : PontryaginDual G => χ / χ₀) ⁻¹' N ∈ nhds χ₀ := by
    intro χ₀
    have hc : Continuous fun χ : PontryaginDual G => χ / χ₀ :=
      continuous_id.div' continuous_const
    have h1 : N ∈ nhds ((fun χ : PontryaginDual G => χ / χ₀) χ₀) := by
      simpa [div_self'] using hN
    exact hc.continuousAt.preimage_mem_nhds h1
  obtain ⟨t, -, hcover⟩ :=
    hQ.elim_nhds_subcover (fun χ₀ => (fun χ : PontryaginDual G => χ / χ₀) ⁻¹' N)
      fun χ₀ _ => hUχ χ₀
  have hVmem : ∀ χ₀ : PontryaginDual G,
      {x : G | ‖(χ₀ x : ℂ) - 1‖ < ε / 2} ∈ nhds (1 : G) := by
    intro χ₀
    have hc : Continuous fun x : G => ‖(χ₀ x : ℂ) - 1‖ :=
      ((continuous_induced_dom.comp (map_continuous χ₀)).sub continuous_const).norm
    have h1 : Set.Iio (ε / 2) ∈ nhds ((fun x : G => ‖(χ₀ x : ℂ) - 1‖) 1) := by
      have h2 : ((χ₀ (1 : G) : Circle) : ℂ) = 1 := by rw [_root_.map_one, Circle.coe_one]
      simpa [h2] using Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)
    exact hc.continuousAt.preimage_mem_nhds h1
  refine ⟨C ∩ ⋂ χ₀ ∈ t, {x : G | ‖(χ₀ x : ℂ) - 1‖ < ε / 2},
    Filter.inter_mem hCnhds ((Filter.biInter_finset_mem t).mpr fun χ₀ _ => hVmem χ₀),
    fun χ hχQ x hx => ?_⟩
  obtain ⟨hxC, hxV⟩ := hx
  obtain ⟨χ₀, hχ₀t, hχdiv⟩ : ∃ χ₀ ∈ t, χ / χ₀ ∈ N := by
    have h := hcover hχQ
    simpa only [Set.mem_iUnion, Set.mem_preimage, exists_prop] using h
  have h1 : ‖(χ x : ℂ) - (χ₀ x : ℂ)‖ ≤ ε / 2 := by
    rw [FourierTransform.PontryaginDual.norm_coe_sub_coe]
    exact ((hχdiv x hxC).trans_le (min_le_left _ _)).le
  have h2 : ‖(χ₀ x : ℂ) - 1‖ ≤ ε / 2 := (Set.mem_iInter₂.mp hxV χ₀ hχ₀t).le
  calc ‖(χ x : ℂ) - 1‖
      = ‖((χ x : ℂ) - (χ₀ x : ℂ)) + ((χ₀ x : ℂ) - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(χ x : ℂ) - (χ₀ x : ℂ)‖ + ‖(χ₀ x : ℂ) - 1‖ := norm_add_le _ _
    _ ≤ ε := by linarith

end Equicontinuity

/-! ### The positive pairing on `L¹(G)` -/

section PosPairing

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

include hφ hφc

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [μ.IsHaarMeasure] [μ.Regular] in
/-- The integrand of the positive pairing is integrable: an `L¹` function times a bounded
continuous function. -/
private theorem integrable_coeFn_mul_posType (F : Lp ℂ 1 μ) :
    Integrable (fun x => F x * φ x) μ :=
  (L1.integrable_coeFn F).mul_bdd hφc.aestronglyMeasurable
    (Eventually.of_forall fun x => hφ.norm_apply_le x)

/-- Pairing an `L¹` class against a continuous function of positive type, as a continuous
linear functional on `L¹(G)`: `posPairing μ hφ hφc F = ∫ x, F x * φ x ∂μ`. -/
def posPairing : Lp ℂ 1 μ →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun F : Lp ℂ 1 μ => ∫ x, F x * φ x ∂μ
      map_add' := fun F K => by
        rw [← integral_add (integrable_coeFn_mul_posType μ hφ hφc F)
          (integrable_coeFn_mul_posType μ hφ hφc K)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add F K] with x hx
        rw [hx, Pi.add_apply, add_mul]
      map_smul' := fun c F => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    ⟨(φ 1).re, fun F => by
      calc ‖∫ x, F x * φ x ∂μ‖
          ≤ ∫ x, ‖F x‖ * (φ 1).re ∂μ := by
            refine norm_integral_le_of_norm_le (((L1.integrable_coeFn F).norm).mul_const _)
              (Eventually.of_forall fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hφ.norm_apply_le x) (norm_nonneg _)
        _ = (φ 1).re * ‖F‖ := by
            rw [integral_mul_const, ← L1.norm_eq_integral_norm, mul_comm]⟩

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [μ.IsHaarMeasure] [μ.Regular] in
@[simp]
theorem posPairing_apply (F : Lp ℂ 1 μ) :
    posPairing μ hφ hφc F = ∫ x, F x * φ x ∂μ := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [μ.IsHaarMeasure] [μ.Regular] in
/-- The fundamental norm bound `‖posPairing F‖ ≤ (φ 1).re * ‖F‖`. -/
theorem norm_posPairing_apply_le (F : Lp ℂ 1 μ) :
    ‖posPairing μ hφ hφc F‖ ≤ (φ 1).re * ‖F‖ := by
  rw [posPairing_apply]
  calc ‖∫ x, F x * φ x ∂μ‖
      ≤ ∫ x, ‖F x‖ * (φ 1).re ∂μ := by
        refine norm_integral_le_of_norm_le (((L1.integrable_coeFn F).norm).mul_const _)
          (Eventually.of_forall fun x => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hφ.norm_apply_le x) (norm_nonneg _)
    _ = (φ 1).re * ‖F‖ := by
        rw [integral_mul_const, ← L1.norm_eq_integral_norm, mul_comm]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- On a `C_c` class, the pairing is computed by the representative. -/
theorem posPairing_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) = ∫ x, f x * φ x ∂μ := by
  rw [posPairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs] with x hx
  rw [hx]

omit [T2Space G] in
/-- The pairing intertwines the star involution of `L¹(G)` with complex conjugation. -/
theorem posPairing_L1star (F : Lp ℂ 1 μ) :
    posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1star μ F) = conj (posPairing μ hφ hφc F) := by
  have h1 : posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1star μ F) = ∫ x, conj (F x⁻¹) * φ x ∂μ := by
    rw [posPairing_apply]
    refine integral_congr_ae ?_
    filter_upwards [Pontryagin.Algebra.MeasureTheory.coeFn_L1star μ F] with x hx
    rw [hx, Convolution.MeasureTheory.mstar_apply]
  rw [h1]
  calc ∫ x, conj (F x⁻¹) * φ x ∂μ
      = ∫ x, conj (F x⁻¹) * φ x⁻¹⁻¹ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show conj (F x⁻¹) * φ x = conj (F x⁻¹) * φ x⁻¹⁻¹
        rw [inv_inv]
    _ = ∫ x, conj (F x) * φ x⁻¹ ∂μ :=
        integral_inv_eq_self (fun x => conj (F x) * φ x⁻¹) μ
    _ = ∫ x, conj (F x * φ x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show conj (F x) * φ x⁻¹ = conj (F x * φ x)
        rw [hφ.apply_inv x, ← _root_.map_mul]
    _ = conj (∫ x, F x * φ x ∂μ) := integral_conj
    _ = conj (posPairing μ hφ hφc F) := by rw [posPairing_apply]

/-- **Positivity on star-squares**: `0 ≤ posPairing (F⋆ * F)`, first on `C_c` classes by
`IsPositiveType.integral_mconv_mstar_mul_nonneg`, then on all of `L¹(G)` by density. -/
theorem posPairing_star_mul_self_nonneg (F : Lp ℂ 1 μ) :
    0 ≤ posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F) := by
  have hcont : Continuous fun K : Lp ℂ 1 μ =>
      posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K) := by
    apply (posPairing μ hφ hφc).continuous.comp
    exact (Pontryagin.Algebra.MeasureTheory.mulCLM μ).continuous₂.comp ((Pontryagin.Algebra.MeasureTheory.continuous_L1star μ).prodMk continuous_id)
  have hclosed : IsClosed ((fun K : Lp ℂ 1 μ =>
      posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K)) ⁻¹' {z : ℂ | 0 ≤ z}) :=
    (isClosed_Ici (a := (0 : ℂ))).preimage hcont
  have hsub : (Pontryagin.Algebra.MeasureTheory.ccSubmodule μ : Set (Lp ℂ 1 μ)) ⊆ (fun K : Lp ℂ 1 μ =>
      posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K)) ⁻¹' {z : ℂ | 0 ≤ z} := by
    intro K hK
    obtain ⟨f, hfc, hfs, hf⟩ := (Pontryagin.Algebra.MeasureTheory.mem_ccSubmodule_iff μ).mp hK
    have hrw : K = Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs := Lp.ext (hf.trans (Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs).symm)
    show 0 ≤ posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K)
    rw [hrw, Pontryagin.Algebra.MeasureTheory.L1star_toLpCc μ f hfc hfs,
      Pontryagin.Algebra.MeasureTheory.mulCLM_toLpCc μ (Convolution.MeasureTheory.mstar f) f (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs) hfc hfs,
      posPairing_toLpCc μ hφ hφc _ _ _]
    exact hφ.integral_mconv_mstar_mul_nonneg μ hφc hfc hfs
  have huniv : (Set.univ : Set (Lp ℂ 1 μ)) ⊆ (fun K : Lp ℂ 1 μ =>
      posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K)) ⁻¹' {z : ℂ | 0 ≤ z} := by
    rw [← (Pontryagin.Algebra.MeasureTheory.dense_ccSubmodule μ).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ F)

end PosPairing

/-! ### Cauchy–Schwarz for the positive sesquilinear form -/

section CauchySchwarz

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

include hφ hφc

/-- **Cauchy–Schwarz** for the sesquilinear form `B X Y = posPairing (X⋆ * Y)`:
`‖B F K‖² ≤ (B F F).re * (B K K).re`. Proved by the classical discriminant argument;
no inner-product-space structure is introduced. -/
theorem norm_posPairing_mul_sq_le (F K : Lp ℂ 1 μ) :
    ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) K)‖ ^ 2
      ≤ (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re
        * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ K) K)).re := by
  set B : Lp ℂ 1 μ → Lp ℂ 1 μ → ℂ :=
    fun X Y => posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) Y) with hBdef
  show ‖B F K‖ ^ 2 ≤ (B F F).re * (B K K).re
  have hBpos : ∀ X, 0 ≤ B X X := fun X => posPairing_star_mul_self_nonneg μ hφ hφc X
  have hBconj : ∀ X Y, conj (B X Y) = B Y X := by
    intro X Y
    calc conj (B X Y) = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) Y)) :=
          (posPairing_L1star μ hφ hφc _).symm
      _ = B Y X := by
          show posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) Y))
            = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ Y) X)
          rw [Pontryagin.Algebra.MeasureTheory.L1star_mulCLM μ, Pontryagin.Algebra.MeasureTheory.L1star_L1star μ, Pontryagin.Algebra.MeasureTheory.mulCLM_comm μ]
  have hBsmul_left : ∀ (c : ℂ) (X Y : Lp ℂ 1 μ), B (c • X) Y = conj c * B X Y := by
    intro c X Y
    show posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ (c • X)) Y)
      = conj c * posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) Y)
    rw [Pontryagin.Algebra.MeasureTheory.L1star_smul μ, map_smul, smul_apply, map_smul, smul_eq_mul]
  have hBsmul_right : ∀ (c : ℂ) (X Y : Lp ℂ 1 μ), B X (c • Y) = c * B X Y := by
    intro c X Y
    show posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) (c • Y))
      = c * posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) Y)
    rw [map_smul, map_smul, smul_eq_mul]
  have hBadd_left : ∀ X X' Y : Lp ℂ 1 μ, B (X + X') Y = B X Y + B X' Y := by
    intro X X' Y
    show posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ (X + X')) Y) = _
    rw [Pontryagin.Algebra.MeasureTheory.L1star_add μ, map_add, add_apply, map_add]
  have hBadd_right : ∀ X Y Y' : Lp ℂ 1 μ, B X (Y + Y') = B X Y + B X Y' := by
    intro X Y Y'
    show posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ X) (Y + Y')) = _
    rw [map_add, map_add]
  have hFF : 0 ≤ (B F F).re := (Complex.nonneg_iff.mp (hBpos F)).1
  have hKK : 0 ≤ (B K K).re := (Complex.nonneg_iff.mp (hBpos K)).1
  rcases eq_or_ne (B F K) 0 with hz | hz
  · rw [hz, norm_zero]
    simpa using mul_nonneg hFF hKK
  · have hznorm : 0 < ‖B F K‖ := norm_pos_iff.mpr hz
    set z : ℂ := B F K with hzdef
    set u : ℂ := conj z / ((‖z‖ : ℝ) : ℂ) with hudef
    have hu_norm : ‖u‖ = 1 := by
      rw [hudef, norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self hznorm.ne']
    have huz : u * z = ((‖z‖ : ℝ) : ℂ) := by
      rw [hudef, div_mul_eq_mul_div]
      rw [show conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
      rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) by
        push_cast; ring]
      rw [mul_div_assoc, div_self (by exact_mod_cast hznorm.ne'), mul_one]
    have huu : conj u * u = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu_norm]
      norm_num
    set W : Lp ℂ 1 μ := u • K with hWdef
    have hBFW : B F W = ((‖z‖ : ℝ) : ℂ) := by
      rw [hWdef, hBsmul_right, ← hzdef]
      exact huz
    have hBWF : B W F = ((‖z‖ : ℝ) : ℂ) := by
      rw [← hBconj F W, hBFW, Complex.conj_ofReal]
    have hBWW : B W W = B K K := by
      rw [hWdef, hBsmul_left, hBsmul_right, ← mul_assoc, huu, one_mul]
    -- the nonnegative quadratic in a real variable `t`
    have hquad : ∀ t : ℝ,
        0 ≤ (B K K).re * (t * t) + 2 * ‖z‖ * t + (B F F).re := by
      intro t
      have h0 := hBpos ((t : ℂ) • W + F)
      have hexp : B ((t : ℂ) • W + F) ((t : ℂ) • W + F)
          = (t : ℂ) * ((t : ℂ) * B K K)
            + ((t : ℂ) * ((‖z‖ : ℝ) : ℂ) + ((t : ℂ) * ((‖z‖ : ℝ) : ℂ) + B F F)) := by
        have e1 : B ((t : ℂ) • W + F) ((t : ℂ) • W + F)
            = B ((t : ℂ) • W) ((t : ℂ) • W + F) + B F ((t : ℂ) • W + F) :=
          hBadd_left _ _ _
        have e2 : B ((t : ℂ) • W) ((t : ℂ) • W + F)
            = B ((t : ℂ) • W) ((t : ℂ) • W) + B ((t : ℂ) • W) F := hBadd_right _ _ _
        have e3 : B F ((t : ℂ) • W + F) = B F ((t : ℂ) • W) + B F F := hBadd_right _ _ _
        have e4 : B ((t : ℂ) • W) ((t : ℂ) • W) = conj (t : ℂ) * ((t : ℂ) * B W W) := by
          rw [hBsmul_left, hBsmul_right]
        have e5 : B ((t : ℂ) • W) F = conj (t : ℂ) * B W F := hBsmul_left _ _ _
        have e6 : B F ((t : ℂ) • W) = (t : ℂ) * B F W := hBsmul_right _ _ _
        rw [e1, e2, e3, e4, e5, e6, Complex.conj_ofReal, hBWW, hBWF, hBFW]
        ring
      rw [hexp] at h0
      have hre := (Complex.nonneg_iff.mp h0).1
      have hcompute : ((t : ℂ) * ((t : ℂ) * B K K)
          + ((t : ℂ) * ((‖z‖ : ℝ) : ℂ) + ((t : ℂ) * ((‖z‖ : ℝ) : ℂ) + B F F))).re
          = (B K K).re * (t * t) + 2 * ‖z‖ * t + (B F F).re := by
        simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
        ring
      rw [hcompute] at hre
      exact hre
    have hd := discrim_le_zero hquad
    rw [discrim] at hd
    show ‖z‖ ^ 2 ≤ (B F F).re * (B K K).re
    nlinarith [hd]

end CauchySchwarz

/-! ### The first bound: `‖posPairing F‖² ≤ (φ 1).re * (posPairing (F⋆ * F)).re` -/

section FirstBound

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

include hφ hφc

/-- **The approximate-identity bound**: for every `F ∈ L¹(G)`,
`‖posPairing F‖² ≤ (φ 1).re * (posPairing (F⋆ * F)).re`. -/
theorem norm_posPairing_sq_le (F : Lp ℂ 1 μ) :
    ‖posPairing μ hφ hφc F‖ ^ 2
      ≤ (φ 1).re * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re := by
  have hCφ0 : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp hφ.apply_one_nonneg).1
  have hFF0 : 0 ≤ (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re :=
    (Complex.nonneg_iff.mp (posPairing_star_mul_self_nonneg μ hφ hφc F)).1
  set R : ℝ :=
    Real.sqrt ((φ 1).re * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re) with hRdef
  -- Step 1: for every ε > 0, `‖posPairing F‖ ≤ (φ 1).re * ε + R`.
  have key : ∀ ε : ℝ, 0 < ε → ‖posPairing μ hφ hφc F‖ ≤ (φ 1).re * ε + R := by
    intro ε hε
    obtain ⟨U, hU, hUprop⟩ := Pontryagin.Algebra.MeasureTheory.L1G.exists_bump_mul_close μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F) hε
    have hU' : U ∩ U⁻¹ ∈ nhds (1 : G) := Filter.inter_mem hU (inv_mem_nhds_one G hU)
    obtain ⟨h, hhc, hhs, hh0, hhsupp, hhint⟩ := Translation.MeasureTheory.exists_normalized_bump μ (U ∩ U⁻¹) hU'
    -- the reflected bump `h'` = `x ↦ h x⁻¹`, again a normalized bump supported in `U`
    have hh'c : Continuous fun x : G => h x⁻¹ := hhc.comp continuous_inv
    have hsupp' : tsupport (fun x : G => h x⁻¹) = (tsupport h)⁻¹ := by
      have hs : support (fun x : G => h x⁻¹) = (support h)⁻¹ := by
        ext x
        simp only [mem_support, Set.mem_inv]
      unfold tsupport
      rw [hs, ← inv_closure]
    have hh's : HasCompactSupport fun x : G => h x⁻¹ := by
      have hcomp := IsCompact.inv (hhs : IsCompact (tsupport h))
      rwa [← hsupp'] at hcomp
    have hh'0 : ∀ x : G, 0 ≤ h x⁻¹ := fun x => hh0 x⁻¹
    have hh'supp : tsupport (fun x : G => h x⁻¹) ⊆ U := by
      rw [hsupp']
      intro x hx
      have h1 : x⁻¹ ∈ U ∩ U⁻¹ := hhsupp (Set.mem_inv.mp hx)
      have h2 : x⁻¹ ∈ U⁻¹ := h1.2
      rwa [Set.mem_inv, inv_inv] at h2
    have hh'int : ∫ x, h x⁻¹ ∂μ = 1 := (integral_inv_eq_self h μ).trans hhint
    -- the `L¹` class of the complexified bump
    set H : Lp ℂ 1 μ := Pontryagin.Algebra.MeasureTheory.toLpCc μ (fun x => ((h x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hhc) (hhs.comp_left Complex.ofReal_zero) with hHdef
    have hHnorm : ‖H‖ = 1 := Pontryagin.Algebra.MeasureTheory.L1G.norm_bump μ h hhc hhs hh0 hhint
    have hstarH : Pontryagin.Algebra.MeasureTheory.L1star μ H = Pontryagin.Algebra.MeasureTheory.toLpCc μ (fun x => ((h x⁻¹ : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp hh'c) (hh's.comp_left Complex.ofReal_zero) := by
      rw [hHdef, Pontryagin.Algebra.MeasureTheory.L1star_toLpCc]
      refine Pontryagin.Algebra.MeasureTheory.toLpCc_congr μ _ _ _ _ ?_
      funext x
      show conj ((h x⁻¹ : ℝ) : ℂ) = ((h x⁻¹ : ℝ) : ℂ)
      exact Complex.conj_ofReal _
    -- the approximate-identity estimate transported to `mulCLM`
    have hclose : ‖Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F - F‖ ≤ ε := by
      have hb := hUprop (fun x => h x⁻¹) hh'c hh's hh'0 hh'supp hh'int
      have heq : Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.bump μ (fun x => h x⁻¹) hh'c hh's) = Pontryagin.Algebra.MeasureTheory.L1star μ H :=
        Eq.trans rfl hstarH.symm
      have he2 : Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.bump μ (fun x => h x⁻¹) hh'c hh's * Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F)
          = Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F := by
        rw [Pontryagin.Algebra.MeasureTheory.L1G.toLp_mul, heq, Pontryagin.Algebra.MeasureTheory.L1G.toLp_ofLp]
      calc ‖Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F - F‖
          = ‖Pontryagin.Algebra.MeasureTheory.L1G.bump μ (fun x => h x⁻¹) hh'c hh's * Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F - Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F‖ := by
            rw [← he2]
            rfl
        _ ≤ ε := hb
    -- assemble the estimate
    have hsplit : posPairing μ hφ hφc F
        = posPairing μ hφ hφc (F - Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)
          + posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F) := by
      rw [← map_add]
      congr 1
      abel
    have h1 : ‖posPairing μ hφ hφc (F - Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖ ≤ (φ 1).re * ε := by
      refine (norm_posPairing_apply_le μ hφ hφc _).trans ?_
      have h2 : ‖F - Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F‖ ≤ ε := by
        rw [norm_sub_rev]
        exact hclose
      exact mul_le_mul_of_nonneg_left h2 hCφ0
    have h2 : ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖ ≤ R := by
      have hcs := norm_posPairing_mul_sq_le μ hφ hφc H F
      have hHH : (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) H)).re ≤ (φ 1).re := by
        calc (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) H)).re
            ≤ ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) H)‖ :=
              (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ (φ 1).re * ‖Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) H‖ := norm_posPairing_apply_le μ hφ hφc _
          _ ≤ (φ 1).re * (‖Pontryagin.Algebra.MeasureTheory.L1star μ H‖ * ‖H‖) :=
              mul_le_mul_of_nonneg_left (Pontryagin.Algebra.MeasureTheory.norm_mulCLM_apply_le μ _ _) hCφ0
          _ = (φ 1).re := by rw [Pontryagin.Algebra.MeasureTheory.norm_L1star μ, hHnorm, one_mul, mul_one]
      have hsq : ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖ ^ 2
          ≤ (φ 1).re * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re :=
        hcs.trans (mul_le_mul_of_nonneg_right hHH hFF0)
      rw [hRdef]
      exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg hCφ0 hFF0)).mpr hsq
    calc ‖posPairing μ hφ hφc F‖
        = ‖posPairing μ hφ hφc (F - Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)
            + posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖ := by rw [← hsplit]
      _ ≤ ‖posPairing μ hφ hφc (F - Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖
            + ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ H) F)‖ := norm_add_le _ _
      _ ≤ (φ 1).re * ε + R := add_le_add h1 h2
  -- Step 2: let ε → 0.
  have hle : ‖posPairing μ hφ hφc F‖ ≤ R := by
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    have hεp : 0 < ε' / ((φ 1).re + 1) := by positivity
    refine (key _ hεp).trans ?_
    have h3 : (φ 1).re / ((φ 1).re + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (φ 1).re * (ε' / ((φ 1).re + 1)) ≤ ε' := by
      calc (φ 1).re * (ε' / ((φ 1).re + 1))
          = ((φ 1).re / ((φ 1).re + 1)) * ε' := by ring
        _ ≤ 1 * ε' := mul_le_mul_of_nonneg_right h3 hε'.le
        _ = ε' := one_mul ε'
    linarith
  -- Step 3: square.
  calc ‖posPairing μ hφ hφc F‖ ^ 2
      ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = (φ 1).re * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re :=
        Real.sq_sqrt (mul_nonneg hCφ0 hFF0)

end FirstBound

/-! ### Convolution-power bookkeeping in `L1G` -/

section NpowHelpers

/-- Convolution powers multiply: `F^(a+1) * F^(b+1) = F^(a+b+2)` in `npow` indexing. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.npow_mul_npow (Q : Pontryagin.Algebra.MeasureTheory.L1G μ) (a b : ℕ) :
    Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q a * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q b = Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q (a + b + 1) := by
  induction a with
  | zero =>
    rw [Pontryagin.Algebra.MeasureTheory.L1G.npow_zero, Nat.zero_add, ← Pontryagin.Algebra.MeasureTheory.L1G.npow_succ]
  | succ a ih =>
    calc Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q (a + 1) * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q b
        = Q * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q a * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q b := by rw [Pontryagin.Algebra.MeasureTheory.L1G.npow_succ]
      _ = Q * (Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q a * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q b) := mul_assoc _ _ _
      _ = Q * Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q (a + b + 1) := by rw [ih]
      _ = Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q (a + b + 1 + 1) := (Pontryagin.Algebra.MeasureTheory.L1G.npow_succ μ Q (a + b + 1)).symm
      _ = Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q (a + 1 + b + 1) := by
          congr 1
          omega

/-- The star involution acts on convolution powers through the base. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.star_npow (Q : Pontryagin.Algebra.MeasureTheory.L1G μ) (n : ℕ) :
    star (Pontryagin.Algebra.MeasureTheory.L1G.npow μ Q n) = Pontryagin.Algebra.MeasureTheory.L1G.npow μ (star Q) n := by
  induction n with
  | zero => rw [Pontryagin.Algebra.MeasureTheory.L1G.npow_zero, Pontryagin.Algebra.MeasureTheory.L1G.npow_zero]
  | succ n ih =>
    rw [Pontryagin.Algebra.MeasureTheory.L1G.npow_succ, star_mul, ih, mul_comm, Pontryagin.Algebra.MeasureTheory.L1G.npow_succ]

end NpowHelpers

/-! ### The fundamental bound: `‖posPairing F‖ ≤ (φ 1).re * ‖𝓕F‖_∞` -/

section FourierBound

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

include hφ hφc

/-- **The fundamental spectral bound.** For every `F ∈ L¹(G)`,

`‖posPairing μ hφ hφc F‖ ≤ (φ 1).re * ‖𝓕F‖_∞`.

The proof iterates the Cauchy–Schwarz bound `norm_posPairing_sq_le` along the convolution
powers `P^(2^n)` of `P = F⋆ * F` (which is star-self-adjoint) and controls
`‖P^(2^n)‖^(2^{-n})` by the Gelfand spectral-radius formula
(`L1G.exists_norm_npow_rpow_le`), with `‖𝓕P‖_∞ ≤ ‖𝓕F‖_∞²`. -/
theorem norm_posPairing_le_fourier (F : Lp ℂ 1 μ) :
    ‖posPairing μ hφ hφc F‖ ≤ (φ 1).re * ‖Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F)‖ := by
  have hCφ0 : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp hφ.apply_one_nonneg).1
  set F' : Pontryagin.Algebra.MeasureTheory.L1G μ := Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ F with hF'def
  set P' : Pontryagin.Algebra.MeasureTheory.L1G μ := star F' * F' with hP'def
  set C0 : ℝ := ‖Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ F'‖ with hC0def
  have hC00 : 0 ≤ C0 := norm_nonneg _
  -- the sequence of norms along the powers `P'^(2^k)`
  set a : ℕ → ℝ :=
    fun k => ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)))‖ with hadef
  have ha0 : ∀ k, 0 ≤ a k := fun k => norm_nonneg _
  -- `P'` is star-self-adjoint, hence so are all its powers
  have hPstar : star P' = P' := by
    rw [hP'def, star_mul, star_star]
  have hXstar : ∀ m : ℕ, star (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' m) = Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' m := fun m => by
    rw [Pontryagin.Algebra.MeasureTheory.L1G.star_npow, hPstar]
  -- the recurrence `a k ^ 2 ≤ Cφ * a (k+1)`
  have hstep : ∀ k, a k ^ 2 ≤ (φ 1).re * a (k + 1) := by
    intro k
    have h5 := norm_posPairing_sq_le μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)))
    have hL1s : Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)))
        = Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)) := by
      have hst := congrArg (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ) (hXstar (2 ^ k - 1))
      rwa [Pontryagin.Algebra.MeasureTheory.L1G.star_def, Pontryagin.Algebra.MeasureTheory.L1G.toLp_ofLp] at hst
    have hidx : (2 ^ k - 1) + (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
      have hp : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      have hq : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      omega
    have hmul : Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1))))
        (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)))
        = Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ (k + 1) - 1)) := by
      rw [hL1s, ← Pontryagin.Algebra.MeasureTheory.L1G.toLp_mul, Pontryagin.Algebra.MeasureTheory.L1G.npow_mul_npow, hidx]
    rw [hmul] at h5
    refine h5.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCφ0
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  -- the iterated bound `a 0 ^ (2^k) ≤ Cφ ^ (2^k - 1) * a k`
  have hiter : ∀ k, a 0 ^ (2 ^ k) ≤ (φ 1).re ^ (2 ^ k - 1) * a k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : a 0 ^ (2 ^ (k + 1)) = (a 0 ^ (2 ^ k)) ^ 2 := by
        rw [← pow_mul, pow_succ]
      have h2 : (a 0 ^ (2 ^ k)) ^ 2 ≤ ((φ 1).re ^ (2 ^ k - 1) * a k) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (ha0 0) _) ih 2
      have h3 : ((φ 1).re ^ (2 ^ k - 1) * a k) ^ 2
          = (φ 1).re ^ ((2 ^ k - 1) * 2) * a k ^ 2 := by
        rw [mul_pow, ← pow_mul]
      have h4 : (φ 1).re ^ ((2 ^ k - 1) * 2) * a k ^ 2
          ≤ (φ 1).re ^ ((2 ^ k - 1) * 2) * ((φ 1).re * a (k + 1)) :=
        mul_le_mul_of_nonneg_left (hstep k) (pow_nonneg hCφ0 _)
      have h5 : (φ 1).re ^ ((2 ^ k - 1) * 2) * ((φ 1).re * a (k + 1))
          = (φ 1).re ^ ((2 ^ k - 1) * 2 + 1) * a (k + 1) := by
        rw [pow_succ]
        ring
      have h6 : (2 ^ k - 1) * 2 + 1 = 2 ^ (k + 1) - 1 := by
        have hp : 1 ≤ 2 ^ k := Nat.two_pow_pos k
        have hq : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        omega
      calc a 0 ^ (2 ^ (k + 1)) = (a 0 ^ (2 ^ k)) ^ 2 := h1
        _ ≤ ((φ 1).re ^ (2 ^ k - 1) * a k) ^ 2 := h2
        _ = (φ 1).re ^ ((2 ^ k - 1) * 2) * a k ^ 2 := h3
        _ ≤ (φ 1).re ^ ((2 ^ k - 1) * 2) * ((φ 1).re * a (k + 1)) := h4
        _ = (φ 1).re ^ ((2 ^ k - 1) * 2 + 1) * a (k + 1) := h5
        _ = (φ 1).re ^ (2 ^ (k + 1) - 1) * a (k + 1) := by rw [h6]
  -- the trivial bound `a k ≤ Cφ * ‖P'^(2^k)‖`
  have hbound : ∀ k, a k ≤ (φ 1).re * ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)‖ := by
    intro k
    have h1 := norm_posPairing_apply_le μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ k - 1)))
    rwa [Pontryagin.Algebra.MeasureTheory.L1G.norm_toLp] at h1
  -- the uniform Fourier bound for `P'`
  have hfourier : ∀ χ : PontryaginDual G, ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ P' χ‖ ≤ C0 ^ 2 := by
    intro χ
    rw [hP'def, Pontryagin.Algebra.MeasureTheory.L1G.fourier_mul, Pontryagin.Algebra.MeasureTheory.L1G.fourier_star, norm_mul, RCLike.norm_conj]
    have h1 : ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F' χ‖ ≤ C0 := by
      have h2 := FourierDense.ZeroAtInftyContinuousMap.norm_apply_le (Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ F') χ
      rwa [Pontryagin.Algebra.MeasureTheory.L1G.coe_fourierC0] at h2
    calc ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F' χ‖ * ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F' χ‖
        ≤ C0 * C0 := mul_le_mul h1 h1 (norm_nonneg _) hC00
      _ = C0 ^ 2 := (pow_two C0).symm
  -- for every ε > 0, `a 0 ≤ Cφ * (C0² + ε)`
  have hkey : ∀ ε : ℝ, 0 < ε → a 0 ≤ (φ 1).re * (C0 ^ 2 + ε) := by
    intro ε hε
    obtain ⟨N, hN⟩ := Pontryagin.Algebra.MeasureTheory.L1G.exists_norm_npow_rpow_le μ P' (sq_nonneg C0) hfourier hε
    have hkN : 2 ^ N - 1 ≥ N := by
      have := Nat.lt_two_pow_self (n := N)
      omega
    have h6 := hN (2 ^ N - 1) hkN
    have hone : (1 : ℕ) ≤ 2 ^ N := Nat.two_pow_pos N
    have hcast : ((2 ^ N - 1 : ℕ) : ℝ) + 1 = ((2 ^ N : ℕ) : ℝ) := by
      rw [Nat.cast_sub hone, Nat.cast_one]
      ring
    rw [hcast] at h6
    have hM0 : (0 : ℝ) < ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos N
    -- convert the rpow bound into a plain power bound
    have hyM : ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ N - 1)‖ ≤ (C0 ^ 2 + ε) ^ (2 ^ N : ℕ) := by
      have h7 : (‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ N - 1)‖ ^ ((1 : ℝ) / ((2 ^ N : ℕ) : ℝ)))
            ^ (((2 ^ N : ℕ) : ℝ)) ≤ (C0 ^ 2 + ε) ^ (((2 ^ N : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h6 hM0.le
      rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hM0.ne', Real.rpow_one,
        Real.rpow_natCast] at h7
      exact h7
    have hchain : a 0 ^ (2 ^ N) ≤ ((φ 1).re * (C0 ^ 2 + ε)) ^ (2 ^ N) := by
      calc a 0 ^ (2 ^ N)
          ≤ (φ 1).re ^ (2 ^ N - 1) * a N := hiter N
        _ ≤ (φ 1).re ^ (2 ^ N - 1) * ((φ 1).re * ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ N - 1)‖) :=
            mul_le_mul_of_nonneg_left (hbound N) (pow_nonneg hCφ0 _)
        _ = (φ 1).re ^ (2 ^ N - 1 + 1) * ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ N - 1)‖ := by
            rw [pow_succ]
            ring
        _ = (φ 1).re ^ (2 ^ N) * ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ N - 1)‖ := by
            rw [Nat.sub_add_cancel hone]
        _ ≤ (φ 1).re ^ (2 ^ N) * (C0 ^ 2 + ε) ^ (2 ^ N) :=
            mul_le_mul_of_nonneg_left hyM (pow_nonneg hCφ0 _)
        _ = ((φ 1).re * (C0 ^ 2 + ε)) ^ (2 ^ N) := (mul_pow _ _ _).symm
    exact le_of_pow_le_pow_left₀ (Nat.two_pow_pos N).ne'
      (mul_nonneg hCφ0 (add_nonneg (sq_nonneg C0) hε.le)) hchain
  -- pass to the limit ε → 0
  have ha0C : a 0 ≤ (φ 1).re * C0 ^ 2 := by
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    have hεp : 0 < ε' / ((φ 1).re + 1) := by positivity
    refine (hkey _ hεp).trans ?_
    have h3 : (φ 1).re / ((φ 1).re + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (φ 1).re * (ε' / ((φ 1).re + 1)) ≤ ε' := by
      calc (φ 1).re * (ε' / ((φ 1).re + 1))
          = ((φ 1).re / ((φ 1).re + 1)) * ε' := by ring
        _ ≤ 1 * ε' := mul_le_mul_of_nonneg_right h3 hε'.le
        _ = ε' := one_mul ε'
    calc (φ 1).re * (C0 ^ 2 + ε' / ((φ 1).re + 1))
        = (φ 1).re * C0 ^ 2 + (φ 1).re * (ε' / ((φ 1).re + 1)) := by ring
      _ ≤ (φ 1).re * C0 ^ 2 + ε' := by linarith
  -- identify `a 0` and conclude
  have hA0 : a 0 = ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)‖ := by
    have h1 : (2 ^ 0 - 1 : ℕ) = 0 := by norm_num
    have h2 : Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ 0 - 1)) = Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F := by
      rw [h1, Pontryagin.Algebra.MeasureTheory.L1G.npow_zero, hP'def, Pontryagin.Algebra.MeasureTheory.L1G.toLp_mul, Pontryagin.Algebra.MeasureTheory.L1G.star_def, Pontryagin.Algebra.MeasureTheory.L1G.toLp_ofLp, hF'def,
        Pontryagin.Algebra.MeasureTheory.L1G.toLp_ofLp]
    show ‖posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.npow μ P' (2 ^ 0 - 1)))‖ = _
    rw [h2]
  have hsq := norm_posPairing_sq_le μ hφ hφc F
  have hre_le : (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re ≤ a 0 := by
    rw [hA0]
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hfinal : ‖posPairing μ hφ hφc F‖ ^ 2 ≤ ((φ 1).re * C0) ^ 2 := by
    calc ‖posPairing μ hφ hφc F‖ ^ 2
        ≤ (φ 1).re * (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.mulCLM μ (Pontryagin.Algebra.MeasureTheory.L1star μ F) F)).re := hsq
      _ ≤ (φ 1).re * a 0 := mul_le_mul_of_nonneg_left hre_le hCφ0
      _ ≤ (φ 1).re * ((φ 1).re * C0 ^ 2) := mul_le_mul_of_nonneg_left ha0C hCφ0
      _ = ((φ 1).re * C0) ^ 2 := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hCφ0 hC00) hfinal

end FourierBound

/-! ### Algebraic lemmas for `C_c` classes and their transforms -/

section CcAlgebra

/-- The bundled transform is additive in the function. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.PontryaginDual.ccFourierC0_add {f g : G → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    FourierDense.PontryaginDual.ccFourierC0 μ (f + g) (hfc.add hgc) (hfs.add hgs)
      = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs + FourierDense.PontryaginDual.ccFourierC0 μ g hgc hgs := by
  ext χ
  rw [ZeroAtInftyContinuousMap.add_apply]
  exact congrFun (FourierTransform.PontryaginDual.fourierTransform_add μ (hfc.integrable_of_hasCompactSupport hfs)
    (hgc.integrable_of_hasCompactSupport hgs)) χ

/-- The bundled transform is homogeneous in the function. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.PontryaginDual.ccFourierC0_smul (c : ℂ) {f : G → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    FourierDense.PontryaginDual.ccFourierC0 μ (c • f) (hfc.const_smul c) (hfs.mono (support_const_smul_subset c f))
      = c • FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs := by
  ext χ
  rw [ZeroAtInftyContinuousMap.smul_apply]
  exact congrFun (FourierTransform.PontryaginDual.fourierTransform_smul μ c f) χ

/-- The bundled transform of the zero function is zero. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.PontryaginDual.ccFourierC0_zero :
    FourierDense.PontryaginDual.ccFourierC0 μ (0 : G → ℂ) continuous_const HasCompactSupport.zero = 0 := by
  ext χ
  rw [ZeroAtInftyContinuousMap.zero_apply]
  show FourierTransform.PontryaginDual.fourierTransform μ (0 : G → ℂ) χ = 0
  rw [FourierTransform.PontryaginDual.fourierTransform_apply]
  simp

/-- The bundled transform intertwines `mstar` and the star of `C₀`. -/
theorem _root_.OAI.Topology.Pontryagin.Bochner.PontryaginDual.ccFourierC0_star {f : G → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    star (FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs) = FourierDense.PontryaginDual.ccFourierC0 μ (Convolution.MeasureTheory.mstar f) (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs) := by
  ext χ
  rw [ZeroAtInftyContinuousMap.star_apply]
  show star (FourierTransform.PontryaginDual.fourierTransform μ f χ) = FourierTransform.PontryaginDual.fourierTransform μ (Convolution.MeasureTheory.mstar f) χ
  rw [FourierTransform.PontryaginDual.fourierTransform_mstar μ f χ]
  rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- `C_c` classes add under `toLpCc`. -/
theorem toLpCc_add {f g : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Pontryagin.Algebra.MeasureTheory.toLpCc μ (f + g) (hfc.add hgc) (hfs.add hgs)
      = Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs + Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs := by
  refine Lp.ext ?_
  filter_upwards [Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ (f + g) (hfc.add hgc) (hfs.add hgs),
    Lp.coeFn_add (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs),
    Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs, Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ g hgc hgs] with x h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, Pi.add_apply, h3, h4]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- `C_c` classes rescale under `toLpCc`. -/
theorem toLpCc_smul (c : ℂ) {f : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Pontryagin.Algebra.MeasureTheory.toLpCc μ (c • f) (hfc.const_smul c) (hfs.mono (support_const_smul_subset c f))
      = c • Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs := by
  refine Lp.ext ?_
  filter_upwards [Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ (c • f) (hfc.const_smul c)
      (hfs.mono (support_const_smul_subset c f)),
    Lp.coeFn_smul c (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs), Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, h3]

/-- The bundled `C₀` Fourier transform of a `C_c` class agrees with the bundled transform
of the representative. -/
theorem fourierC0_ofLp_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs := by
  ext χ
  show Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) χ = FourierTransform.PontryaginDual.fourierTransform μ f χ
  rw [Pontryagin.Algebra.MeasureTheory.L1G.fourier_ofLp_toLpCc μ f hfc hfs]

end CcAlgebra

/-! ### The Bochner functional on `C₀(Ĝ, ℂ)` -/

section BochnerCLM

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

include hφ hφc

/-- **Well-definedness of the descended functional**: two `C_c` functions with the same
Fourier transform have the same positive pairing. This is the key consequence of the
fundamental bound `norm_posPairing_le_fourier`. -/
private theorem posPairing_toLpCc_congr {f g : G → ℂ}
    (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hgc : Continuous g) (hgs : HasCompactSupport g)
    (h : FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs = FourierDense.PontryaginDual.ccFourierC0 μ g hgc hgs) :
    posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) := by
  have hfg : FourierTransform.PontryaginDual.fourierTransform μ f = FourierTransform.PontryaginDual.fourierTransform μ g := by
    have h2 := congrArg (fun v : C₀(PontryaginDual G, ℂ) => ⇑v) h
    simpa only [FourierDense.PontryaginDual.coe_ccFourierC0] using h2
  have hDae : ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) =ᵐ[μ] f - g := by
    filter_upwards [Lp.coeFn_sub (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs),
      Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs, Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ g hgc hgs] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  have hzero : Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)) = 0 := by
    ext χ
    rw [ZeroAtInftyContinuousMap.zero_apply]
    show FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) χ = 0
    calc FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) χ
        = FourierTransform.PontryaginDual.fourierTransform μ (f - g) χ := by rw [FourierTransform.PontryaginDual.fourierTransform_congr_ae hDae]
      _ = (FourierTransform.PontryaginDual.fourierTransform μ f - FourierTransform.PontryaginDual.fourierTransform μ g) χ := by
          rw [FourierTransform.PontryaginDual.fourierTransform_sub μ (hfc.integrable_of_hasCompactSupport hfs)
            (hgc.integrable_of_hasCompactSupport hgs)]
      _ = FourierTransform.PontryaginDual.fourierTransform μ f χ - FourierTransform.PontryaginDual.fourierTransform μ g χ := rfl
      _ = 0 := by rw [hfg, sub_self]
  have hD : posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) = 0 := by
    have h1 := norm_posPairing_le_fourier μ hφ hφc
      (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs - Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)
    rw [hzero, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  rw [map_sub] at hD
  exact sub_eq_zero.mp hD

omit hφ hφc in
/-- The subspace of `C₀(Ĝ, ℂ)` of Fourier transforms of `C_c` functions, as a submodule
(the same carrier as `ccFourierSubalgebra`). -/
private abbrev ccFourierSubmodule : Submodule ℂ C₀(PontryaginDual G, ℂ) where
  carrier := {u | ∃ f : G → ℂ, ∃ (hfc : Continuous f) (hfs : HasCompactSupport f),
    u = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs}
  add_mem' := by
    rintro u v ⟨f, hfc, hfs, rfl⟩ ⟨g, hgc, hgs, rfl⟩
    exact ⟨f + g, hfc.add hgc, hfs.add hgs, (Bochner.PontryaginDual.ccFourierC0_add μ hfc hfs hgc hgs).symm⟩
  zero_mem' := ⟨0, continuous_const, HasCompactSupport.zero, (Bochner.PontryaginDual.ccFourierC0_zero μ).symm⟩
  smul_mem' := by
    rintro c u ⟨f, hfc, hfs, rfl⟩
    exact ⟨c • f, hfc.const_smul c, hfs.mono (support_const_smul_subset c f),
      (Bochner.PontryaginDual.ccFourierC0_smul μ c hfc hfs).symm⟩

omit hφ hφc in
private theorem coe_ccFourierSubmodule :
    (ccFourierSubmodule μ : Set C₀(PontryaginDual G, ℂ))
      = (FourierDense.PontryaginDual.ccFourierSubalgebra μ : Set C₀(PontryaginDual G, ℂ)) := rfl

omit hφ hφc in
private theorem dense_ccFourierSubmodule :
    Dense (ccFourierSubmodule μ : Set C₀(PontryaginDual G, ℂ)) := by
  rw [coe_ccFourierSubmodule]
  exact FourierDense.PontryaginDual.dense_ccFourierSubalgebra μ

omit hφ hφc in
private theorem denseRange_ccFourierSubtypeL :
    DenseRange ⇑(ccFourierSubmodule μ).subtypeL :=
  (dense_ccFourierSubmodule μ).denseRange_val

omit hφ hφc in
private theorem isUniformInducing_ccFourierSubtypeL :
    IsUniformInducing ⇑(ccFourierSubmodule μ).subtypeL :=
  isUniformEmbedding_subtype_val.isUniformInducing

omit hφ hφc in
private theorem ccFourierSubmodule_mem_def (u : ccFourierSubmodule μ) :
    ∃ f : G → ℂ, ∃ (hfc : Continuous f) (hfs : HasCompactSupport f),
      (u : C₀(PontryaginDual G, ℂ)) = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs := u.2

omit hφ hφc in
/-- A choice of `C_c` representative of an element of `ccFourierSubmodule`. -/
private def bochnerRep (u : ccFourierSubmodule μ) : G → ℂ :=
  (ccFourierSubmodule_mem_def μ u).choose

omit hφ hφc in
private theorem bochnerRep_continuous (u : ccFourierSubmodule μ) : Continuous (bochnerRep μ u) :=
  (ccFourierSubmodule_mem_def μ u).choose_spec.choose

omit hφ hφc in
private theorem bochnerRep_hasCompactSupport (u : ccFourierSubmodule μ) :
    HasCompactSupport (bochnerRep μ u) :=
  (ccFourierSubmodule_mem_def μ u).choose_spec.choose_spec.choose

omit hφ hφc in
private theorem ccFourierC0_bochnerRep (u : ccFourierSubmodule μ) :
    (u : C₀(PontryaginDual G, ℂ))
      = FourierDense.PontryaginDual.ccFourierC0 μ (bochnerRep μ u) (bochnerRep_continuous μ u)
          (bochnerRep_hasCompactSupport μ u) :=
  (ccFourierSubmodule_mem_def μ u).choose_spec.choose_spec.choose_spec

/-- The value of the descended functional on the subspace of transforms. -/
private def bochnerVal (u : ccFourierSubmodule μ) : ℂ :=
  posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ (bochnerRep μ u) (bochnerRep_continuous μ u)
    (bochnerRep_hasCompactSupport μ u))

private theorem bochnerVal_eq (u : ccFourierSubmodule μ) {f : G → ℂ}
    (hfc : Continuous f) (hfs : HasCompactSupport f)
    (h : (u : C₀(PontryaginDual G, ℂ)) = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs) :
    bochnerVal μ hφ hφc u = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) :=
  posPairing_toLpCc_congr μ hφ hφc (bochnerRep_continuous μ u)
    (bochnerRep_hasCompactSupport μ u) hfc hfs
    ((ccFourierC0_bochnerRep μ u).symm.trans h)

private theorem bochnerVal_add (u v : ccFourierSubmodule μ) :
    bochnerVal μ hφ hφc (u + v) = bochnerVal μ hφ hφc u + bochnerVal μ hφ hφc v := by
  have hsum : ((u + v : ccFourierSubmodule μ) : C₀(PontryaginDual G, ℂ))
      = FourierDense.PontryaginDual.ccFourierC0 μ (bochnerRep μ u + bochnerRep μ v)
        ((bochnerRep_continuous μ u).add (bochnerRep_continuous μ v))
        ((bochnerRep_hasCompactSupport μ u).add (bochnerRep_hasCompactSupport μ v)) := by
    rw [Submodule.coe_add, ccFourierC0_bochnerRep μ u, ccFourierC0_bochnerRep μ v,
      ← Bochner.PontryaginDual.ccFourierC0_add]
  rw [bochnerVal_eq μ hφ hφc (u + v) _ _ hsum, toLpCc_add, map_add]
  rfl

private theorem bochnerVal_smul (c : ℂ) (u : ccFourierSubmodule μ) :
    bochnerVal μ hφ hφc (c • u) = c * bochnerVal μ hφ hφc u := by
  have hcu : ((c • u : ccFourierSubmodule μ) : C₀(PontryaginDual G, ℂ))
      = FourierDense.PontryaginDual.ccFourierC0 μ (c • bochnerRep μ u)
        ((bochnerRep_continuous μ u).const_smul c)
        ((bochnerRep_hasCompactSupport μ u).mono
          (support_const_smul_subset c (bochnerRep μ u))) := by
    rw [Submodule.coe_smul, ccFourierC0_bochnerRep μ u, ← Bochner.PontryaginDual.ccFourierC0_smul]
  rw [bochnerVal_eq μ hφ hφc (c • u) _ _ hcu, toLpCc_smul, map_smul]
  rfl

private theorem norm_bochnerVal_le (u : ccFourierSubmodule μ) :
    ‖bochnerVal μ hφ hφc u‖ ≤ (φ 1).re * ‖u‖ := by
  have h1 := norm_posPairing_le_fourier μ hφ hφc
    (Pontryagin.Algebra.MeasureTheory.toLpCc μ (bochnerRep μ u) (bochnerRep_continuous μ u)
      (bochnerRep_hasCompactSupport μ u))
  rw [fourierC0_ofLp_toLpCc, ← ccFourierC0_bochnerRep μ u, Submodule.norm_coe] at h1
  exact h1

-- Select the inherited normed-space structures before constructing the extension.
local instance : NormedAddCommGroup (ccFourierSubmodule μ) :=
  (ccFourierSubmodule μ).normedAddCommGroup
local instance : NormedSpace ℂ (ccFourierSubmodule μ) :=
  (ccFourierSubmodule μ).normedSpace

/-- The linear part of the descended functional, with its type explicit. -/
private def bochnerSubLinear : ccFourierSubmodule μ →ₗ[ℂ] ℂ where
  toFun := bochnerVal μ hφ hφc
  map_add' := bochnerVal_add μ hφ hφc
  map_smul' c u := bochnerVal_smul μ hφ hφc c u

/-- The descended functional on the subspace of transforms, as a continuous linear map. -/
private def bochnerSubCLM : ccFourierSubmodule μ →L[ℂ] ℂ :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := ccFourierSubmodule μ) (F := ℂ)
    (bochnerSubLinear μ hφ hφc)
    ((φ 1).re) (norm_bochnerVal_le μ hφ hφc)

/-- **The Bochner functional**: the continuous linear functional on `C₀(Ĝ, ℂ)` obtained by
extending `f ↦ ∫ x, f x * φ x ∂μ` along the Fourier transform, using the density of `C_c`
transforms. -/
def bochnerCLM : C₀(PontryaginDual G, ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.extend (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := ccFourierSubmodule μ) (Eₗ := C₀(PontryaginDual G, ℂ)) (F := ℂ)
    (bochnerSubCLM μ hφ hφc) (ccFourierSubmodule μ).subtypeL

private theorem bochnerCLM_coe (u : ccFourierSubmodule μ) :
    bochnerCLM μ hφ hφc (u : C₀(PontryaginDual G, ℂ)) = bochnerVal μ hφ hφc u := by
  have h := ContinuousLinearMap.extend_eq (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := ccFourierSubmodule μ) (Eₗ := C₀(PontryaginDual G, ℂ)) (F := ℂ)
    (bochnerSubCLM μ hφ hφc) (denseRange_ccFourierSubtypeL μ)
    (isUniformInducing_ccFourierSubtypeL μ) u
  rw [Submodule.subtypeL_apply] at h
  exact h

/-- **Agreement**: on the Fourier transform of a `C_c` function, the Bochner functional is
the positive pairing: `bochnerCLM (𝓕f) = ∫ x, f x * φ x ∂μ`. -/
theorem bochnerCLM_ccFourierC0 (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    bochnerCLM μ hφ hφc (FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs) = ∫ x, f x * φ x ∂μ := by
  have hmem : FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs ∈ ccFourierSubmodule μ := ⟨f, hfc, hfs, rfl⟩
  have h := bochnerCLM_coe μ hφ hφc ⟨FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs, hmem⟩
  rw [bochnerVal_eq μ hφ hφc _ hfc hfs rfl, posPairing_toLpCc μ hφ hφc f hfc hfs] at h
  exact h

/-- The Bochner functional inherits the norm bound `(φ 1).re` from the fundamental bound. -/
theorem norm_bochnerCLM_apply_le (u : C₀(PontryaginDual G, ℂ)) :
    ‖bochnerCLM μ hφ hφc u‖ ≤ (φ 1).re * ‖u‖ := by
  have hCφ0 : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp hφ.apply_one_nonneg).1
  have hnorm : ‖bochnerCLM μ hφ hφc‖ ≤ (φ 1).re := by
    have he : ∀ x : ccFourierSubmodule μ,
        ‖x‖ ≤ ((1 : ℝ≥0) : ℝ) * ‖(ccFourierSubmodule μ).subtypeL x‖ := by
      intro x
      rw [NNReal.coe_one, one_mul, Submodule.subtypeL_apply, ← Submodule.norm_coe]
    have h1 := (bochnerSubCLM μ hφ hφc).opNorm_extend_le (N := 1)
      (denseRange_ccFourierSubtypeL μ) he
    rw [NNReal.coe_one, one_mul] at h1
    exact h1.trans (LinearMap.mkContinuous_norm_le _ hCφ0 _)
  calc ‖bochnerCLM μ hφ hφc u‖
      ≤ ‖bochnerCLM μ hφ hφc‖ * ‖u‖ := (bochnerCLM μ hφ hφc).le_opNorm u
    _ ≤ (φ 1).re * ‖u‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)

/-- The Bochner functional intertwines the star of `C₀` with complex conjugation. -/
theorem bochnerCLM_star (u : C₀(PontryaginDual G, ℂ)) :
    bochnerCLM μ hφ hφc (star u) = conj (bochnerCLM μ hφ hφc u) := by
  have heq : (fun u : C₀(PontryaginDual G, ℂ) => bochnerCLM μ hφ hφc (star u))
      = fun u => conj (bochnerCLM μ hφ hφc u) := by
    refine Continuous.ext_on (FourierDense.PontryaginDual.dense_ccFourierSubalgebra μ)
      ((bochnerCLM μ hφ hφc).continuous.comp continuous_star)
      (Complex.continuous_conj.comp (bochnerCLM μ hφ hφc).continuous) ?_
    rintro u ⟨f, hfc, hfs, rfl⟩
    show bochnerCLM μ hφ hφc (star (FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs))
      = conj (bochnerCLM μ hφ hφc (FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs))
    rw [Bochner.PontryaginDual.ccFourierC0_star μ hfc hfs, bochnerCLM_ccFourierC0 μ hφ hφc (Convolution.MeasureTheory.mstar f) (Convolution.Continuous.mstar hfc)
      (Convolution.HasCompactSupport.mstar hfs), bochnerCLM_ccFourierC0 μ hφ hφc f hfc hfs]
    calc ∫ x, Convolution.MeasureTheory.mstar f x * φ x ∂μ
        = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mstar f) (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs)) :=
          (posPairing_toLpCc μ hφ hφc (Convolution.MeasureTheory.mstar f) (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs)).symm
      _ = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) := by
          rw [Pontryagin.Algebra.MeasureTheory.L1star_toLpCc]
      _ = conj (posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) :=
          posPairing_L1star μ hφ hφc _
      _ = conj (∫ x, f x * φ x ∂μ) := by rw [posPairing_toLpCc μ hφ hφc f hfc hfs]
  exact congrFun heq u

/-- **Positivity of the Bochner functional**: it is nonnegative (in `ComplexOrder`) on
functions with nonnegative values, by the square-root trick and positivity on star-squares
of transforms. -/
theorem bochnerCLM_nonneg {γ : C₀(PontryaginDual G, ℂ)} (hγ : ∀ χ, 0 ≤ γ χ) :
    0 ≤ bochnerCLM μ hφ hφc γ := by
  have hCφ0 : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp hφ.apply_one_nonneg).1
  -- the square root of `γ`
  have hwc : Continuous fun χ : PontryaginDual G => Real.sqrt ((γ χ).re) :=
    Real.continuous_sqrt.comp (Complex.continuous_re.comp (map_continuous γ))
  have hwz : Tendsto (fun χ : PontryaginDual G => ((Real.sqrt ((γ χ).re) : ℝ) : ℂ))
      (cocompact (PontryaginDual G)) (nhds 0) := by
    have h1 : Tendsto ⇑γ (cocompact (PontryaginDual G)) (nhds 0) := γ.zero_at_infty'
    have h2 : Tendsto (fun χ : PontryaginDual G => (γ χ).re)
        (cocompact (PontryaginDual G)) (nhds 0) := by
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp h1
    have h3 : Tendsto (fun χ : PontryaginDual G => Real.sqrt ((γ χ).re))
        (cocompact (PontryaginDual G)) (nhds 0) := by
      simpa [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h3
  set W : C₀(PontryaginDual G, ℂ) :=
    ⟨⟨fun χ => ((Real.sqrt ((γ χ).re) : ℝ) : ℂ), Complex.continuous_ofReal.comp hwc⟩,
      hwz⟩ with hWdef
  have hγW : γ = star W * W := by
    ext χ
    rw [ZeroAtInftyContinuousMap.mul_apply, ZeroAtInftyContinuousMap.star_apply]
    show γ χ = star ((Real.sqrt ((γ χ).re) : ℝ) : ℂ) * ((Real.sqrt ((γ χ).re) : ℝ) : ℂ)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp (hγ χ)
    rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h1]
    exact Complex.ext rfl (by rw [Complex.ofReal_im, ← h2])
  -- approximate `W` by transforms and take a limit of nonnegative values: the target value
  -- lies in the closure of the closed set of nonnegative complex numbers (`isClosed_Ici`
  -- for the scoped `ComplexOrder`, whose topology is order-closed).
  suffices key : ∀ ε : ℝ, 0 < ε →
      ∃ w : ℂ, 0 ≤ w ∧ ‖bochnerCLM μ hφ hφc γ - w‖ ≤ ε by
    have hz : bochnerCLM μ hφ hφc γ ∈ closure (Set.Ici (0 : ℂ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨w, hw0, hwd⟩ := key (ε / 2) (half_pos hε)
      exact ⟨w, hw0, lt_of_le_of_lt (by rwa [dist_eq_norm]) (half_lt_self hε)⟩
    simpa using isClosed_Ici.closure_subset hz
  intro ε hε
  have hMW1 : (0 : ℝ) < 2 * ‖W‖ + 1 := by positivity
  have hden : (0 : ℝ) < ((φ 1).re + 1) * (2 * ‖W‖ + 1) := by positivity
  set δ : ℝ := min 1 (ε / (((φ 1).re + 1) * (2 * ‖W‖ + 1))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
  obtain ⟨f, hfc, hfs, hfd⟩ := FourierDense.PontryaginDual.exists_cc_fourier_close μ W hδpos
  set u : C₀(PontryaginDual G, ℂ) := FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs with hudef
  -- `star u * u` is close to `γ = star W * W`
  have huW : ‖u - W‖ ≤ δ := hfd
  have hu_norm : ‖u‖ ≤ ‖W‖ + δ := by
    calc ‖u‖ = ‖(u - W) + W‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - W‖ + ‖W‖ := norm_add_le _ _
      _ ≤ ‖W‖ + δ := by linarith
  have hclose : ‖star u * u - γ‖ ≤ δ * (2 * ‖W‖ + 1) := by
    rw [hγW]
    have hdecomp : star u * u - star W * W
        = star u * (u - W) + (star u - star W) * W := by
      rw [mul_sub, sub_mul]
      abel
    calc ‖star u * u - star W * W‖
        = ‖star u * (u - W) + (star u - star W) * W‖ := by rw [hdecomp]
      _ ≤ ‖star u * (u - W)‖ + ‖(star u - star W) * W‖ := norm_add_le _ _
      _ ≤ ‖star u‖ * ‖u - W‖ + ‖star u - star W‖ * ‖W‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖u‖ * ‖u - W‖ + ‖u - W‖ * ‖W‖ := by
          rw [norm_star u, ← star_sub u W, norm_star (u - W)]
      _ ≤ (‖W‖ + δ) * δ + δ * ‖W‖ := by
          have h1 : ‖u‖ * ‖u - W‖ ≤ (‖W‖ + δ) * δ :=
            mul_le_mul hu_norm huW (norm_nonneg _) (by positivity)
          have h2 : ‖u - W‖ * ‖W‖ ≤ δ * ‖W‖ :=
            mul_le_mul_of_nonneg_right huW (norm_nonneg _)
          linarith
      _ ≤ δ * (2 * ‖W‖ + 1) := by
          have hδ1 : δ ≤ 1 := min_le_left _ _
          nlinarith [hδpos.le, norm_nonneg W]
  -- the approximating value is nonnegative
  refine ⟨bochnerCLM μ hφ hφc (star u * u), ?_, ?_⟩
  · have hmul : star u * u = FourierDense.PontryaginDual.ccFourierC0 μ (Convolution.MeasureTheory.mconv μ (Convolution.MeasureTheory.mstar f) f)
        (Convolution.Continuous.mconv (μ := μ)
          (Convolution.Continuous.mstar hfc)
          (Convolution.HasCompactSupport.mstar hfs) hfc hfs)
        (Convolution.HasCompactSupport.mconv (μ := μ)
          (Convolution.HasCompactSupport.mstar hfs) hfs) := by
      ext χ
      rw [ZeroAtInftyContinuousMap.mul_apply, ZeroAtInftyContinuousMap.star_apply]
      show star (FourierTransform.PontryaginDual.fourierTransform μ f χ) * FourierTransform.PontryaginDual.fourierTransform μ f χ
        = FourierTransform.PontryaginDual.fourierTransform μ (Convolution.MeasureTheory.mconv μ (Convolution.MeasureTheory.mstar f) f) χ
      rw [FourierTransform.PontryaginDual.fourierTransform_mconv μ (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs) hfc hfs χ,
        FourierTransform.PontryaginDual.fourierTransform_mstar μ f χ]
      rfl
    rw [hmul, bochnerCLM_ccFourierC0 μ hφ hφc (Convolution.MeasureTheory.mconv μ (Convolution.MeasureTheory.mstar f) f) _ _]
    exact hφ.integral_mconv_mstar_mul_nonneg μ hφc hfc hfs
  · rw [← map_sub]
    refine (norm_bochnerCLM_apply_le μ hφ hφc _).trans ?_
    have h1 : ‖γ - star u * u‖ ≤ δ * (2 * ‖W‖ + 1) := by
      rw [norm_sub_rev]
      exact hclose
    have hδle : δ ≤ ε / (((φ 1).re + 1) * (2 * ‖W‖ + 1)) := min_le_right _ _
    calc (φ 1).re * ‖γ - star u * u‖
        ≤ (φ 1).re * (δ * (2 * ‖W‖ + 1)) := mul_le_mul_of_nonneg_left h1 hCφ0
      _ ≤ ((φ 1).re + 1) * (δ * (2 * ‖W‖ + 1)) := by
          have := mul_nonneg hδpos.le hMW1.le
          nlinarith
      _ = (((φ 1).re + 1) * (2 * ‖W‖ + 1)) * δ := by ring
      _ ≤ (((φ 1).re + 1) * (2 * ‖W‖ + 1))
            * (ε / (((φ 1).re + 1) * (2 * ‖W‖ + 1))) :=
          mul_le_mul_of_nonneg_left hδle hden.le
      _ = ε := mul_div_cancel₀ ε hden.ne'

end BochnerCLM

/-! ### The Riesz–Markov–Kakutani measure on the dual group -/

section DualMeasure

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- **Continuity of the Fourier–Stieltjes transform**: for a finite inner-regular measure
`σ` on the dual group, `x ↦ ∫ χ, χ x ∂σ` is continuous on `G`. The proof combines inner
regularity (to reduce to a compact set of characters) with the equicontinuity lemma
`IsCompact.exists_nhds_one_forall_norm_char_sub_one_le`. -/
theorem continuous_integral_char (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ]
    [σ.InnerRegularCompactLTTop] :
    Continuous fun x : G => ∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ := by
  have hcont : ∀ z : G, Continuous fun χ : PontryaginDual G => (χ z : ℂ) := fun z => by
    refine continuous_subtype_val.comp ?_
    change Continuous fun χ : G →ₜ* Circle => χ z
    exact continuous_eval_const z
  have hint : ∀ z : G, Integrable (fun χ : PontryaginDual G => (χ z : ℂ)) σ := fun z =>
    (integrable_const (1 : ℝ)).mono' (hcont z).aestronglyMeasurable
      (Eventually.of_forall fun χ => (Circle.norm_coe (χ z)).le)
  rw [continuous_iff_continuousAt]
  intro x₀
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  set M : ℝ := σ.real Set.univ with hMdef
  have hM0 : 0 ≤ M := measureReal_nonneg
  -- a compact set of characters carrying most of the mass
  obtain ⟨Q, -, hQcomp, hQlt⟩ := MeasurableSet.univ.exists_isCompact_lt_add
    (μ := σ) (measure_ne_top σ _) (by positivity : ENNReal.ofReal (ε / 8) ≠ 0)
  have hQc : σ Qᶜ ≤ ENNReal.ofReal (ε / 8) := by
    rw [measure_compl hQcomp.measurableSet (measure_ne_top σ Q)]
    rw [tsub_le_iff_right, add_comm]
    exact hQlt.le
  have hQcreal : σ.real Qᶜ ≤ ε / 8 := ENNReal.toReal_le_of_le_ofReal (by positivity) hQc
  -- equicontinuity of `Q`
  obtain ⟨W, hW, hWsmall⟩ :=
    Bochner.IsCompact.exists_nhds_one_forall_norm_char_sub_one_le
      (ε := ε / (4 * (M + 1))) hQcomp (by positivity)
  -- eventually `x * x₀⁻¹ ∈ W`
  have hnhds : {x : G | x * x₀⁻¹ ∈ W} ∈ nhds x₀ := by
    have hc : Continuous fun x : G => x * x₀⁻¹ := continuous_id.mul continuous_const
    have h1 : W ∈ nhds ((fun x : G => x * x₀⁻¹) x₀) := by
      rwa [show (fun x : G => x * x₀⁻¹) x₀ = 1 from mul_inv_cancel x₀]
    exact hc.continuousAt.preimage_mem_nhds h1
  filter_upwards [hnhds] with x hx
  rw [dist_eq_norm]
  show ‖(∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ) - ∫ χ : PontryaginDual G, (χ x₀ : ℂ) ∂σ‖ < ε
  have hsub : (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ) - ∫ χ : PontryaginDual G, (χ x₀ : ℂ) ∂σ
      = ∫ χ : PontryaginDual G, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ :=
    (integral_sub (hint x) (hint x₀)).symm
  have hsplit : ∫ χ : PontryaginDual G, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ
      = (∫ χ in Q, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ)
        + ∫ χ in Qᶜ, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ :=
    (integral_add_compl hQcomp.measurableSet ((hint x).sub (hint x₀))).symm
  -- the estimate on `Q`
  have hptQ : ∀ χ ∈ Q, ‖(χ x : ℂ) - (χ x₀ : ℂ)‖ ≤ ε / (4 * (M + 1)) := by
    intro χ hχ
    have h1 : (χ x : ℂ) = (χ (x * x₀⁻¹) : ℂ) * (χ x₀ : ℂ) := by
      rw [← Circle.coe_mul, ← _root_.map_mul, inv_mul_cancel_right]
    calc ‖(χ x : ℂ) - (χ x₀ : ℂ)‖
        = ‖((χ (x * x₀⁻¹) : ℂ) - 1) * (χ x₀ : ℂ)‖ := by
          rw [h1, sub_mul, one_mul]
      _ = ‖(χ (x * x₀⁻¹) : ℂ) - 1‖ := by rw [norm_mul, Circle.norm_coe, mul_one]
      _ ≤ ε / (4 * (M + 1)) := hWsmall χ hχ _ hx
  have hQbound : ‖∫ χ in Q, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ‖ ≤ ε / (4 * (M + 1)) * σ.real Q :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top σ Q) hptQ
  -- the estimate on `Qᶜ`
  have hptQc : ∀ χ ∈ Qᶜ, ‖(χ x : ℂ) - (χ x₀ : ℂ)‖ ≤ 2 := by
    intro χ _
    calc ‖(χ x : ℂ) - (χ x₀ : ℂ)‖
        ≤ ‖(χ x : ℂ)‖ + ‖(χ x₀ : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Circle.norm_coe, Circle.norm_coe]; norm_num
  have hQcbound : ‖∫ χ in Qᶜ, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ‖ ≤ 2 * σ.real Qᶜ :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top σ Qᶜ) hptQc
  -- assemble
  have hQreal : σ.real Q ≤ M := measureReal_mono (Set.subset_univ Q) (measure_ne_top σ _)
  have hfrac : ε / (4 * (M + 1)) * σ.real Q ≤ ε / 4 := by
    have h1 : ε / (4 * (M + 1)) * σ.real Q ≤ ε / (4 * (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ε / (4 * (M + 1)) * σ.real Q
        ≤ ε / (4 * (M + 1)) * (M + 1) := h1
      _ = ε / 4 := by field_simp
  calc ‖(∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ) - ∫ χ : PontryaginDual G, (χ x₀ : ℂ) ∂σ‖
      = ‖(∫ χ in Q, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ)
          + ∫ χ in Qᶜ, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ‖ := by rw [hsub, hsplit]
    _ ≤ ‖∫ χ in Q, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ‖
          + ‖∫ χ in Qᶜ, ((χ x : ℂ) - (χ x₀ : ℂ)) ∂σ‖ := norm_add_le _ _
    _ ≤ ε / (4 * (M + 1)) * σ.real Q + 2 * σ.real Qᶜ := add_le_add hQbound hQcbound
    _ ≤ ε / 4 + 2 * (ε / 8) := by
        refine add_le_add hfrac ?_
        linarith
    _ < ε := by linarith

/-- The complexification of a real compactly supported continuous function on the dual
group, as an element of `C₀(Ĝ, ℂ)`. -/
def bochnerRealC0 (γ : C_c(PontryaginDual G, ℝ)) : C₀(PontryaginDual G, ℂ) where
  toFun := fun χ => ((γ χ : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp (map_continuous γ)
  zero_at_infty' :=
    (γ.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero).is_zero_at_infty

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in
@[simp]
theorem bochnerRealC0_apply (γ : C_c(PontryaginDual G, ℝ)) (χ : PontryaginDual G) :
    bochnerRealC0 γ χ = ((γ χ : ℝ) : ℂ) := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in
theorem bochnerRealC0_add (γ δ : C_c(PontryaginDual G, ℝ)) :
    bochnerRealC0 (γ + δ) = bochnerRealC0 γ + bochnerRealC0 δ := by
  ext χ
  rw [ZeroAtInftyContinuousMap.add_apply, bochnerRealC0_apply, bochnerRealC0_apply,
    bochnerRealC0_apply, CompactlySupportedContinuousMap.add_apply]
  push_cast
  ring

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in
theorem bochnerRealC0_smul (c : ℝ) (γ : C_c(PontryaginDual G, ℝ)) :
    bochnerRealC0 (c • γ) = (c : ℂ) • bochnerRealC0 γ := by
  ext χ
  rw [ZeroAtInftyContinuousMap.smul_apply, bochnerRealC0_apply, bochnerRealC0_apply,
    CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

variable {φ : G → ℂ} (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ)

/-- The positive linear functional on `C_c(Ĝ, ℝ)` given by the real part of the Bochner
functional, ready for Riesz–Markov–Kakutani. -/
def bochnerLambda : C_c(PontryaginDual G, ℝ) →ₚ[ℝ] ℝ where
  toFun := fun γ => (bochnerCLM μ hφ hφc (bochnerRealC0 γ)).re
  map_add' := fun γ δ => by
    rw [bochnerRealC0_add, map_add, Complex.add_re]
  map_smul' := fun c γ => by
    rw [bochnerRealC0_smul, map_smul, RingHom.id_apply, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul]
  monotone' := fun γ δ hγδ => by
    have hpt : ∀ χ, 0 ≤ (bochnerRealC0 δ - bochnerRealC0 γ) χ := by
      intro χ
      rw [ZeroAtInftyContinuousMap.sub_apply, bochnerRealC0_apply, bochnerRealC0_apply,
        ← Complex.ofReal_sub, Complex.zero_le_real]
      exact sub_nonneg.mpr (hγδ χ)
    have h0 := bochnerCLM_nonneg μ hφ hφc hpt
    rw [map_sub] at h0
    have h1 := (Complex.nonneg_iff.mp h0).1
    rw [Complex.sub_re] at h1
    show (bochnerCLM μ hφ hφc (bochnerRealC0 γ)).re ≤ (bochnerCLM μ hφ hφc (bochnerRealC0 δ)).re
    linarith

/-- The **Bochner measure** on the dual group: the Riesz–Markov–Kakutani measure of the
positive functional `bochnerLambda`. -/
def bochnerMeasure0 : Measure (PontryaginDual G) :=
  RealRMK.rieszMeasure (bochnerLambda μ hφ hφc)

theorem bochnerMeasure0_regular : (bochnerMeasure0 μ hφ hφc).Regular :=
  RealRMK.regular_rieszMeasure _

/-- The Bochner measure is finite, with total mass at most `(φ 1).re`. -/
theorem bochnerMeasure0_isFiniteMeasure : IsFiniteMeasure (bochnerMeasure0 μ hφ hφc) := by
  have hCφ0 : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp hφ.apply_one_nonneg).1
  have hreg : (bochnerMeasure0 μ hφ hφc).Regular := bochnerMeasure0_regular μ hφ hφc
  -- every compact set has measure at most `ofReal (φ 1).re`
  have key : ∀ K : Set (PontryaginDual G), IsCompact K →
      bochnerMeasure0 μ hφ hφc K ≤ ENNReal.ofReal (φ 1).re := by
    intro K hK
    obtain ⟨g, hg1, -, hgs, hg01⟩ :=
      exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
    set gc : C_c(PontryaginDual G, ℝ) := ⟨(g : C(PontryaginDual G, ℝ)), hgs⟩ with hgcdef
    have h1 : bochnerMeasure0 μ hφ hφc K ≤ ENNReal.ofReal (bochnerLambda μ hφ hφc gc) :=
      RealRMK.rieszMeasure_le_of_eq_one _ (fun χ => (hg01 χ).1) hK fun χ hχ => hg1 hχ
    have h2 : bochnerLambda μ hφ hφc gc ≤ (φ 1).re := by
      have h3 : ‖bochnerRealC0 gc‖ ≤ 1 := by
        rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun χ => ?_
        show ‖((g χ : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hg01 χ).1], (hg01 χ).2⟩
      calc bochnerLambda μ hφ hφc gc
          = (bochnerCLM μ hφ hφc (bochnerRealC0 gc)).re := rfl
        _ ≤ ‖bochnerCLM μ hφ hφc (bochnerRealC0 gc)‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ (φ 1).re * ‖bochnerRealC0 gc‖ := norm_bochnerCLM_apply_le μ hφ hφc _
        _ ≤ (φ 1).re * 1 := mul_le_mul_of_nonneg_left h3 hCφ0
        _ = (φ 1).re := mul_one _
    exact h1.trans (ENNReal.ofReal_le_ofReal h2)
  -- inner regularity: the total mass is bounded by the compact bound
  have huniv : bochnerMeasure0 μ hφ hφc Set.univ ≤ ENNReal.ofReal (φ 1).re := by
    by_contra hcon
    push Not at hcon
    obtain ⟨K, -, hKcomp, hKlt⟩ := isOpen_univ.exists_lt_isCompact hcon
    exact absurd (key K hKcomp) (not_le.mpr hKlt)
  exact ⟨lt_of_le_of_lt huniv ENNReal.ofReal_lt_top⟩

/-- The Bochner functional is real on (complexified) real compactly supported functions,
and computes the `bochnerMeasure0`-integral. -/
private theorem bochnerCLM_realCc (γ : C_c(PontryaginDual G, ℝ)) :
    bochnerCLM μ hφ hφc (bochnerRealC0 γ)
      = ((∫ χ, γ χ ∂(bochnerMeasure0 μ hφ hφc) : ℝ) : ℂ) := by
  have hstar : star (bochnerRealC0 γ) = bochnerRealC0 γ := by
    ext χ
    rw [ZeroAtInftyContinuousMap.star_apply]
    show star ((γ χ : ℝ) : ℂ) = ((γ χ : ℝ) : ℂ)
    rw [RCLike.star_def]
    exact Complex.conj_ofReal _
  have hconj := bochnerCLM_star μ hφ hφc (bochnerRealC0 γ)
  rw [hstar] at hconj
  have him : (bochnerCLM μ hφ hφc (bochnerRealC0 γ)).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj.symm
  have hre : (bochnerCLM μ hφ hφc (bochnerRealC0 γ)).re
      = ∫ χ, γ χ ∂(bochnerMeasure0 μ hφ hφc) :=
    (RealRMK.integral_rieszMeasure (bochnerLambda μ hφ hφc) γ).symm
  refine Complex.ext ?_ ?_
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

/-- **Integral representation of the Bochner functional**: for every `u ∈ C₀(Ĝ, ℂ)`,
`bochnerCLM u = ∫ χ, u χ ∂(bochnerMeasure0)`. -/
theorem bochnerCLM_eq_integral (u : C₀(PontryaginDual G, ℂ)) :
    bochnerCLM μ hφ hφc u = ∫ χ, u χ ∂(bochnerMeasure0 μ hφ hφc) := by
  have hfin : IsFiniteMeasure (bochnerMeasure0 μ hφ hφc) :=
    bochnerMeasure0_isFiniteMeasure μ hφ hφc
  -- the compactly supported elements are dense in `C₀`
  have hdense : Dense {v : C₀(PontryaginDual G, ℂ) | HasCompactSupport ⇑v} := by
    rw [Metric.dense_iff]
    intro v r hr
    obtain ⟨w, hws, hwd⟩ :=
      Bochner.ZeroAtInftyContinuousMap.exists_hasCompactSupport_norm_sub_le v (half_pos hr)
    refine ⟨w, Metric.mem_ball.mpr ?_, hws⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hwd (half_lt_self hr)
  have hfun : (fun v : C₀(PontryaginDual G, ℂ) => bochnerCLM μ hφ hφc v)
      = fun v : C₀(PontryaginDual G, ℂ) => ∫ χ, v χ ∂(bochnerMeasure0 μ hφ hφc) := by
    refine Continuous.ext_on hdense (bochnerCLM μ hφ hφc).continuous
      (FourierDense.MeasureTheory.continuous_integral_zeroAtInfty (bochnerMeasure0 μ hφ hφc)) ?_
    intro v hv
    show bochnerCLM μ hφ hφc v = ∫ χ, v χ ∂(bochnerMeasure0 μ hφ hφc)
    -- decompose `v` into real and imaginary parts
    set γre : C_c(PontryaginDual G, ℝ) :=
      ⟨⟨fun χ => (v χ).re, Complex.continuous_re.comp (map_continuous v)⟩,
        hv.comp_left (g := Complex.re) Complex.zero_re⟩ with hγredef
    set γim : C_c(PontryaginDual G, ℝ) :=
      ⟨⟨fun χ => (v χ).im, Complex.continuous_im.comp (map_continuous v)⟩,
        hv.comp_left (g := Complex.im) Complex.zero_im⟩ with hγimdef
    have hsplit : v = bochnerRealC0 γre + Complex.I • bochnerRealC0 γim := by
      ext χ
      rw [ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
        bochnerRealC0_apply, bochnerRealC0_apply]
      show v χ = (((v χ).re : ℝ) : ℂ) + Complex.I • (((v χ).im : ℝ) : ℂ)
      rw [smul_eq_mul, mul_comm]
      exact (Complex.re_add_im (v χ)).symm
    have hint1 : Integrable (⇑(bochnerRealC0 γre)) (bochnerMeasure0 μ hφ hφc) :=
      FourierDense.ZeroAtInftyContinuousMap.integrable
        (bochnerMeasure0 μ hφ hφc)
        (bochnerRealC0 γre)
    have hint2 : Integrable (⇑(bochnerRealC0 γim)) (bochnerMeasure0 μ hφ hφc) :=
      FourierDense.ZeroAtInftyContinuousMap.integrable
        (bochnerMeasure0 μ hφ hφc)
        (bochnerRealC0 γim)
    have hR : ∫ χ, (bochnerRealC0 γre + Complex.I • bochnerRealC0 γim) χ
          ∂(bochnerMeasure0 μ hφ hφc)
        = (∫ χ, ((γre χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc))
          + Complex.I * ∫ χ, ((γim χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc) := by
      calc ∫ χ, (bochnerRealC0 γre + Complex.I • bochnerRealC0 γim) χ
            ∂(bochnerMeasure0 μ hφ hφc)
          = ∫ χ, (bochnerRealC0 γre χ + Complex.I * bochnerRealC0 γim χ)
              ∂(bochnerMeasure0 μ hφ hφc) := by
            refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
            rw [ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
              smul_eq_mul]
        _ = (∫ χ, bochnerRealC0 γre χ ∂(bochnerMeasure0 μ hφ hφc))
              + ∫ χ, Complex.I * bochnerRealC0 γim χ ∂(bochnerMeasure0 μ hφ hφc) :=
            integral_add hint1 (hint2.const_mul _)
        _ = (∫ χ, ((γre χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc))
              + Complex.I * ∫ χ, ((γim χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc) := by
            rw [integral_const_mul]
            rfl
    rw [hsplit, map_add, map_smul, bochnerCLM_realCc μ hφ hφc γre,
      bochnerCLM_realCc μ hφ hφc γim, hR,
      show ∫ χ, ((γre χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc)
        = ((∫ χ, γre χ ∂(bochnerMeasure0 μ hφ hφc) : ℝ) : ℂ) from integral_ofReal,
      show ∫ χ, ((γim χ : ℝ) : ℂ) ∂(bochnerMeasure0 μ hφ hφc)
        = ((∫ χ, γim χ ∂(bochnerMeasure0 μ hφ hφc) : ℝ) : ℂ) from integral_ofReal,
      smul_eq_mul]
  exact congrFun hfun u

end DualMeasure

/-! ### Bochner's theorem -/

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]
variable {φ : G → ℂ}

include μ in
/-- **Bochner's theorem.** Every continuous function of positive type on a locally compact
Hausdorff abelian group is the Fourier–Stieltjes transform of a finite positive regular
measure on the Pontryagin dual:

`φ x = ∫ χ, χ x ∂σ`. -/
theorem _root_.OAI.Topology.Pontryagin.PositiveType.IsPositiveType.exists_bochner_measure (hφ : PositiveType.IsPositiveType φ) (hφc : Continuous φ) :
    ∃ σ : Measure (PontryaginDual G), IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ x : G, φ x = ∫ χ, (χ x : ℂ) ∂σ := by
  set σ₀ : Measure (PontryaginDual G) := bochnerMeasure0 μ hφ hφc with hσ₀def
  have : IsFiniteMeasure σ₀ := bochnerMeasure0_isFiniteMeasure μ hφ hφc
  have : σ₀.Regular := bochnerMeasure0_regular μ hφ hφc
  have hψc : Continuous fun x : G => ∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀ :=
    continuous_integral_char σ₀
  -- key identity: testing against complex `C_c` functions
  have hkey : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f),
      ∫ x, f x * φ x ∂μ
        = ∫ x, f x * conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀) ∂μ := by
    intro f hfc hfs
    calc ∫ x, f x * φ x ∂μ
        = posPairing μ hφ hφc (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) :=
          (posPairing_toLpCc μ hφ hφc f hfc hfs).symm
      _ = bochnerCLM μ hφ hφc (FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs) := by
          rw [bochnerCLM_ccFourierC0 μ hφ hφc f hfc hfs,
            posPairing_toLpCc μ hφ hφc f hfc hfs]
      _ = ∫ χ, FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs χ ∂σ₀ := bochnerCLM_eq_integral μ hφ hφc _
      _ = ∫ χ, FourierTransform.PontryaginDual.fourierTransform μ f χ ∂σ₀ := rfl
      _ = ∫ x, f x * conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀) ∂μ :=
          FourierDense.PontryaginDual.integral_fourierTransform_cc μ σ₀ hfc hfs
  -- hence `φ = conj ∘ ψ` everywhere, by the testing lemma
  have huc : Continuous fun x : G =>
      φ x - conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀) :=
    hφc.sub (Complex.continuous_conj.comp hψc)
  have hvanish := (FourierDense.Continuous.eq_zero_of_forall_integral_cc_eq_zero huc) μ ?_
  swap
  · intro f hfc hfs hf0
    have hfcℂ : Continuous fun x : G => ((f x : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp hfc
    have hfsℂ : HasCompactSupport fun x : G => ((f x : ℝ) : ℂ) :=
      hfs.comp_left Complex.ofReal_zero
    have h1 := hkey (fun x => ((f x : ℝ) : ℂ)) hfcℂ hfsℂ
    have hint1 : Integrable (fun x => ((f x : ℝ) : ℂ) * φ x) μ :=
      (hfcℂ.mul hφc).integrable_of_hasCompactSupport hfsℂ.mul_right
    have hint2 : Integrable (fun x => ((f x : ℝ) : ℂ)
        * conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀)) μ :=
      (hfcℂ.mul (Complex.continuous_conj.comp hψc)).integrable_of_hasCompactSupport
        hfsℂ.mul_right
    calc ∫ x, f x • (φ x - conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀)) ∂μ
        = ∫ x, (((f x : ℝ) : ℂ) * φ x
            - ((f x : ℝ) : ℂ) * conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show f x • (φ x - conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀)) = _
          rw [Complex.real_smul, mul_sub]
      _ = (∫ x, ((f x : ℝ) : ℂ) * φ x ∂μ)
            - ∫ x, ((f x : ℝ) : ℂ) * conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀) ∂μ :=
          integral_sub hint1 hint2
      _ = 0 := by rw [h1, sub_self]
  have hrep0 : ∀ x : G, φ x = conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀) := fun x =>
    sub_eq_zero.mp (hvanish x)
  -- push the measure forward by inversion of the dual group
  set e : PontryaginDual G ≃ᵐ PontryaginDual G :=
    (Homeomorph.inv (PontryaginDual G)).toMeasurableEquiv with hedef
  refine ⟨σ₀.map e, Measure.isFiniteMeasure_map σ₀ e, ?_, ?_⟩
  · -- regularity of the pushforward
    have hcoe : (⇑e : PontryaginDual G → PontryaginDual G)
        = ⇑(Homeomorph.inv (PontryaginDual G)) :=
      Homeomorph.toMeasurableEquiv_coe _
    rw [show σ₀.map ⇑e = σ₀.map ⇑(Homeomorph.inv (PontryaginDual G)) by rw [hcoe]]
    exact Measure.Regular.map (Homeomorph.inv (PontryaginDual G))
  · intro x
    rw [hrep0 x]
    calc conj (∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ₀)
        = ∫ χ : PontryaginDual G, conj ((χ x : Circle) : ℂ) ∂σ₀ := integral_conj.symm
      _ = ∫ χ : PontryaginDual G, ((e χ) x : ℂ) ∂σ₀ := by
          refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
          show conj ((χ x : Circle) : ℂ) = (((e χ) x : Circle) : ℂ)
          rw [← Circle.coe_inv_eq_conj]
          rfl
      _ = ∫ χ, (χ x : ℂ) ∂(σ₀.map e) :=
          (MeasureTheory.integral_map_equiv e fun χ : PontryaginDual G =>
            ((χ x : Circle) : ℂ)).symm

include μ in
/-- **Uniqueness in Bochner's theorem**: the representing measure of a function of positive
type is unique among finite regular measures. (Immediate from the Fourier–Stieltjes
uniqueness theorem; the positivity hypothesis is kept for the sake of the API.) -/
theorem _root_.OAI.Topology.Pontryagin.PositiveType.IsPositiveType.bochner_measure_unique (_hφ : PositiveType.IsPositiveType φ)
    {σ σ' : Measure (PontryaginDual G)} [IsFiniteMeasure σ] [IsFiniteMeasure σ']
    [σ.Regular] [σ'.Regular]
    (h : ∀ x : G, φ x = ∫ χ, (χ x : ℂ) ∂σ) (h' : ∀ x : G, φ x = ∫ χ, (χ x : ℂ) ∂σ') :
    σ = σ' :=
  FourierDense.PontryaginDual.measure_ext_of_forall_integral_char_eq μ fun x => (h x).symm.trans (h' x)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [BorelSpace (PontryaginDual G)] in
/-- **The total mass of the Bochner measure**: under the representation of Bochner's
theorem, `φ 1` is the (real, nonnegative) total mass of `σ`. -/
theorem _root_.OAI.Topology.Pontryagin.PositiveType.IsPositiveType.bochner_measure_mass (_hφ : PositiveType.IsPositiveType φ)
    {σ : Measure (PontryaginDual G)} [IsFiniteMeasure σ]
    (h : ∀ x : G, φ x = ∫ χ, (χ x : ℂ) ∂σ) :
    φ 1 = ((σ.real Set.univ : ℝ) : ℂ) := by
  rw [h 1]
  calc ∫ χ : PontryaginDual G, ((χ (1 : G) : Circle) : ℂ) ∂σ
      = ∫ _χ : PontryaginDual G, (1 : ℂ) ∂σ := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show ((χ (1 : G) : Circle) : ℂ) = 1
        rw [_root_.map_one, Circle.coe_one]
    _ = ((σ.real Set.univ : ℝ) : ℂ) := by
        rw [integral_const, Complex.real_smul, mul_one]

end

end OAI.Topology.Pontryagin.Bochner.MeasureTheory
