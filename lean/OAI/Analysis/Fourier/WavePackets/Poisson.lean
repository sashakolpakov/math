import OAI.Analysis.Fourier.WavePackets.Periodic

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open Topology
open scoped Pointwise ENNReal RealInnerProductSpace FourierTransform

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def unitCell (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

def torusProjection {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : UnitAddTorus (Fin n) :=
  fun i => (x i : UnitAddCircle)

theorem continuous_torusProjection {n : ℕ} : Continuous (@torusProjection n) := by
  apply continuous_pi
  intro i
  exact continuous_quotient_mk'.comp (PiLp.continuous_apply 2 _ i)

theorem torusProjection_add_integerVector {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (k : Fin n → ℤ) : torusProjection (integerVector k + x) = torusProjection x := by
  ext i
  simp [torusProjection, integerVector]

theorem integral_eq_tsum_unitCell {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) :
    (∫ x, f x) = ∑' k : Fin n → ℤ, ∫ x in unitCell n, f (integerVector k + x) := by
  have : Countable (Submodule.span ℤ
      (Set.range ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).toAddSubgroup :=
    inferInstanceAs (Countable (integerLattice n))
  rw [(ZSpan.isAddFundamentalDomain'
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis volume).integral_eq_tsum'' f hf]
  exact (integerLatticeEquiv n).tsum_eq _ |>.symm

theorem lintegral_eq_tsum_unitCell {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    (∫⁻ x, f x) = ∑' k : Fin n → ℤ, ∫⁻ x in unitCell n, f (integerVector k + x) := by
  have : Countable (Submodule.span ℤ
      (Set.range ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).toAddSubgroup :=
    inferInstanceAs (Countable (integerLattice n))
  rw [(ZSpan.isAddFundamentalDomain'
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis volume).lintegral_eq_tsum'' f]
  exact (integerLatticeEquiv n).tsum_eq _ |>.symm

theorem integral_torus_eq_unitCell {n : ℕ} (f : UnitAddTorus (Fin n) → ℂ) :
    (∫ x, f x) = ∫ x in unitCell n, f (torusProjection x) := by
  rw [UnitAddTorus.integral_preimage f (fun _ => 0)]
  have hbox : (volume : Measure (Fin n → ℝ)).restrict
      {x | ∀ i, x i ∈ Set.Ioc 0 (0 + 1)} =
      volume.restrict {x | ∀ i, x i ∈ Set.Ico 0 1} := by
    have hset (s : Set ℝ) : {x : Fin n → ℝ | ∀ i, x i ∈ s} = Set.univ.pi (fun _ => s) := by
      ext x
      simp
    rw [hset, hset]
    change (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Set.Ioc 0 (0 + 1)) =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Set.Ico 0 1)
    simp_rw [Measure.restrict_pi_pi, zero_add, ← restrict_Ico_eq_restrict_Ioc]
  rw [hbox]
  have hpres := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding
    (fun x => f (fun i => (x i : UnitAddCircle))) {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ico 0 1}
  convert hpres.symm using 1
  have hcell : unitCell n = WithLp.ofLp ⁻¹'
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ico 0 1} := by
    ext x
    simp [unitCell, ZSpan.fundamentalDomain]
  rw [hcell]
  rfl

/-- Fourier transform samples in the convention with the character `exp(-2π i k·x)`. -/
noncomputable def latticeFourierSample {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-k) (torusProjection x) * f x

theorem integrable_lattice_character_mul {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (k : Fin n → ℤ) :
    Integrable (fun x => UnitAddTorus.mFourier k (torusProjection x) * f x) := by
  exact hf.bdd_mul ((UnitAddTorus.mFourier k).continuous.comp
    continuous_torusProjection).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_mFourier_apply k (torusProjection x)).le)

/-- The Fourier coefficients of an integrable lattice periodization are the
Euclidean Fourier transform sampled on the dual lattice. -/
theorem mFourierCoeff_periodization {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (F : UnitAddTorus (Fin n) → ℂ)
    (hF : ∀ x, F (torusProjection x) = ∑' k : Fin n → ℤ, f (integerVector k + x))
    (m : Fin n → ℤ) : UnitAddTorus.mFourierCoeff F m = latticeFourierSample f m := by
  let g : EuclideanSpace ℝ (Fin n) → ℂ := fun x =>
    UnitAddTorus.mFourier (-m) (torusProjection x) * f x
  have hg : Integrable g := integrable_lattice_character_mul hf (-m)
  have hgshift (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
      g (integerVector k + x) = UnitAddTorus.mFourier (-m) (torusProjection x) *
        f (integerVector k + x) := by simp [g, torusProjection_add_integerVector]
  change (∫ x, UnitAddTorus.mFourier (-m) x * F x) = ∫ x, g x
  rw [integral_torus_eq_unitCell, integral_eq_tsum_unitCell hg]
  simp_rw [hF, ← tsum_mul_left, ← hgshift]
  apply integral_tsum
  · intro k
    exact (hg.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left volume (integerVector k))).restrict
  · rw [← lintegral_eq_tsum_unitCell (fun x => ‖g x‖ₑ)]
    exact hg.hasFiniteIntegral.ne

/-- Multidimensional Poisson summation for an integrable function whose
periodization is continuous and whose dual-lattice samples are summable. -/
theorem poisson_of_continuous_periodization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f)
    (F : C(UnitAddTorus (Fin n), ℂ))
    (hF : ∀ x, F (torusProjection x) = ∑' k : Fin n → ℤ, f (integerVector k + x))
    (hs : Summable (latticeFourierSample f)) (x : EuclideanSpace ℝ (Fin n)) :
    (∑' k : Fin n → ℤ, f (integerVector k + x)) =
      ∑' k : Fin n → ℤ, latticeFourierSample f k *
        UnitAddTorus.mFourier k (torusProjection x) := by
  have hcoeff := mFourierCoeff_periodization hf F hF
  have heq : UnitAddTorus.mFourierCoeff F = latticeFourierSample f := funext hcoeff
  have hs' : Summable (UnitAddTorus.mFourierCoeff F) := heq ▸ hs
  rw [← hF]
  simpa only [hcoeff, smul_eq_mul] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs' (torusProjection x)).tsum_eq.symm

theorem torusProjection_surjective {n : ℕ} : Function.Surjective (@torusProjection n) := by
  intro x
  choose y hy using fun i => Quotient.exists_rep (x i)
  refine ⟨WithLp.toLp 2 y, ?_⟩
  ext i
  exact hy i

theorem isQuotientMap_torusProjection {n : ℕ} : IsQuotientMap (@torusProjection n) := by
  apply IsOpenMap.isQuotientMap _ continuous_torusProjection torusProjection_surjective
  change IsOpenMap ((Pi.map fun _ : Fin n => ((↑) : ℝ → UnitAddCircle)) ∘ WithLp.ofLp)
  exact (IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall fun _ => Quotient.mk''_surjective)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isOpenMap

theorem torusProjection_fiber {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (h : torusProjection x = torusProjection y) :
    ∃ k : Fin n → ℤ, x = integerVector k + y := by
  have hi (i : Fin n) : ∃ k : ℤ, (k : ℝ) = x i - y i := by
    have hzero : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      simpa [torusProjection] using sub_eq_zero.mpr (congrFun h i)
    simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff 1).mp hzero
  choose k hk using hi
  refine ⟨k, ?_⟩
  ext i
  change x i = (k i : ℝ) + y i
  linarith [hk i]

theorem integerVector_add {n : ℕ} (k l : Fin n → ℤ) :
    integerVector (k + l) = integerVector k + integerVector l := by
  ext i
  simp [integerVector]

theorem lattice_sum_periodic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑' l : Fin n → ℤ, f (integerVector l + (integerVector k + x))) =
      ∑' l : Fin n → ℤ, f (integerVector l + x) := by
  simpa only [Equiv.coe_addRight, integerVector_add, add_assoc] using
    (Equiv.addRight k).tsum_eq (fun l : Fin n → ℤ => f (integerVector l + x))

/-- Local normal convergence allows the periodized sum to descend continuously
to the torus. This is a construction, rather than an assumed periodic extension. -/
theorem exists_continuous_periodization {n : ℕ} (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hs : ∀ K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)),
      Summable fun k : Fin n → ℤ =>
        ‖(f.comp (ContinuousMap.addLeft (integerVector k))).restrict K‖) :
    ∃ F : C(UnitAddTorus (Fin n), ℂ), ∀ x,
      F (torusProjection x) = ∑' k : Fin n → ℤ, f (integerVector k + x) := by
  classical
  let g : C(EuclideanSpace ℝ (Fin n), ℂ) :=
    ∑' k : Fin n → ℤ, f.comp (ContinuousMap.addLeft (integerVector k))
  have hg (x : EuclideanSpace ℝ (Fin n)) :
      g x = ∑' k : Fin n → ℤ, f (integerVector k + x) := by
    exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hs) x).symm
  let F : UnitAddTorus (Fin n) → ℂ := fun x => g (torusProjection_surjective x).choose
  have hF (x : EuclideanSpace ℝ (Fin n)) : F (torusProjection x) = g x := by
    have hq := (torusProjection_surjective (torusProjection x)).choose_spec
    obtain ⟨k, hk⟩ := torusProjection_fiber hq
    dsimp [F]
    rw [hk, hg, lattice_sum_periodic, ← hg]
  have hc : Continuous F := isQuotientMap_torusProjection.continuous_iff.mpr (by
    have heq : F ∘ torusProjection = g := funext hF
    rw [heq]
    exact g.continuous)
  exact ⟨⟨F, hc⟩, fun x => (hF x).trans (hg x)⟩

theorem summable_integerWeight (n M : ℕ) (hM : Module.finrank ℤ (integerLattice n) < M) :
    Summable (fun k : Fin n → ℤ => ((1 + ‖integerVector k‖) ^ M)⁻¹) := by
  classical
  have hs0 : Summable (Pi.single (0 : integerLattice n) (1 : ℝ)) :=
    (hasSum_single 0 (by intro b hb; simp [hb])).summable
  have hs := hs0.add
    (ZLattice.summable_norm_pow_inv (integerLattice n) M hM)
  have hw : Summable (fun z : integerLattice n => ((1 + ‖z‖) ^ M)⁻¹) := by
    apply hs.of_nonneg_of_le (fun z => by positivity)
    intro z
    by_cases hz : z = 0
    · subst z
      simp only [norm_zero, add_zero, one_pow, inv_one, Pi.single_eq_same]
      exact le_add_of_nonneg_right (pow_nonneg (by simp) M)
    · simp only [Pi.single_eq_of_ne hz, zero_add]
      simpa only [inv_pow] using (inv_le_inv₀ (by positivity : 0 < (1 + ‖z‖) ^ M)
        (pow_pos (norm_pos_iff.mpr hz) M)).mpr
        (pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) M)
  convert hw.comp_injective (integerLatticeEquiv n).injective using 1
  funext k
  rfl

/-- Schwartz decay gives locally normal convergence of all lattice translates. -/
theorem schwartz_lattice_locally_summable {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n))) :
    Summable (fun k : Fin n → ℤ =>
      ‖(f.toContinuousMap.comp (ContinuousMap.addLeft (integerVector k))).restrict K‖) := by
  classical
  let M := Module.finrank ℤ (integerLattice n) + 1
  let C := 2 ^ M * ((Finset.Iic (M, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f
  have hC : 0 ≤ C := by positivity
  have hb (x : EuclideanSpace ℝ (Fin n)) : (1 + ‖x‖) ^ M * ‖f x‖ ≤ C := by
    simpa [C] using (SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0) le_rfl le_rfl f x)
  obtain ⟨R, hR, hbound⟩ := K.isCompact.isBounded.exists_pos_norm_le
  have hmajor (k : Fin n → ℤ) (x : K) :
      ‖f (integerVector k + x)‖ ≤ C * (1 + R) ^ M * ((1 + ‖integerVector k‖) ^ M)⁻¹ := by
    have hnorm : 1 + ‖integerVector k‖ ≤ (1 + R) * (1 + ‖integerVector k + x‖) := by
      have ht := norm_sub_le (integerVector k + (x : EuclideanSpace ℝ (Fin n))) x
      have hx := hbound x x.property
      simp only [add_sub_cancel_right] at ht
      nlinarith [norm_nonneg (integerVector k + (x : EuclideanSpace ℝ (Fin n)))]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖integerVector k‖) hnorm M
    rw [mul_pow] at hp
    have hmul := mul_le_mul_of_nonneg_right hp (norm_nonneg (f (integerVector k + x)))
    have hdecay := mul_le_mul_of_nonneg_left (hb (integerVector k + x))
      (pow_nonneg (by linarith : 0 ≤ 1 + R) M)
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith
  apply ((summable_integerWeight n M (by dsimp [M]; omega)).mul_left (C * (1 + R) ^ M)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact hmajor k x

theorem mFourier_torusProjection {n : ℕ} (k : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (torusProjection x) =
      Complex.exp (((2 * Real.pi * ⟪x, integerVector k⟫ : ℝ) : ℂ) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, integerVector, RCLike.inner_apply,
    starRingEnd_apply, star_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem latticeFourierSample_eq_fourier {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (k : Fin n → ℤ) :
    latticeFourierSample f k = 𝓕 f (integerVector k) := by
  rw [latticeFourierSample, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mFourier_torusProjection]
  have hneg : integerVector (-k) = -integerVector k := by ext i; simp [integerVector]
  simp only [hneg, inner_neg_right, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul]
  congr 2
  ring

theorem summable_schwartz_lattice {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable (fun k : Fin n → ℤ => f (integerVector k)) := by
  have hs := ContinuousMap.summable_of_locally_summable_norm (schwartz_lattice_locally_summable f)
  have ha := ((ContinuousMap.evalCLM ℂ (0 : EuclideanSpace ℝ (Fin n))).hasSum hs.hasSum).summable
  convert ha using 1
  funext k
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addLeft,
    add_zero]
  rfl

theorem summable_norm_schwartz_lattice_add {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ => ‖f (integerVector k + x)‖) := by
  let K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)) :=
    ⟨{x}, isCompact_singleton⟩
  apply (schwartz_lattice_locally_summable f K).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  exact ((f.toContinuousMap.comp (ContinuousMap.addLeft (integerVector k))).restrict K).norm_coe_le_norm
    ⟨x, rfl⟩

/-- Poisson summation on the full Euclidean integer lattice, in every finite dimension. -/
theorem schwartz_poisson {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑' k : Fin n → ℤ, f (integerVector k + x)) =
      ∑' k : Fin n → ℤ, 𝓕 f (integerVector k) *
        UnitAddTorus.mFourier k (torusProjection x) := by
  obtain ⟨F, hF⟩ := exists_continuous_periodization f.toContinuousMap
    (schwartz_lattice_locally_summable f)
  have hs : Summable (latticeFourierSample (f : EuclideanSpace ℝ (Fin n) → ℂ)) := by
    convert summable_schwartz_lattice (𝓕 f) using 1
    funext k
    rw [latticeFourierSample_eq_fourier, SchwartzMap.fourier_coe]
  simpa only [latticeFourierSample_eq_fourier, ← SchwartzMap.fourier_coe] using
    poisson_of_continuous_periodization f.integrable F hF hs x

end OAI.Analysis.Fourier.WavePackets
