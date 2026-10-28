import OAI.Topology.Pontryagin.Convolution
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Positive Type -/

namespace OAI.Topology.Pontryagin.PositiveType

noncomputable section

/-!
# Functions of positive type on a locally compact abelian group

A function `f: G → ℂ` on a group `G` is of *positive type* (or *positive-definite*) if all the
finite matrices `(f ((x i)⁻¹ * x j))_{i j}` are positive semidefinite:

`0 ≤ ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)`

for all `x: Fin n → G` and `c: Fin n → ℂ`, the inequality being in the partial order of
`Complex.partialOrder` (available with `open scoped ComplexOrder`).

## Main definitions and results

* `IsPositiveType f`: the definition above.

Elementary consequences (pure algebra):

* `IsPositiveType.apply_one_nonneg`: `0 ≤ f 1`;
* `IsPositiveType.apply_inv`: `f x⁻¹ = conj (f x)` (hermitian symmetry);
* `IsPositiveType.norm_apply_le`: `‖f x‖ ≤ (f 1).re`;
* `isPositiveType_zero`, `IsPositiveType.add`, `IsPositiveType.smul_of_nonneg`: positive-type
 functions form a cone;
* `isPositiveType_char`: every continuous character is of positive type;
* `isPositiveType_integral_char`: `x ↦ ∫ χ, χ x ∂σ` is of positive type for every finite
 measure `σ` on the Pontryagin dual (one half of Bochner's theorem).

Convolution squares (with a regular Haar measure `μ`):

* `isPositiveType_mconv_mstar_of_memLp_two`: `g ⋆ g^*` is of positive type for `g ∈ L²(μ)`;
* `isPositiveType_mconv_mstar`: the same for continuous compactly supported `g`.

Uniform-continuity helpers (of independent use):

* `Continuous.exists_nhds_one_forall_norm_sub_le`: a continuous compactly supported function on
 a topological abelian group is uniformly continuous, in ε-neighborhood form;
* `Continuous.exists_nhds_one_forall_norm_sub_le_of_isCompact`: uniform continuity of an
 arbitrary continuous function on a compact set, in the same form.

The key bridge from finite sums to integrals, used by the Bochner layer:

* `IsPositiveType.integral_mconv_nonneg`: for `φ` continuous of positive type and `f`
 continuous compactly supported, `0 ≤ ∫ x, ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ`;
* `IsPositiveType.integral_mconv_mstar_mul_nonneg`: equivalently,
 `0 ≤ ∫ x, mconv μ (mstar f) f x * φ x ∂μ`.

The proof of `IsPositiveType.integral_mconv_nonneg` is a Riemann-sum approximation: the
compactly supported kernel is approximated, uniformly up to `ε`, by its values on a finite
Borel partition of `tsupport f` subordinate to translates of a small neighborhood of `1`, and
each Riemann sum is nonnegative by `IsPositiveType`. No product measures are used anywhere.
-/

open Function _root_.MeasureTheory Set _root_.Topology Filter
open scoped ENNReal Pointwise ComplexConjugate ComplexOrder Uniformity

-- The measure-theoretic sections deliberately use one coarse hypothesis block (locally compact
-- Hausdorff abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

/-! ### Definition and elementary consequences -/

section Algebra

variable {G : Type*} [CommGroup G]

/-- A function `f: G → ℂ` is of *positive type* if every matrix `(f ((x i)⁻¹ * x j))_{i j}` is
positive semidefinite. The inequality lives in the partial order of `ComplexOrder`; in
particular each such sum is real. -/
def IsPositiveType (f : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)

theorem IsPositiveType.apply_one_nonneg {f : G → ℂ} (hf : IsPositiveType f) : 0 ≤ f 1 := by
  simpa using hf 1 (fun _ => 1) fun _ => 1

/-- The `2 × 2` positivity condition, at the points `1` and `x`. -/
private theorem IsPositiveType.sum_two {f : G → ℂ} (hf : IsPositiveType f) (x : G)
    (c₁ c₂ : ℂ) :
    0 ≤ conj c₁ * c₁ * f 1 + conj c₁ * c₂ * f x + conj c₂ * c₁ * f x⁻¹ +
      conj c₂ * c₂ * f 1 := by
  have h := hf 2 ![1, x] ![c₁, c₂]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel] at h
  calc (0 : ℂ) ≤ _ := h
    _ = conj c₁ * c₁ * f 1 + conj c₁ * c₂ * f x + conj c₂ * c₁ * f x⁻¹ +
        conj c₂ * c₂ * f 1 := by ring

/-- A function of positive type is hermitian: `f x⁻¹ = conj (f x)`. -/
theorem IsPositiveType.apply_inv {f : G → ℂ} (hf : IsPositiveType f) (x : G) :
    f x⁻¹ = conj (f x) := by
  have him1 : (f 1).im = 0 := ((Complex.nonneg_iff.mp hf.apply_one_nonneg).2).symm
  have h1 := (IsPositiveType.sum_two hf) x 1 1
  have h2 := (IsPositiveType.sum_two hf) x 1 Complex.I
  simp only [map_one, one_mul, mul_one, Complex.conj_I] at h1 h2
  -- imaginary part of the first inequality: `im (f x) + im (f x⁻¹) = 0`
  have e1 : (f x).im + (f x⁻¹).im = 0 := by
    have := (Complex.nonneg_iff.mp h1).2
    simp only [Complex.add_im, him1] at this
    linarith
  -- imaginary part of the second inequality: `re (f x) - re (f x⁻¹) = 0`
  have e2 : (f x).re - (f x⁻¹).re = 0 := by
    have := (Complex.nonneg_iff.mp h2).2
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.mul_re, him1] at this
    linarith
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- A function of positive type attains its maximal modulus at `1`: `‖f x‖ ≤ (f 1).re`. -/
theorem IsPositiveType.norm_apply_le {f : G → ℂ} (hf : IsPositiveType f) (x : G) :
    ‖f x‖ ≤ (f 1).re := by
  have h1 : 0 ≤ (f 1).re := (Complex.nonneg_iff.mp hf.apply_one_nonneg).1
  rcases eq_or_ne (f x) 0 with h | h
  · simpa [h] using h1
  -- apply the `2 × 2` condition with `c₁ = ‖f x‖` and `c₂ = -conj (f x)`
  set N : ℂ := ((‖f x‖ : ℝ) : ℂ) with hN
  have key := (IsPositiveType.sum_two hf) x N (-conj (f x))
  have cm : conj (f x) * f x = N * N := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast [hN]
    ring
  have e : conj N * N * f 1 + conj N * (-conj (f x)) * f x + conj (-conj (f x)) * N * f x⁻¹ +
      conj (-conj (f x)) * (-conj (f x)) * f 1 = 2 * (N * N) * f 1 - 2 * (N * (N * N)) := by
    rw [hf.apply_inv x]
    simp only [map_neg, Complex.conj_conj, hN, Complex.conj_ofReal]
    linear_combination (f 1 - 2 * ((‖f x‖ : ℝ) : ℂ)) * cm
  rw [e] at key
  have key2 : 0 ≤ ((2 * ‖f x‖ * ‖f x‖ : ℝ) : ℂ) * f 1 - ((2 * ‖f x‖ * ‖f x‖ * ‖f x‖ : ℝ) : ℂ) := by
    convert key using 2 <;> · push_cast [hN]; ring
  have hre := (Complex.nonneg_iff.mp key2).1
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  have hp : 0 < ‖f x‖ := norm_pos_iff.mpr h
  have h2 : 0 < 2 * ‖f x‖ * ‖f x‖ := by positivity
  refine le_of_mul_le_mul_left ?_ h2
  linarith

theorem isPositiveType_zero : IsPositiveType (0 : G → ℂ) := by
  intro n x c
  simp

theorem IsPositiveType.add {f g : G → ℂ} (hf : IsPositiveType f) (hg : IsPositiveType g) :
    IsPositiveType (f + g) := by
  intro n x c
  have key : ∑ i, ∑ j, conj (c i) * c j * (f + g) ((x i)⁻¹ * x j) =
      (∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)) +
        ∑ i, ∑ j, conj (c i) * c j * g ((x i)⁻¹ * x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [key]
  exact add_nonneg (hf n x c) (hg n x c)

theorem IsPositiveType.smul_of_nonneg {f : G → ℂ} (hf : IsPositiveType f) {r : ℝ}
    (hr : 0 ≤ r) : IsPositiveType (r • f) := by
  intro n x c
  have key : ∑ i, ∑ j, conj (c i) * c j * (r • f) ((x i)⁻¹ * x j) =
      (r : ℂ) * ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [key]
  exact mul_nonneg (by exact_mod_cast hr) (hf n x c)

end Algebra

/-! ### Characters and integrals of characters are of positive type -/

section Characters

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The fundamental algebraic identity behind `isPositiveType_char`: the positive-type double
sum of a character is `conj S * S` for `S = ∑ i, c i * χ (x i)`. -/
private theorem sum_sum_char_eq (χ : PontryaginDual G) {n : ℕ} (x : Fin n → G)
    (c : Fin n → ℂ) :
    ∑ i, ∑ j, conj (c i) * c j * ((χ ((x i)⁻¹ * x j) : ℂ)) =
      conj (∑ i, c i * χ (x i)) * ∑ i, c i * χ (x i) := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hval : ((χ ((x i)⁻¹ * x j) : ℂ)) = conj ((χ (x i) : ℂ)) * (χ (x j) : ℂ) := by
    rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  rw [hval, map_mul]
  ring

/-- Continuous characters are of positive type. -/
theorem isPositiveType_char (χ : PontryaginDual G) :
    IsPositiveType (fun x => (χ x : ℂ)) := by
  intro n x c
  rw [sum_sum_char_eq χ x c]
  simpa only [starRingEnd_apply] using star_mul_self_nonneg (∑ i, c i * (χ (x i) : ℂ))

/-- One half of Bochner's theorem: for a finite measure `σ` on the Pontryagin dual, the
function `x ↦ ∫ χ, χ x ∂σ` is of positive type. -/
theorem isPositiveType_integral_char {mΓ : MeasurableSpace (PontryaginDual G)}
    [OpensMeasurableSpace (PontryaginDual G)] (σ : Measure (PontryaginDual G))
    [IsFiniteMeasure σ] :
    IsPositiveType (fun x => ∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ) := by
  intro n x c
  have hcont : ∀ z : G, Continuous fun χ : PontryaginDual G => (χ z : ℂ) := fun z => by
    refine continuous_subtype_val.comp ?_
    change Continuous fun χ : G →ₜ* Circle => χ z
    exact continuous_eval_const z
  have hint : ∀ z : G, Integrable (fun χ : PontryaginDual G => (χ z : ℂ)) σ := fun z => by
    refine (integrable_const (1 : ℝ)).mono' (hcont z).aestronglyMeasurable ?_
    exact Eventually.of_forall fun χ => (Circle.norm_coe (χ z)).le
  calc ∑ i, ∑ j, conj (c i) * c j * ∫ χ : PontryaginDual G, (χ ((x i)⁻¹ * x j) : ℂ) ∂σ
      = ∫ χ : PontryaginDual G, ∑ i, ∑ j, conj (c i) * c j * (χ ((x i)⁻¹ * x j) : ℂ) ∂σ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          ((hint _).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => ((hint _).const_mul _)]
        exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    _ = ∫ χ : PontryaginDual G, ((‖∑ i, c i * (χ (x i) : ℂ)‖ ^ 2 : ℝ) : ℂ) ∂σ := by
        congr 1
        funext χ
        rw [sum_sum_char_eq χ x c, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∫ χ : PontryaginDual G, ‖∑ i, c i * (χ (x i) : ℂ)‖ ^ 2 ∂σ : ℝ) : ℂ) :=
        integral_ofReal
    _ ≥ 0 := by
        rw [ge_iff_le, Complex.zero_le_real]
        exact integral_nonneg fun χ => sq_nonneg _

end Characters

/-! ### Convolution squares are of positive type -/

section ConvolutionSquare

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- For `g ∈ L²(μ)`, the convolution square `g ⋆ g^*` is of positive type. -/
theorem isPositiveType_mconv_mstar_of_memLp_two {g : G → ℂ} (hg : MemLp g 2 μ) :
    IsPositiveType (Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g)) := by
  intro n x c
  -- the summand functions `Q i = conj (c i) * g ((x i)⁻¹ * ·)`, all in `L²`
  set Q : Fin n → G → ℂ := fun i y => conj (c i) * g ((x i)⁻¹ * y) with hQdef
  have hQ : ∀ i, MemLp (Q i) 2 μ := fun i => (Translation.MeasureTheory.MemLp.mtranslate μ hg (x i)).const_mul _
  have hint : ∀ i j : Fin n, Integrable (fun y => Q i y * conj (Q j y)) μ := fun i j =>
    (hQ i).integrable_mul ((hQ j).star)
  -- each convolution value is an integral of a product of shifted copies of `g`
  have hterm : ∀ i j : Fin n, conj (c i) * c j * Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g) ((x i)⁻¹ * x j) =
      ∫ y, Q i y * conj (Q j y) ∂μ := by
    intro i j
    have h1 : Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g) ((x i)⁻¹ * x j) =
        ∫ y, g ((x i)⁻¹ * y) * conj (g ((x j)⁻¹ * y)) ∂μ := by
      calc Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g) ((x i)⁻¹ * x j)
          = ∫ y, g ((x i)⁻¹ * (x i * y)) * conj (g ((x j)⁻¹ * (x i * y))) ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            change g y * Convolution.MeasureTheory.mstar g (y⁻¹ * ((x i)⁻¹ * x j)) = _
            rw [Convolution.MeasureTheory.mstar_apply]
            congr 2
            · rw [inv_mul_cancel_left]
            · simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
        _ = ∫ y, g ((x i)⁻¹ * y) * conj (g ((x j)⁻¹ * y)) ∂μ :=
            integral_mul_left_eq_self
              (fun y => g ((x i)⁻¹ * y) * conj (g ((x j)⁻¹ * y))) (x i)
    rw [h1, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hQdef, map_mul, Complex.conj_conj]
    ring
  calc ∑ i, ∑ j, conj (c i) * c j * Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g) ((x i)⁻¹ * x j)
      = ∑ i, ∑ j, ∫ y, Q i y * conj (Q j y) ∂μ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ∫ y, ∑ i, ∑ j, Q i y * conj (Q j y) ∂μ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ =>
          (integral_finsetSum _ fun j _ => hint i j).symm
    _ = ∫ y, ((‖∑ i, Q i y‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        congr 1
        funext y
        rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∫ y, ‖∑ i, Q i y‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal
    _ ≥ 0 := by
        rw [ge_iff_le, Complex.zero_le_real]
        exact integral_nonneg fun y => sq_nonneg _

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- For continuous compactly supported `g`, the convolution square `g ⋆ g^*` is of positive
type. -/
theorem isPositiveType_mconv_mstar {g : G → ℂ} (hg : Continuous g)
    (hg' : HasCompactSupport g) : IsPositiveType (Convolution.MeasureTheory.mconv μ g (Convolution.MeasureTheory.mstar g)) :=
  isPositiveType_mconv_mstar_of_memLp_two μ (hg.memLp_of_hasCompactSupport hg')

end ConvolutionSquare

/-! ### Uniform-continuity helpers on a topological abelian group

A topological group carries no `UniformSpace` instance, so uniform continuity of continuous
compactly supported functions (and of continuous functions on compact sets) is packaged here
in explicit ε-neighborhood form, by locally installing the right uniformity
`IsTopologicalGroup.rightUniformSpace`. -/

section UniformHelpers

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  {E : Type*} [NormedAddCommGroup E]

/-- **Uniform continuity of continuous compactly supported functions**, ε-neighborhood form:
there is a neighborhood `W` of `1` such that `‖f (x * w) - f x‖ ≤ ε` for *all* `x: G` and all
`w ∈ W`. -/
theorem Continuous.exists_nhds_one_forall_norm_sub_le {f : G → E} (hf : Continuous f)
    (hf' : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ 𝓝 (1 : G), ∀ (x : G), ∀ w ∈ W, ‖f (x * w) - f x‖ ≤ ε := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have huc : UniformContinuous f := hf'.uniformContinuous_of_continuous hf
  have h2 : {p : G × G | dist (f p.1) (f p.2) < ε} ∈ 𝓤 G :=
    huc (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_one' G] at h2
  obtain ⟨V, hV, hVsub⟩ := Filter.mem_comap.mp h2
  refine ⟨V, hV, fun x w hw => ?_⟩
  have hmem : ((x, x * w) : G × G) ∈ (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V := by
    simpa [mul_inv_cancel_comm] using hw
  have := hVsub hmem
  rw [Set.mem_ofPred_eq, dist_eq_norm] at this
  rw [norm_sub_rev]
  exact this.le

/-- **Uniform continuity on a compact set**, ε-neighborhood form: for `φ` continuous and `L`
compact there is a neighborhood `W` of `1` with `‖φ (z * w) - φ z‖ ≤ ε` for all `z ∈ L` and
`w ∈ W`. -/
theorem Continuous.exists_nhds_one_forall_norm_sub_le_of_isCompact [LocallyCompactSpace G]
    {φ : G → E} (hφ : Continuous φ) {L : Set G} (hL : IsCompact L) {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ 𝓝 (1 : G), ∀ z ∈ L, ∀ w ∈ W, ‖φ (z * w) - φ z‖ ≤ ε := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  -- enlarge `L` by a compact neighborhood `C` of `1` so that `z * w` stays inside
  obtain ⟨C, hCcomp, hCmem⟩ := exists_compact_mem_nhds (1 : G)
  have hL' : IsCompact (L * C) := hL.mul hCcomp
  have huc : UniformContinuousOn φ (L * C) :=
    hL'.uniformContinuousOn_of_continuous hφ.continuousOn
  have h2 : {p : G × G | dist (φ p.1) (φ p.2) < ε} ∈ 𝓤 G ⊓ 𝓟 ((L * C) ×ˢ (L * C)) :=
    huc (Metric.dist_mem_uniformity hε)
  rw [Filter.mem_inf_principal] at h2
  rw [uniformity_eq_comap_nhds_one' G] at h2
  obtain ⟨V, hV, hVsub⟩ := Filter.mem_comap.mp h2
  refine ⟨V ∩ C, Filter.inter_mem hV hCmem, fun z hz w hw => ?_⟩
  have hz1 : z ∈ L * C := by
    have := Set.mul_mem_mul hz (mem_of_mem_nhds hCmem)
    rwa [mul_one] at this
  have hz2 : z * w ∈ L * C := Set.mul_mem_mul hz hw.2
  have hmem : ((z, z * w) : G × G) ∈
      (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V := by
    simpa [mul_inv_cancel_comm] using hw.1
  have := hVsub hmem ⟨hz1, hz2⟩
  rw [Set.mem_ofPred_eq, dist_eq_norm] at this
  rw [norm_sub_rev]
  exact this.le

end UniformHelpers

/-! ### The key bridge: from finite sums to integrals -/

section Bridge

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]

/-- A complex number that is approximated arbitrarily well by nonnegative complex numbers is
nonnegative. -/
private theorem complex_nonneg_of_forall_dist_le {z : ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ w : ℂ, 0 ≤ w ∧ ‖z - w‖ ≤ ε) : 0 ≤ z := by
  rw [Complex.nonneg_iff]
  constructor
  · by_contra hre
    push Not at hre
    obtain ⟨w, hw0, hd⟩ := h (-z.re / 2) (by linarith)
    have hwre : 0 ≤ w.re := (Complex.nonneg_iff.mp hw0).1
    have h1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := abs_le.mp (h1.trans hd)
    linarith [h2.1]
  · by_contra him
    have habs : 0 < |z.im| := abs_pos.mpr fun hh => him hh.symm
    obtain ⟨w, hw0, hd⟩ := h (|z.im| / 2) (by linarith)
    have hwim : 0 = w.im := (Complex.nonneg_iff.mp hw0).2
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← hwim, sub_zero] at h1
    have h2 := h1.trans hd
    linarith

omit [T2Space G] in
/-- The uniform kernel estimate for the Riemann-sum approximation: for `f` continuous with
compact support, `φ` continuous, and `δ > 0`, there is a neighborhood `W` of `1` such that the
kernel `(x, y) ↦ conj (f y) * f x * φ (y⁻¹ * x)` varies by at most `δ` when `x`, `y` range
over the `W`-translates `z • W`, `w • W` of base points `z, w ∈ tsupport f`. -/
private theorem exists_nhds_one_kernel_estimate {φ f : G → ℂ} (hφc : Continuous φ)
    (hf : Continuous f) (hf' : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W ∈ 𝓝 (1 : G), ∀ z ∈ tsupport f, ∀ w ∈ tsupport f, ∀ x ∈ z • W, ∀ y ∈ w • W,
      ‖conj (f y) * f x * φ (y⁻¹ * x) - conj (f w) * f z * φ (w⁻¹ * z)‖ ≤ δ := by
  have hK : IsCompact (tsupport f) := hf'
  have hL : IsCompact ((tsupport f)⁻¹ * tsupport f) := hK.inv.mul hK
  -- global bound for `f`, bound for `φ` on the compact set `K⁻¹ * K`
  obtain ⟨Cf₀, hCf₀⟩ := hf.bounded_above_of_compact_support hf'
  obtain ⟨Cφ₀, hCφ₀⟩ := hL.exists_bound_of_continuousOn hφc.continuousOn
  set Cf : ℝ := max Cf₀ 0 with hCfdef
  set Cφ : ℝ := max Cφ₀ 0 with hCφdef
  have hCf : ∀ u, ‖f u‖ ≤ Cf := fun u => (hCf₀ u).trans (le_max_left _ _)
  have hCφ : ∀ u ∈ (tsupport f)⁻¹ * tsupport f, ‖φ u‖ ≤ Cφ := fun u hu =>
    (hCφ₀ u hu).trans (le_max_left _ _)
  have hCf0 : 0 ≤ Cf := le_max_right _ _
  have hCφ0 : 0 ≤ Cφ := le_max_right _ _
  have hDpos : 0 < Cf * Cf + 2 * Cf * Cφ + 1 := by nlinarith
  set δ' : ℝ := δ / (Cf * Cf + 2 * Cf * Cφ + 1) with hδ'def
  have hδ' : 0 < δ' := div_pos hδ hDpos
  -- uniform continuity of `f` (globally) and of `φ` on `K⁻¹ * K`
  obtain ⟨W₁, hW₁mem, hW₁⟩ := (PositiveType.Continuous.exists_nhds_one_forall_norm_sub_le hf) hf' hδ'
  obtain ⟨W₂, hW₂mem, hW₂⟩ := (PositiveType.Continuous.exists_nhds_one_forall_norm_sub_le_of_isCompact hφc) hL hδ'
  obtain ⟨V, hVopen, hV1, hVsub⟩ := exists_open_nhds_one_mul_subset hW₂mem
  refine ⟨W₁ ∩ (V ∩ V⁻¹), Filter.inter_mem hW₁mem
    (Filter.inter_mem (hVopen.mem_nhds hV1)
      (inv_mem_nhds_one G (hVopen.mem_nhds hV1))), ?_⟩
  intro z hz w hw x hx y hy
  obtain ⟨v₁, hv₁, hv₁x⟩ := hx
  obtain ⟨v₂, hv₂, hv₂y⟩ := hy
  have hx1 : x = z * v₁ := hv₁x.symm
  have hy1 : y = w * v₂ := hv₂y.symm
  subst hx1 hy1
  -- the three elementary estimates
  have e1 : ‖f (z * v₁) - f z‖ ≤ δ' := hW₁ z v₁ hv₁.1
  have e2 : ‖f (w * v₂) - f w‖ ≤ δ' := hW₁ w v₂ hv₂.1
  have hzL : w⁻¹ * z ∈ (tsupport f)⁻¹ * tsupport f :=
    Set.mul_mem_mul (Set.inv_mem_inv.mpr hw) hz
  have hu : v₂⁻¹ * v₁ ∈ W₂ :=
    hVsub (Set.mul_mem_mul (Set.mem_inv.mp hv₂.2.2) hv₁.2.1)
  have harg : (w * v₂)⁻¹ * (z * v₁) = (w⁻¹ * z) * (v₂⁻¹ * v₁) := by
    simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  have e3 : ‖φ ((w * v₂)⁻¹ * (z * v₁)) - φ (w⁻¹ * z)‖ ≤ δ' := by
    rw [harg]
    exact hW₂ _ hzL _ hu
  have hφb : ‖φ (w⁻¹ * z)‖ ≤ Cφ := hCφ _ hzL
  -- telescoping and the final bound
  have decomp : conj (f (w * v₂)) * f (z * v₁) * φ ((w * v₂)⁻¹ * (z * v₁)) -
      conj (f w) * f z * φ (w⁻¹ * z) =
      conj (f (w * v₂)) * f (z * v₁) * (φ ((w * v₂)⁻¹ * (z * v₁)) - φ (w⁻¹ * z)) +
        (conj (f (w * v₂)) - conj (f w)) * f (z * v₁) * φ (w⁻¹ * z) +
          conj (f w) * (f (z * v₁) - f z) * φ (w⁻¹ * z) := by
    ring
  rw [decomp]
  have b1 : ‖conj (f (w * v₂)) * f (z * v₁) * (φ ((w * v₂)⁻¹ * (z * v₁)) - φ (w⁻¹ * z))‖ ≤
      Cf * Cf * δ' := by
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (mul_le_mul (hCf _) (hCf _) (norm_nonneg _) hCf0) e3 (norm_nonneg _)
      (mul_nonneg hCf0 hCf0)
  have b2 : ‖(conj (f (w * v₂)) - conj (f w)) * f (z * v₁) * φ (w⁻¹ * z)‖ ≤
      δ' * Cf * Cφ := by
    rw [norm_mul, norm_mul, ← map_sub, RCLike.norm_conj]
    exact mul_le_mul (mul_le_mul e2 (hCf _) (norm_nonneg _) hδ'.le) hφb (norm_nonneg _)
      (mul_nonneg hδ'.le hCf0)
  have b3 : ‖conj (f w) * (f (z * v₁) - f z) * φ (w⁻¹ * z)‖ ≤ Cf * δ' * Cφ := by
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (mul_le_mul (hCf _) e1 (norm_nonneg _) hCf0) hφb (norm_nonneg _)
      (mul_nonneg hCf0 hδ'.le)
  have hkey : δ' * (Cf * Cf + 2 * Cf * Cφ + 1) = δ := div_mul_cancel₀ _ hDpos.ne'
  calc ‖_ + _ + _‖ ≤ _ := norm_add₃_le
    _ ≤ Cf * Cf * δ' + δ' * Cf * Cφ + Cf * δ' * Cφ := by
        exact add_le_add (add_le_add b1 b2) b3
    _ ≤ δ := by nlinarith [hδ'.le]

end Bridge

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [T2Space G] [μ.Regular] in
/-- **The key bridge from finite-sum positivity to integral positivity.** For a continuous
function `φ` of positive type and a continuous compactly supported `f`,

`0 ≤ ∫ x, ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ`.

The proof approximates the (compactly supported, jointly continuous) kernel uniformly by its
values at base points of a finite disjoint Borel partition of `tsupport f` subordinate to
translates of a small neighborhood of `1`; the resulting Riemann sums are exactly the finite
sums appearing in `IsPositiveType φ`. -/
theorem IsPositiveType.integral_mconv_nonneg {φ : G → ℂ} (hφ : IsPositiveType φ)
    (hφc : Continuous φ) {f : G → ℂ} (hf : Continuous f) (hf' : HasCompactSupport f) :
    0 ≤ ∫ x, ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ := by
  classical
  -- the kernel is jointly continuous with compact support
  have hkc : Continuous (uncurry fun x y : G => conj (f y) * f x * φ (y⁻¹ * x)) :=
    ((Complex.continuous_conj.comp (hf.comp continuous_snd)).mul
      (hf.comp continuous_fst)).mul (hφc.comp (continuous_snd.inv.mul continuous_fst))
  have hksupp : HasCompactSupport (uncurry fun x y : G => conj (f y) * f x * φ (y⁻¹ * x)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hf'.isCompact.prod hf'.isCompact) ?_
    rintro ⟨x, y⟩ hp
    have hp' : conj (f y) * f x * φ (y⁻¹ * x) ≠ 0 := hp
    have h1 : f x ≠ 0 := fun h0 => hp' (by simp [h0])
    have h2 : f y ≠ 0 := fun h0 => hp' (by simp [h0])
    exact ⟨subset_tsupport f (mem_support.mpr h1), subset_tsupport f (mem_support.mpr h2)⟩
  set F : G → ℂ := fun x => ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ with hFdef
  have hFint : Integrable F μ := CcFubini.MeasureTheory.integrable_integral_right hkc hksupp
  refine complex_nonneg_of_forall_dist_le fun ε hε => ?_
  -- the constants of the approximation
  have hK : IsCompact (tsupport f) := hf'
  have hKmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  set a : ℝ := μ.real (tsupport f) with hadef
  have ha : 0 ≤ a := measureReal_nonneg
  have hεpos' : 0 < ε / ((a + 1) ^ 2) := by positivity
  obtain ⟨W, hWmem, hWest⟩ := exists_nhds_one_kernel_estimate hφc hf hf' hεpos'
  -- a finite cover of `tsupport f` by translates of `interior W`
  have hU1 : (1 : G) ∈ interior W := mem_interior_iff_mem_nhds.mpr hWmem
  have hcov : ∀ p ∈ tsupport f, p • interior W ∈ 𝓝 p := fun p _ =>
    (isOpen_interior.smul p).mem_nhds ⟨1, hU1, mul_one p⟩
  obtain ⟨t, htK, htcov⟩ := hK.elim_nhds_subcover (fun p => p • interior W) hcov
  set n := t.card with hndef
  set e : ↥t ≃ Fin n := Fintype.equivFinOfCardEq (Fintype.card_coe t) with hedef
  set z : Fin n → G := fun i => (e.symm i : G) with hzdef
  have hzK : ∀ i, z i ∈ tsupport f := fun i => htK _ (e.symm i).2
  have hcov' : ∀ p ∈ tsupport f, ∃ i, p ∈ z i • interior W := by
    intro p hp
    have hmem := htcov hp
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨q, hq, hpq⟩ := hmem
    exact ⟨e ⟨q, hq⟩, by simpa [hzdef] using hpq⟩
  -- the disjointified Borel partition of `tsupport f`
  set A : Fin n → Set G := fun i =>
    (tsupport f ∩ z i • interior W) \ ⋃ j : Fin n, ⋃ _ : j < i, z j • interior W with hAdef
  have hzUopen : ∀ i : Fin n, IsOpen (z i • interior W) := fun i => isOpen_interior.smul _
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i =>
    (hKmeas.inter (hzUopen i).measurableSet).diff
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => (hzUopen j).measurableSet)
  have hAK : ∀ i, A i ⊆ tsupport f := fun i p hp => hp.1.1
  have hAsub : ∀ i, A i ⊆ z i • W := fun i p hp =>
    Set.smul_set_mono interior_subset hp.1.2
  have hdisj : Pairwise (Disjoint on A) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.mpr fun p hpi hpj => ?_
      exact hpj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨h, hpi.1.2⟩⟩)
    · refine Set.disjoint_left.mpr fun p hpi hpj => ?_
      exact hpi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h, hpj.1.2⟩⟩)
  have hAUnion : ⋃ i, A i = tsupport f := by
    apply Set.Subset.antisymm (Set.iUnion_subset fun i => hAK i)
    intro p hp
    have hex : ∃ i, p ∈ z i • interior W := hcov' p hp
    set s : Finset (Fin n) := {i ∈ Finset.univ | p ∈ z i • interior W} with hsdef
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp [hsdef, hi]⟩
    have hi₀mem : p ∈ z (s.min' hs) • interior W := by
      have := s.min'_mem hs
      simp only [hsdef, Finset.mem_filter] at this
      exact this.2
    refine Set.mem_iUnion.mpr ⟨s.min' hs, ⟨⟨hp, hi₀mem⟩, ?_⟩⟩
    intro hcon
    simp only [Set.mem_iUnion] at hcon
    obtain ⟨j, hji, hpj⟩ := hcon
    have hle : s.min' hs ≤ j := Finset.min'_le s j (by simp [hsdef, hpj])
    exact absurd hji (not_lt.mpr hle)
  have hμA : ∀ i, μ (A i) ≠ ∞ := fun i =>
    (lt_of_le_of_lt (measure_mono (hAK i)) hK.measure_lt_top).ne
  -- the measures of the pieces sum to the measure of the support
  have hsum_meas : ∑ i, μ.real (A i) = a := by
    have h2 : μ (tsupport f) = ∑ i, μ (A i) := by
      rw [← hAUnion, measure_iUnion hdisj hAmeas, tsum_fintype]
    calc ∑ i, μ.real (A i) = ∑ i, (μ (A i)).toReal := rfl
      _ = (∑ i, μ (A i)).toReal := (ENNReal.toReal_sum fun i _ => hμA i).symm
      _ = (μ (tsupport f)).toReal := by rw [← h2]
      _ = a := rfl
  -- the Riemann sum, nonnegative by `IsPositiveType`
  set c : Fin n → ℂ := fun i => ((μ.real (A i) : ℝ) : ℂ) * f (z i) with hcdef
  refine ⟨∑ i, ∑ j, conj (c i) * c j * φ ((z i)⁻¹ * z j), hφ n z c, ?_⟩
  -- rewrite the Riemann sum in kernel form
  have hSalt : ∑ i, ∑ j, conj (c i) * c j * φ ((z i)⁻¹ * z j) =
      ∑ i, ∑ j, ((μ.real (A i) : ℝ) : ℂ) *
        (((μ.real (A j) : ℝ) : ℂ) * (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hcdef, map_mul, Complex.conj_ofReal]
    ring
  -- decompose the integral over the partition
  have hI : ∫ x, F x ∂μ = ∑ i, ∫ x in A i, F x ∂μ := by
    have h0 : ∀ x ∉ tsupport f, F x = 0 := fun x hx => by
      have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hFdef]
      simp [hfx]
    calc ∫ x, F x ∂μ
        = ∫ x in tsupport f, F x ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = ∫ x in ⋃ i, A i, F x ∂μ := by rw [hAUnion]
      _ = ∑' i, ∫ x in A i, F x ∂μ :=
          integral_iUnion hAmeas hdisj (by rw [hAUnion]; exact hFint.integrableOn)
      _ = ∑ i, ∫ x in A i, F x ∂μ := tsum_fintype _
  -- decompose each slice integral over the partition
  have hFx : ∀ x : G, F x = ∑ j, ∫ y in A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ := by
    intro x
    have h0 : ∀ y ∉ tsupport f, conj (f y) * f x * φ (y⁻¹ * x) = 0 := fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]
    have hxint : Integrable (fun y => conj (f y) * f x * φ (y⁻¹ * x)) μ :=
      (CcFubini.Continuous.integrable_uncurry_left hkc) hksupp x
    calc F x = ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ := rfl
      _ = ∫ y in tsupport f, conj (f y) * f x * φ (y⁻¹ * x) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = ∫ y in ⋃ j, A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ := by rw [hAUnion]
      _ = ∑' j, ∫ y in A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ :=
          integral_iUnion hAmeas hdisj (by rw [hAUnion]; exact hxint.integrableOn)
      _ = ∑ j, ∫ y in A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ := tsum_fintype _
  -- express the Riemann sum as a sum of set integrals of constants
  have hSint : ∑ i, ∑ j, conj (c i) * c j * φ ((z i)⁻¹ * z j) =
      ∑ i, ∫ _ in A i, (∑ j, ((μ.real (A j) : ℝ) : ℂ) *
        (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))) ∂μ := by
    rw [hSalt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_const, Complex.real_smul, Finset.mul_sum]
  -- the per-piece error bound
  have hbound : ∀ i, ‖(∫ x in A i, F x ∂μ) -
      ∫ _ in A i, (∑ j, ((μ.real (A j) : ℝ) : ℂ) *
        (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))) ∂μ‖ ≤
      ε / ((a + 1) ^ 2) * a * μ.real (A i) := by
    intro i
    rw [← integral_sub hFint.integrableOn (integrableOn_const (hμA i))]
    refine norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono (hAK i)) hK.measure_lt_top) ?_
    intro x hx
    rw [hFx x, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j, ‖(∫ y in A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ) -
        ((μ.real (A j) : ℝ) : ℂ) * (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))‖ ≤
        ε / ((a + 1) ^ 2) * μ.real (A j) := by
      intro j
      have hconst : ((μ.real (A j) : ℝ) : ℂ) *
          (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i)) =
          ∫ _ in A j, conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i) ∂μ := by
        rw [setIntegral_const, Complex.real_smul]
      rw [hconst, ← integral_sub (((CcFubini.Continuous.integrable_uncurry_left hkc) hksupp x).integrableOn)
        (integrableOn_const (hμA j))]
      refine norm_setIntegral_le_of_norm_le_const
        (lt_of_le_of_lt (measure_mono (hAK j)) hK.measure_lt_top) ?_
      intro y hy
      exact hWest (z i) (hzK i) (z j) (hzK j) x (hAsub i hx) y (hAsub j hy)
    calc ∑ j, ‖(∫ y in A j, conj (f y) * f x * φ (y⁻¹ * x) ∂μ) -
          ((μ.real (A j) : ℝ) : ℂ) * (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))‖
        ≤ ∑ j, ε / ((a + 1) ^ 2) * μ.real (A j) := Finset.sum_le_sum fun j _ => hterm j
      _ = ε / ((a + 1) ^ 2) * a := by rw [← Finset.mul_sum, hsum_meas]
  -- assemble
  rw [hI, hSint, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(∫ x in A i, F x ∂μ) -
        ∫ _ in A i, (∑ j, ((μ.real (A j) : ℝ) : ℂ) *
          (conj (f (z j)) * f (z i) * φ ((z j)⁻¹ * z i))) ∂μ‖
      ≤ ∑ i, ε / ((a + 1) ^ 2) * a * μ.real (A i) := Finset.sum_le_sum fun i _ => hbound i
    _ = ε / ((a + 1) ^ 2) * a * a := by rw [← Finset.mul_sum, hsum_meas]
    _ ≤ ε := by
        have h2 : a * a ≤ (a + 1) ^ 2 := by nlinarith
        calc ε / ((a + 1) ^ 2) * a * a = ε / ((a + 1) ^ 2) * (a * a) := by ring
          _ ≤ ε / ((a + 1) ^ 2) * ((a + 1) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 hεpos'.le
          _ = ε := div_mul_cancel₀ _ (by positivity)

omit [T2Space G] in
/-- Corollary form of the bridge, as used by the Bochner layer: for `φ` continuous of positive
type and `f` continuous compactly supported, `0 ≤ ∫ x, ((mstar f) ⋆ f) x * φ x ∂μ`. -/
theorem IsPositiveType.integral_mconv_mstar_mul_nonneg {φ : G → ℂ} (hφ : IsPositiveType φ)
    (hφc : Continuous φ) {f : G → ℂ} (hf : Continuous f) (hf' : HasCompactSupport f) :
    0 ≤ ∫ x, Convolution.MeasureTheory.mconv μ (Convolution.MeasureTheory.mstar f) f x * φ x ∂μ := by
  -- the two kernels for the iterated-integral swaps
  have hk₂c : Continuous (uncurry fun x y : G => Convolution.MeasureTheory.mstar f y * f (y⁻¹ * x) * φ x) :=
    (Convolution.MeasureTheory.mconv_kernel_continuous (Convolution.Continuous.mstar hf) hf).mul (hφc.comp continuous_fst)
  have hk₂supp : HasCompactSupport (uncurry fun x y : G => Convolution.MeasureTheory.mstar f y * f (y⁻¹ * x) * φ x) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (((Convolution.HasCompactSupport.mstar hf').isCompact.mul hf'.isCompact).prod (Convolution.HasCompactSupport.mstar hf').isCompact) ?_
    rintro ⟨x, y⟩ hp
    exact Convolution.MeasureTheory.mconv_kernel_support_subset (left_ne_zero_of_mul hp)
  have hk₃c : Continuous (uncurry fun y x : G => conj (f y) * f x * φ (y⁻¹ * x)) :=
    ((Complex.continuous_conj.comp (hf.comp continuous_fst)).mul
      (hf.comp continuous_snd)).mul (hφc.comp (continuous_fst.inv.mul continuous_snd))
  have hk₃supp : HasCompactSupport (uncurry fun y x : G => conj (f y) * f x * φ (y⁻¹ * x)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hf'.isCompact.prod hf'.isCompact) ?_
    rintro ⟨y, x⟩ hp
    have hp' : conj (f y) * f x * φ (y⁻¹ * x) ≠ 0 := hp
    have h1 : f y ≠ 0 := fun h0 => hp' (by simp [h0])
    have h2 : f x ≠ 0 := fun h0 => hp' (by simp [h0])
    exact ⟨subset_tsupport f (mem_support.mpr h1), subset_tsupport f (mem_support.mpr h2)⟩
  calc (0 : ℂ)
      ≤ ∫ x, ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ :=
        hφ.integral_mconv_nonneg μ hφc hf hf'
    _ = ∫ y, ∫ x, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ :=
        (integral_integral_swap_of_hasCompactSupport hk₃c hk₃supp).symm
    _ = ∫ y, ∫ x, conj (f y) * f (y * x) * φ (y⁻¹ * (y * x)) ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact (integral_mul_left_eq_self (fun x => conj (f y) * f x * φ (y⁻¹ * x)) y).symm
    _ = ∫ y, ∫ x, Convolution.MeasureTheory.mstar f y⁻¹ * f ((y⁻¹)⁻¹ * x) * φ x ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [Convolution.MeasureTheory.mstar_apply, inv_inv, inv_mul_cancel_left]
    _ = ∫ y, ∫ x, Convolution.MeasureTheory.mstar f y * f (y⁻¹ * x) * φ x ∂μ ∂μ :=
        integral_inv_eq_self (fun y => ∫ x, Convolution.MeasureTheory.mstar f y * f (y⁻¹ * x) * φ x ∂μ) μ
    _ = ∫ x, ∫ y, Convolution.MeasureTheory.mstar f y * f (y⁻¹ * x) * φ x ∂μ ∂μ :=
        (integral_integral_swap_of_hasCompactSupport hk₂c hk₂supp).symm
    _ = ∫ x, Convolution.MeasureTheory.mconv μ (Convolution.MeasureTheory.mstar f) f x * φ x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact integral_mul_const (φ x) _

end

end OAI.Topology.Pontryagin.PositiveType
