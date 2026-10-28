import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dual Polars -/

namespace OAI.Topology.Pontryagin.DualPolars

noncomputable section

open _root_.Circle
open _root_.PontryaginDual

/-!
# Polars in the Pontryagin dual, and the topology of the dual group

This file studies the compact-open topology of `PontryaginDual G` (`= G →ₜ* Circle`) for a
topological abelian group `G`.

## Main definitions and results

* `Circle.closure_centeredArc`: for `0 < r ≤ π`, the closure of the open arc
 `Circle.centeredArc r` is the closed arc `{z | |Complex.arg z| ≤ r}`.
* `Circle.abs_arg_le_div_of_pow_mem_centeredArc`: quantitative power control on the circle:
 if `z, z ^ 2, …, z ^ m` all lie in the closed quarter arc, then `|Complex.arg z| ≤ π / (4 * m)`.
* `Circle.norm_coe_sub_one_le_abs_arg`: the chord is shorter than the arc:
 `‖(z: ℂ) - 1‖ ≤ |Complex.arg z|`.
* `PontryaginDual.polar S`: the set of characters mapping `S` into the closed quarter arc
 `closure (Circle.centeredArc (π / 4))`.
* `PontryaginDual.isCompact_polar`: the polar of a neighborhood of `1` in `G` is compact
 (equicontinuity + Arzelà–Ascoli). No local compactness of `G` is needed.
* `PontryaginDual.hasBasis_nhds_one`: the sets `{χ | ∀ x ∈ K, χ x ∈ Circle.centeredArc r}`,
 for `K ⊆ G` compact and `0 < r ≤ π`, form a neighborhood basis of `1` in `PontryaginDual G`;
 `PontryaginDual.hasBasis_nhds` is the version translated to an arbitrary character.
* `PontryaginDual.eventually_uniform_arc`: characters near `1` are uniformly close to `1` on
 compact sets, in the norm of `ℂ`.
-/

open Filter Function Real Set _root_.Topology

namespace Circle

/-- For `0 < r ≤ π`, the closure of the open centered arc of half-length `r` is the
corresponding closed arc `{z | |Complex.arg z| ≤ r}`. -/
theorem closure_centeredArc {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π) :
    closure (centeredArc r) = {z : Circle | |Complex.arg z| ≤ r} := by
  have himg : Circle.exp '' Icc (-r) r = {z : Circle | |Complex.arg z| ≤ r} := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      rcases eq_or_lt_of_le ((neg_le_neg hrπ).trans ht1) with heq | hlt
      · have hrpi : π ≤ r := by rw [← heq] at ht1; linarith
        have hexp : Circle.exp t = Circle.exp π := by
          rw [← heq, show -π = π - 2 * π by ring, Circle.exp_sub_two_pi]
        simp only [Set.mem_ofPred_eq, hexp,
          Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl]
        rw [abs_of_nonneg Real.pi_nonneg]
        linarith
      · simp only [Set.mem_ofPred_eq, Circle.arg_exp hlt (ht2.trans hrπ)]
        exact abs_le.mpr ⟨ht1, ht2⟩
    · intro hz
      exact ⟨Complex.arg z, abs_le.mp hz, Circle.exp_arg z⟩
  rw [← himg]
  refine Set.Subset.antisymm
    (closure_minimal (Set.image_mono fun t ht ↦ ?_)
      ((isCompact_Icc.image Circle.exp.continuous).isClosed)) ?_
  · exact abs_le.mp ht.le
  · rw [show Icc (-r) r = closure (Ioo (-r) r) from (closure_Ioo (by linarith)).symm]
    refine (image_closure_subset_closure_image Circle.exp.continuous).trans (closure_mono ?_)
    exact Set.image_mono fun t ht ↦ abs_lt.mpr ⟨ht.1, ht.2⟩

theorem mem_closure_centeredArc {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π) {z : Circle} :
    z ∈ closure (centeredArc r) ↔ |Complex.arg z| ≤ r := by
  rw [closure_centeredArc hr hrπ]
  exact Iff.rfl

/-- Quantitative power control on the circle: if `z, z ^ 2, …, z ^ m` all lie in the closed
quarter arc `closure (centeredArc (π / 4))`, then `|Complex.arg z| ≤ π / (4 * m)`. -/
theorem abs_arg_le_div_of_pow_mem_centeredArc {z : Circle} {m : ℕ} (hm : 0 < m)
    (h : ∀ k, 1 ≤ k → k ≤ m → z ^ k ∈ closure (Circle.centeredArc (π / 4))) :
    |Complex.arg z| ≤ π / (4 * m) := by
  have hπ := Real.pi_pos
  have hmem : ∀ k, 1 ≤ k → k ≤ m → |Complex.arg ((z ^ k : Circle) : ℂ)| ≤ π / 4 := fun k h1 h2 ↦
    (mem_closure_centeredArc (by positivity) (by linarith)).mp (h k h1 h2)
  have h1 : |Complex.arg (z : ℂ)| ≤ π / 4 := by simpa using hmem 1 le_rfl hm
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ m → (k : ℝ) * |Complex.arg (z : ℂ)| ≤ π / 4 := by
    intro k
    induction k with
    | zero => exact fun hk ↦ absurd hk (by omega)
    | succ n ih =>
      intro _ hnm
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using h1
      · have hih : (n : ℝ) * |Complex.arg (z : ℂ)| ≤ π / 4 := ih hn (Nat.le_of_succ_le hnm)
        have hcast : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        have habs : |((n : ℝ) + 1) * Complex.arg (z : ℂ)| ≤ π / 2 := by
          rw [abs_mul, abs_of_nonneg hcast, add_mul, one_mul]
          linarith
        obtain ⟨hb1, hb2⟩ := abs_le.mp habs
        have hzpow : (z ^ (n + 1) : Circle)
            = Circle.exp (((n : ℝ) + 1) * Complex.arg (z : ℂ)) := by
          rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ← nsmul_eq_mul,
            Circle.exp_nsmul, Circle.exp_arg]
        have harg : Complex.arg ((z ^ (n + 1) : Circle) : ℂ)
            = ((n : ℝ) + 1) * Complex.arg (z : ℂ) := by
          rw [hzpow]
          exact Circle.arg_exp (by linarith) (by linarith)
        have hle := hmem (n + 1) (by omega) hnm
        rw [harg, abs_mul, abs_of_nonneg hcast] at hle
        calc ((n + 1 : ℕ) : ℝ) * |Complex.arg (z : ℂ)|
            = ((n : ℝ) + 1) * |Complex.arg (z : ℂ)| := by push_cast; ring
          _ ≤ π / 4 := hle
  have hfin := key m hm le_rfl
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (m : ℝ))]
  calc |Complex.arg (z : ℂ)| * (4 * (m : ℝ))
      = 4 * ((m : ℝ) * |Complex.arg (z : ℂ)|) := by ring
    _ ≤ 4 * (π / 4) := by linarith
    _ = π := by ring

/-- The chord is shorter than the arc: `‖(z: ℂ) - 1‖ ≤ |Complex.arg z|`. -/
theorem norm_coe_sub_one_le_abs_arg (z : Circle) :
    ‖(z : ℂ) - 1‖ ≤ |Complex.arg z| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := Complex.arg (z : ℂ))
  rwa [mul_comm, ← Circle.coe_exp, Circle.exp_arg, Real.norm_eq_abs] at h

end Circle

namespace PontryaginDual

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

instance : ContinuousEvalConst (PontryaginDual G) G Circle :=
  inferInstanceAs (ContinuousEvalConst (G →ₜ* Circle) G Circle)

/-- The polar of a set `S ⊆ G`: the set of characters mapping `S` into the closed quarter
arc `closure (Circle.centeredArc (π / 4))`. -/
def polar (S : Set G) : Set (PontryaginDual G) :=
  {χ | ∀ x ∈ S, χ x ∈ closure (Circle.centeredArc (π / 4))}

@[simp]
theorem mem_polar {S : Set G} {χ : PontryaginDual G} :
    χ ∈ polar S ↔ ∀ x ∈ S, χ x ∈ closure (Circle.centeredArc (π / 4)) :=
  Iff.rfl

theorem one_mem_polar (S : Set G) : (1 : PontryaginDual G) ∈ polar S := by
  intro x _
  rw [one_apply]
  refine subset_closure ((Circle.mem_centeredArc (by linarith [Real.pi_pos])).mpr ?_)
  simpa using (by positivity : (0 : ℝ) < π / 4)

theorem polar_anti {S T : Set G} (h : S ⊆ T) : polar T ⊆ polar S :=
  fun _ hχ x hx ↦ hχ x (h hx)

theorem isClosed_polar (S : Set G) : IsClosed (polar S) := by
  have : polar S = ⋂ x ∈ S,
      (fun χ : PontryaginDual G ↦ χ x) ⁻¹' closure (Circle.centeredArc (π / 4)) := by
    ext χ
    simp only [mem_polar, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_biInter fun x _ ↦ isClosed_closure.preimage (continuous_eval_const x)

/-- The family of (not necessarily continuous) monoid homomorphisms mapping a neighborhood `U`
of `1` into the closed quarter arc is equicontinuous at `1`. -/
private theorem equicontinuousAt_one_polar [IsTopologicalGroup G] {U : Set G}
    (hU : U ∈ nhds (1 : G)) :
    EquicontinuousAt
      (fun f : {f : G →* Circle | ∀ x ∈ U, f x ∈ closure (Circle.centeredArc (π / 4))} ↦
        (f : G → Circle)) 1 := by
  rw [Circle.hasBasis_centeredArc_div_two_pow.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ ↦ ?_
  have hV : (⋂ k ∈ Finset.Icc 1 (2 ^ (n + 1)), (· ^ k) ⁻¹' U) ∈ nhds (1 : G) := by
    rw [Filter.biInter_finset_mem]
    exact fun k _ ↦ (continuous_pow k).continuousAt.preimage_mem_nhds (by rwa [one_pow])
  refine Filter.eventually_iff_exists_mem.mpr ⟨_, hV, fun y hy ⟨f, hf⟩ ↦ ?_⟩
  change f y / f 1 ∈ Circle.centeredArc (π / 2 ^ (n + 1))
  rw [_root_.map_one, div_one,
    Circle.mem_centeredArc (div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two))]
  have hpow : ∀ k, 1 ≤ k → k ≤ 2 ^ (n + 1) →
      f y ^ k ∈ closure (Circle.centeredArc (π / 4)) := by
    intro k hk1 hk2
    rw [← map_pow]
    exact hf _ (Set.mem_iInter₂.mp hy k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩))
  calc |Complex.arg (f y : ℂ)|
      ≤ π / (4 * ((2 ^ (n + 1) : ℕ) : ℝ)) :=
        DualPolars.Circle.abs_arg_le_div_of_pow_mem_centeredArc (by positivity) hpow
    _ < π / 2 ^ (n + 1) := by
        have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
        apply div_lt_div_of_pos_left Real.pi_pos h2
        push_cast
        linarith

/-- The polar of a neighborhood of `1` in `G` is a compact subset of the Pontryagin dual.
(No local compactness of `G` is required.) -/
theorem isCompact_polar [IsTopologicalGroup G] {U : Set G} (hU : U ∈ nhds (1 : G)) :
    IsCompact (polar U) := by
  have h := equicontinuous_of_equicontinuousAt_one _ (equicontinuousAt_one_polar hU)
  let S1 : Set (G →* Circle) :=
    {f | ∀ x ∈ U, f x ∈ closure (Circle.centeredArc (π / 4))}
  replace h : Equicontinuous ((↑) : S1 → G → Circle) := h
  let S2 : Set (PontryaginDual G) := polar U
  let S3 : Set C(G, Circle) := ContinuousMonoidHom.toContinuousMap '' S2
  let S4 : Set (G → Circle) := (↑) '' S3
  have hS4 : S4 = (↑) '' S1 := by
    ext u
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → G → Circle) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ closure (Circle.centeredArc (π / 4))) ∩
      Set.range ((↑) : (G →* Circle) → G → Circle) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun u ↦ ⟨fun ⟨g, hg, hu⟩ ↦ hu ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hu⟩ ↦ ⟨g, hu ▸ hg, hu⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi fun _ _ ↦ isClosed_closure).inter
      (MonoidHom.isClosed_range_coe G Circle)
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr
    (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)

/-- The sets `{χ | ∀ x ∈ K, χ x ∈ Circle.centeredArc r}`, for `K ⊆ G` compact and `0 < r ≤ π`,
form a neighborhood basis of `1` in the Pontryagin dual. -/
theorem hasBasis_nhds_one :
    (nhds (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × ℝ ↦ IsCompact p.1 ∧ 0 < p.2 ∧ p.2 ≤ π)
      (fun p ↦ {χ | ∀ x ∈ p.1, χ x ∈ Circle.centeredArc p.2}) := by
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    have hcomap := (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).basis_nhds
      (x := (1 : PontryaginDual G))
      (nhds_basis_uniformity' ContinuousMap.hasBasis_compactConvergenceUniformity)
    obtain ⟨⟨K, V⟩, ⟨hK, hV⟩, hsub⟩ := hcomap.mem_iff.mp ht
    obtain ⟨n, -, hn⟩ := Circle.hasBasis_centeredArc_div_two_pow.mem_iff.mp
      (UniformSpace.ball_mem_nhds (1 : Circle) hV)
    exact ⟨(K, π / 2 ^ (n + 1)),
      ⟨hK, by positivity, div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two)⟩,
      fun χ hχ ↦ hsub fun x hx ↦ hn (hχ x hx)⟩
  · rintro ⟨⟨K, r⟩, ⟨hK, hr, hrπ⟩, hsub⟩
    refine Filter.mem_of_superset ?_ hsub
    have hopen : IsOpen {χ : PontryaginDual G | ∀ x ∈ K, χ x ∈ Circle.centeredArc r} :=
      isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hK (Circle.isOpen_centeredArc r))
    refine hopen.mem_nhds fun x hx ↦ ?_
    rw [Circle.mem_centeredArc hrπ]
    simpa using hr

/-- Translation of `PontryaginDual.hasBasis_nhds_one` to the neighborhood filter of an
arbitrary character `χ₀`. -/
theorem hasBasis_nhds [IsTopologicalGroup G] (χ₀ : PontryaginDual G) :
    (nhds χ₀).HasBasis
      (fun p : Set G × ℝ ↦ IsCompact p.1 ∧ 0 < p.2 ∧ p.2 ≤ π)
      (fun p ↦ {χ | ∀ x ∈ p.1, χ x / χ₀ x ∈ Circle.centeredArc p.2}) := by
  have h := (hasBasis_nhds_one (G := G)).comap (· * χ₀⁻¹)
  rw [nhds_translation_mul_inv] at h
  refine h.to_hasBasis (fun p hp ↦ ⟨p, hp, fun χ hχ x hx ↦ ?_⟩)
    (fun p hp ↦ ⟨p, hp, fun χ hχ x hx ↦ ?_⟩)
  · have h' := hχ x hx
    rwa [div_eq_mul_inv] at h'
  · rw [div_eq_mul_inv]
    exact hχ x hx

/-- Characters near `1` in the Pontryagin dual map a fixed compact set into a fixed small
arc around `1`. -/
theorem eventually_mem_centeredArc {K : Set G} (hK : IsCompact K) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ π) :
    ∀ᶠ χ in nhds (1 : PontryaginDual G), ∀ x ∈ K, χ x ∈ Circle.centeredArc r :=
  hasBasis_nhds_one.mem_of_mem (i := (K, r)) ⟨hK, hr, hrπ⟩

/-- Characters near `1` in the Pontryagin dual are uniformly close to `1` on compact sets,
in the norm of `ℂ`. -/
theorem eventually_uniform_arc {K : Set G} (hK : IsCompact K) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ π) :
    ∀ᶠ χ in nhds (1 : PontryaginDual G), ∀ x ∈ K, ‖(χ x : ℂ) - 1‖ < r := by
  filter_upwards [eventually_mem_centeredArc hK hr hrπ] with χ hχ x hx
  exact (DualPolars.Circle.norm_coe_sub_one_le_abs_arg (χ x)).trans_lt
    ((Circle.mem_centeredArc hrπ).mp (hχ x hx))

end PontryaginDual

end

end OAI.Topology.Pontryagin.DualPolars
