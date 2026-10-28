import OAI.Topology.Pontryagin.Spectrum
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-! # Unitization Spectrum -/

namespace OAI.Topology.Pontryagin.UnitizationSpectrum.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# The spectrum of `L¹(G)` elements through the unitization

This file transfers the character classification of `Pontryagin.Spectrum` to the unital
commutative Banach algebra `WithLp 1 (Unitization ℂ (L1G μ))` (the unitization of the
convolution algebra with the `L¹` product norm), and extracts the spectral-radius facts
in the exact shape consumed by the Bochner layer.

## Main definitions

* `L1G.unitizationInrCLM μ: L1G μ →L[ℂ] WithLp 1 (Unitization ℂ (L1G μ))`: the isometric
 inclusion, as a continuous linear map;
* `L1G.npow μ F n`: the convolution power `F^(n+1)` (the non-unital algebra `L1G μ` has no
 `Monoid` structure, hence no `^`).

## Main results

* `L1G.spectrum_unitization_subset`: the spectrum of `F` in the unitization is contained in
 `{0} ∪ range (𝓕F)` — every unital character either kills `L¹(G)` (the augmentation) or
 restricts to a character of `L¹(G)`, which is evaluation of the Fourier transform by
 `L1G.characterSpace_exists_char`;
* `L1G.spectralRadius_unitization_le`: a uniform bound `‖𝓕F‖_∞ ≤ C` bounds the spectral
 radius by `C`;
* `L1G.exists_norm_npow_rpow_le`: the Gelfand-formula consequence
 `‖F^(n+1)‖^(1/(n+1)) ≤ C + ε` for `n` large, ready for the Cauchy–Schwarz iteration of
 the Bochner layer.
-/

open Filter Function Set _root_.Topology WeakDual WeakDual.CharacterSpace
open scoped ComplexConjugate ENNReal NNReal

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

-- `show` is used pervasively to cross the definitional equality between the type synonym
-- `L1G μ` and `Lp ℂ 1 μ`.

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

namespace L1G

/-! ### The unitization as a commutative Banach algebra -/

/-- The `L¹`-unitization of the commutative algebra `L1G μ` is a normed **commutative**
ring: commutativity is transported from `Unitization.instCommRing` through the `WithLp`
type synonym. -/
noncomputable instance : NormedCommRing (WithLp 1 (Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) :=
  { (inferInstance : NormedRing (WithLp 1 (Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))) with
    mul_comm := fun x y => by
      rw [WithLp.ext_iff, WithLp.unitization_mul, WithLp.unitization_mul]
      exact mul_comm _ _ }

/-- The isometric inclusion of `L¹(G)` into its `L¹`-normed unitization, as a continuous
linear map. -/
def _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.unitizationInrCLM : Pontryagin.Algebra.MeasureTheory.L1G μ →L[ℂ] WithLp 1 (Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)) :=
  LinearMap.mkContinuous
    ((WithLp.linearEquiv 1 ℂ (Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))).symm.toLinearMap.comp
      (Unitization.inrHom ℂ ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))
    1
    (fun x => by
      rw [one_mul]
      exact le_of_eq (WithLp.unitization_norm_inr x))

@[simp]
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.unitizationInrCLM_apply (x : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    Pontryagin.Algebra.MeasureTheory.L1G.unitizationInrCLM μ x = WithLp.toLp 1 (x : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)) := rfl

/-- The inclusion into the unitization is multiplicative. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.toLp_inr_mul (x y : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    WithLp.toLp 1 ((x : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) * WithLp.toLp 1 ((y : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))
      = WithLp.toLp 1 (((x * y : Pontryagin.Algebra.MeasureTheory.L1G μ) : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) := by
  rw [WithLp.ext_iff, WithLp.unitization_mul]
  exact (Unitization.inr_mul ℂ x y).symm

/-! ### Convolution powers -/

/-- Iterated convolution powers of an element of the non-unital algebra `L1G μ`:
`npow μ F n = F^(n+1)`. (The non-unital algebra has no `Monoid` structure, hence no `^`.) -/
def _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.npow (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : ℕ → Pontryagin.Algebra.MeasureTheory.L1G μ
  | 0 => F
  | n + 1 => F * npow F n

@[simp]
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.npow_zero (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Pontryagin.Algebra.MeasureTheory.L1G.npow μ F 0 = F := rfl

@[simp]
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.npow_succ (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (n : ℕ) : Pontryagin.Algebra.MeasureTheory.L1G.npow μ F (n + 1) = F * Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n := rfl

/-- Convolution powers agree with monoid powers in the unitization: the image of
`npow μ F n` is `(inr F)^(n+1)`. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.toLp_inr_npow (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (n : ℕ) :
    WithLp.toLp 1 ((Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n : Pontryagin.Algebra.MeasureTheory.L1G μ) : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))
      = WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) ^ (n + 1) := by
  induction n with
  | zero => rw [pow_one]; rfl
  | succ n ih =>
    calc WithLp.toLp 1 ((Pontryagin.Algebra.MeasureTheory.L1G.npow μ F (n + 1) : Pontryagin.Algebra.MeasureTheory.L1G μ) : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))
        = WithLp.toLp 1 (((F * Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n : Pontryagin.Algebra.MeasureTheory.L1G μ) : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) := rfl
      _ = WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))
            * WithLp.toLp 1 ((Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n : Pontryagin.Algebra.MeasureTheory.L1G μ) : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)) :=
          (Pontryagin.Algebra.MeasureTheory.L1G.toLp_inr_mul μ F (Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n)).symm
      _ = WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))
            * WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) ^ (n + 1) := by rw [ih]
      _ = WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) ^ (n + 1 + 1) :=
          (pow_succ' _ _).symm

/-! ### The spectrum through the character classification -/

/-- **The spectrum of an `L¹` element in the unitization** is contained in
`{0} ∪ range (𝓕F)`: a unital character of the unitization either kills all of `L¹(G)`
(the augmentation character, giving the value `0`) or restricts to a character of
`L¹(G)`, which is evaluation of the Fourier transform at a point of the dual group. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.spectrum_unitization_subset (F : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    spectrum ℂ (WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))))
      ⊆ insert (0 : ℂ) (Set.range (Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F)) := by
  intro z hz
  obtain ⟨Φ, hΦ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  by_cases hψ0 : ∀ x : Pontryagin.Algebra.MeasureTheory.L1G μ, Φ (WithLp.toLp 1 ((x : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))) = 0
  · refine Set.mem_insert_iff.mpr (Or.inl ?_)
    rw [← hΦ]
    exact hψ0 F
  · push Not at hψ0
    obtain ⟨x₀, hx₀⟩ := hψ0
    -- the restriction of `Φ` to `L¹(G)` is a character of `L¹(G)`
    set ψ : Pontryagin.Algebra.MeasureTheory.L1G μ →L[ℂ] ℂ := (toCLM Φ).comp (Pontryagin.Algebra.MeasureTheory.L1G.unitizationInrCLM μ) with hψdef
    have hψapply : ∀ x : Pontryagin.Algebra.MeasureTheory.L1G μ,
        ψ x = Φ (WithLp.toLp 1 ((x : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))) := fun x => rfl
    have hψne : ψ ≠ 0 := fun h => hx₀ (by rw [← hψapply x₀, h]; simp)
    have hψmul : ∀ x y : Pontryagin.Algebra.MeasureTheory.L1G μ, ψ (x * y) = ψ x * ψ y := by
      intro x y
      rw [hψapply, hψapply, hψapply, ← Pontryagin.Algebra.MeasureTheory.L1G.toLp_inr_mul μ x y]
      exact map_mul Φ _ _
    obtain ⟨χ, hχ, -⟩ := Pontryagin.Algebra.MeasureTheory.L1G.characterSpace_exists_char μ
      (⟨ψ, hψne, hψmul⟩ : characterSpace ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))
    refine Set.mem_insert_iff.mpr (Or.inr ⟨χ, ?_⟩)
    rw [← hΦ, ← hψapply F]
    exact (hχ F).symm

/-- A uniform bound on the Fourier transform bounds the spectral radius in the
unitization. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.spectralRadius_unitization_le (F : Pontryagin.Algebra.MeasureTheory.L1G μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ χ : PontryaginDual G, ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ‖ ≤ C) :
    spectralRadius ℂ (WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)))) ≤ ENNReal.ofReal C := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun z hz => ?_
  rcases Set.mem_insert_iff.mp (Pontryagin.Algebra.MeasureTheory.L1G.spectrum_unitization_subset μ F hz) with rfl | ⟨χ, rfl⟩
  · simp
  · have h1 : ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ‖₊ ≤ C.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC]
      exact h χ
    calc (‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ‖₊ : ℝ≥0∞) ≤ (C.toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1
      _ = ENNReal.ofReal C := rfl

/-- **Gelfand-formula consumer lemma.** If `‖𝓕F‖ ≤ C` pointwise on the dual group, then
for every `ε > 0` the convolution powers eventually satisfy
`‖F^(n+1)‖^(1/(n+1)) ≤ C + ε`. This is the only spectral input the Bochner layer needs;
the unitization does not appear in the statement. -/
theorem _root_.OAI.Topology.Pontryagin.Algebra.MeasureTheory.L1G.exists_norm_npow_rpow_le (F : Pontryagin.Algebra.MeasureTheory.L1G μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ χ : PontryaginDual G, ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Pontryagin.Algebra.MeasureTheory.L1G.npow μ F n‖ ^ ((1 : ℝ) / ((n : ℝ) + 1)) ≤ C + ε := by
  have hsr : spectralRadius ℂ (WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))))
      ≤ ENNReal.ofReal C := Pontryagin.Algebra.MeasureTheory.L1G.spectralRadius_unitization_le μ F hC h
  have hlt : spectralRadius ℂ (WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))))
      < ENNReal.ofReal (C + ε) :=
    lt_of_le_of_lt hsr ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (lt_add_of_pos_right C hε))
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
    (WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))))
  have hev := hg.eventually_lt_const hlt
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (‖WithLp.toLp 1 ((F : Unitization ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ))) ^ (n + 1)‖₊ : ℝ≥0∞)
      ^ (1 / ((n + 1 : ℕ) : ℝ)) ≤ ENNReal.ofReal (C + ε) :=
    (hN (n + 1) (le_trans hn (Nat.le_succ n))).le
  rw [← Pontryagin.Algebra.MeasureTheory.L1G.toLp_inr_npow μ F n, WithLp.unitization_nnnorm_inr] at h1
  have hexp : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.coe_rpow_of_nonneg _ hexp,
    show ENNReal.ofReal (C + ε) = (((C + ε).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    ENNReal.coe_le_coe] at h1
  have h2 := NNReal.coe_le_coe.mpr h1
  rw [NNReal.coe_rpow, coe_nnnorm, Real.coe_toNNReal _ (by positivity)] at h2
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h2
  exact h2

end L1G

end

end OAI.Topology.Pontryagin.UnitizationSpectrum.MeasureTheory
