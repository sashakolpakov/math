import OAI.Topology.Pontryagin.Algebra
import OAI.Topology.Pontryagin.FourierTransform
import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Spectrum -/

namespace OAI.Topology.Pontryagin

noncomputable section

open _root_.MeasureTheory

/-!
# The Gelfand spectrum of the convolution algebra `L¹(G)`

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
identifies the characters of the commutative Banach algebra `L1G μ` (convolution on `L¹`)
with the points of the Pontryagin dual, via the Fourier transform.

## Main definitions

* `L1G.fourier μ F`: the Fourier transform of an `L¹` class, a function on the dual group;
* `L1G.fourierC0 μ F`: the same, bundled in `C₀(PontryaginDual G, ℂ)` (continuity plus the
 Riemann–Lebesgue lemma);
* `L1G.fourierHom μ: L1G μ →⋆ₙₐ[ℂ] C₀(PontryaginDual G, ℂ)`: the Fourier transform as a
 homomorphism of non-unital star algebras;
* `L1G.translate μ a F`: left translation on `L1G μ`;
* `pairCLM μ h`: testing an `L¹` class against a continuous compactly supported function,
 as a continuous linear functional.

## Main results

* `L1G.fourier_mul`, `L1G.fourier_star`, `L1G.norm_fourier_apply_le`,
 `L1G.norm_fourierC0_le`: the algebraic and metric properties of the transform, obtained
 from the `C_c` identities of `Pontryagin.FourierTransform` by density;
* `toLpCc_mconv_eq_integral`: the Bochner-integral form of convolution,
 `class (f ⋆ g) = ∫ a, f a • Lₐ (class g) ∂μ`;
* `fourierTransform_separates`: distinct characters are separated by the Fourier transforms
 of `C_c` functions;
* `exists_fourierTransform_eq_one`: the Fourier transform does not vanish identically at any
 character (a normalized bump times the character transforms to `1`);
* `L1G.characterSpace_exists_char`: **every character of `L¹(G)` is given by a unique
 point of the Pontryagin dual**, `φ F = 𝓕F(χ)` — the translation-ratio argument.
-/

open Filter Function Set _root_.Topology WeakDual WeakDual.CharacterSpace _root_.PontryaginDual
open OAI.Topology.Pontryagin.Translation.MeasureTheory
open scoped ComplexConjugate ENNReal ZeroAtInfty

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

-- `show` is used pervasively to cross the definitional equality between the type synonym
-- `L1G μ` and `Lp ℂ 1 μ`, and to beta-reduce integrands.

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### The Fourier transform on `L¹` classes -/

section FourierLp

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- On a `C_c` class the Fourier transform is computed by the representative. -/
theorem Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) = FourierTransform.PontryaginDual.fourierTransform μ f :=
  FourierTransform.PontryaginDual.fourierTransform_congr_ae (Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The Fourier transform at a fixed character is `1`-Lipschitz on `L¹`. -/
theorem Spectrum.MeasureTheory.norm_fourierTransform_coeFn_sub_le (F K : Lp ℂ 1 μ) (χ : PontryaginDual G) :
    ‖FourierTransform.PontryaginDual.fourierTransform μ ⇑F χ - FourierTransform.PontryaginDual.fourierTransform μ ⇑K χ‖ ≤ ‖F - K‖ :=
  (FourierTransform.PontryaginDual.norm_fourierTransform_sub_le μ (L1.integrable_coeFn F) (L1.integrable_coeFn K) χ).trans
    (le_of_eq (Pontryagin.Algebra.MeasureTheory.norm_sub_eq_integral μ F K).symm)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The Fourier transform at a fixed character is a continuous function of the `L¹` class. -/
theorem Spectrum.MeasureTheory.continuous_fourierTransform_coeFn (χ : PontryaginDual G) :
    Continuous fun F : Lp ℂ 1 μ => FourierTransform.PontryaginDual.fourierTransform μ ⇑F χ :=
  (LipschitzWith.of_dist_le_mul fun F K => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact Spectrum.MeasureTheory.norm_fourierTransform_coeFn_sub_le μ F K χ).continuous

/-- The Fourier transform of an element of the convolution algebra `L1G μ`. -/
def Algebra.MeasureTheory.L1G.fourier (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : PontryaginDual G → ℂ :=
  FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
theorem Algebra.MeasureTheory.L1G.fourier_def (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ = ∫ x, (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F : Lp ℂ 1 μ) x * conj (χ x : ℂ) ∂μ := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- The Fourier transform of a `C_c` class is the Fourier transform of the representative. -/
theorem Algebra.MeasureTheory.L1G.fourier_ofLp_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) = FourierTransform.PontryaginDual.fourierTransform μ f :=
  Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc μ f hfc hfs

/-- The trivial bound: the transform is dominated by the `L¹` norm. -/
theorem Algebra.MeasureTheory.L1G.norm_fourier_apply_le (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    ‖Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ‖ ≤ ‖F‖ :=
  (FourierTransform.PontryaginDual.norm_fourierTransform_le μ _ χ).trans
    (le_of_eq ((L1.norm_eq_integral_norm (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)).symm.trans (Pontryagin.Algebra.MeasureTheory.L1G.norm_toLp μ F)))

theorem Algebra.MeasureTheory.L1G.fourier_add (F K : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (F + K) χ = Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ + Pontryagin.Algebra.MeasureTheory.L1G.fourier μ K χ := by
  show FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F + Pontryagin.Algebra.MeasureTheory.L1G.toLp μ K) χ = _
  rw [FourierTransform.PontryaginDual.fourierTransform_congr_ae (Lp.coeFn_add (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ K)),
    FourierTransform.PontryaginDual.fourierTransform_add μ (L1.integrable_coeFn _) (L1.integrable_coeFn _)]
  rfl

theorem Algebra.MeasureTheory.L1G.fourier_smul (c : ℂ) (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (c • F) χ = c * Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ := by
  show FourierTransform.PontryaginDual.fourierTransform μ ⇑(c • Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) χ = _
  rw [FourierTransform.PontryaginDual.fourierTransform_congr_ae (Lp.coeFn_smul c (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)), FourierTransform.PontryaginDual.fourierTransform_smul μ c]
  rfl

theorem Algebra.MeasureTheory.L1G.fourier_zero (χ : PontryaginDual G) : Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (0 : Pontryagin.Algebra.MeasureTheory.L1G μ) χ = 0 := by
  show FourierTransform.PontryaginDual.fourierTransform μ ⇑(0 : Lp ℂ 1 μ) χ = 0
  rw [FourierTransform.PontryaginDual.fourierTransform_congr_ae (Lp.coeFn_zero ℂ 1 μ), FourierTransform.PontryaginDual.fourierTransform_apply]
  simp

/-- **Multiplicativity of the Fourier transform** on `L¹`, by density from
`fourierTransform_mconv`. -/
theorem Algebra.MeasureTheory.L1G.fourier_mul (F K : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (F * K) χ = Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ * Pontryagin.Algebra.MeasureTheory.L1G.fourier μ K χ := by
  have key : ∀ Fp Kp : Lp ℂ 1 μ,
      FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.mulCLM μ Fp Kp) χ
        = FourierTransform.PontryaginDual.fourierTransform μ ⇑Fp χ * FourierTransform.PontryaginDual.fourierTransform μ ⇑Kp χ := by
    have step1 : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
        (Fp : Lp ℂ 1 μ),
        FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.mulCLM μ Fp (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)) χ
          = FourierTransform.PontryaginDual.fourierTransform μ ⇑Fp χ * FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) χ := by
      intro g hgc hgs
      refine Pontryagin.Algebra.MeasureTheory.funext_of_dense μ
        (fun Fp => FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.mulCLM μ Fp (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)) χ)
        (fun Fp => FourierTransform.PontryaginDual.fourierTransform μ ⇑Fp χ * FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) χ)
        ((Spectrum.MeasureTheory.continuous_fourierTransform_coeFn μ χ).comp
          ((Pontryagin.Algebra.MeasureTheory.mulCLM μ).flip (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)).continuous)
        ((Spectrum.MeasureTheory.continuous_fourierTransform_coeFn μ χ).mul continuous_const) ?_
      intro f hfc hfs
      rw [Pontryagin.Algebra.MeasureTheory.mulCLM_toLpCc μ f g hfc hfs hgc hgs,
        Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc μ (Convolution.MeasureTheory.mconv μ f g) _ _,
        Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc μ f hfc hfs,
        Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc μ g hgc hgs,
        FourierTransform.PontryaginDual.fourierTransform_mconv μ hfc hfs hgc hgs χ]
    intro Fp Kp
    refine Pontryagin.Algebra.MeasureTheory.funext_of_dense μ
      (fun Kp => FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.mulCLM μ Fp Kp) χ)
      (fun Kp => FourierTransform.PontryaginDual.fourierTransform μ ⇑Fp χ * FourierTransform.PontryaginDual.fourierTransform μ ⇑Kp χ)
      ((Spectrum.MeasureTheory.continuous_fourierTransform_coeFn μ χ).comp (Pontryagin.Algebra.MeasureTheory.mulCLM μ Fp).continuous)
      (continuous_const.mul (Spectrum.MeasureTheory.continuous_fourierTransform_coeFn μ χ)) ?_ Kp
    intro g hgc hgs
    exact step1 g hgc hgs Fp
  exact key (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ K)

/-- The Fourier transform intertwines the star involution and complex conjugation. -/
theorem Algebra.MeasureTheory.L1G.fourier_star (F : Pontryagin.Algebra.MeasureTheory.L1G μ) (χ : PontryaginDual G) :
    Pontryagin.Algebra.MeasureTheory.L1G.fourier μ (star F) χ = conj (Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ) := by
  show FourierTransform.PontryaginDual.fourierTransform μ ⇑(Pontryagin.Algebra.MeasureTheory.L1star μ (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)) χ = _
  rw [FourierTransform.PontryaginDual.fourierTransform_congr_ae (Pontryagin.Algebra.MeasureTheory.coeFn_L1star μ (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)),
    FourierTransform.PontryaginDual.fourierTransform_mstar μ ⇑(Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) χ]
  rfl

omit [IsTopologicalGroup G] [μ.IsHaarMeasure] in
theorem Algebra.MeasureTheory.L1G.fourier_continuous (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Continuous (Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F) :=
  FourierTransform.PontryaginDual.continuous_fourierTransform μ (L1.integrable_coeFn (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F))

omit [T2Space G] in
theorem Algebra.MeasureTheory.L1G.fourier_zeroAtInfty (F : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    Tendsto (Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F) (cocompact (PontryaginDual G)) (nhds 0) :=
  FourierTransform.PontryaginDual.tendsto_fourierTransform_cocompact μ (L1.integrable_coeFn (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F))

/-- The Fourier transform of an `L¹` class, as an element of `C₀(Ĝ, ℂ)`. -/
def Algebra.MeasureTheory.L1G.fourierC0 (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : C₀(PontryaginDual G, ℂ) where
  toFun := Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F
  continuous_toFun := Pontryagin.Algebra.MeasureTheory.L1G.fourier_continuous μ F
  zero_at_infty' := Pontryagin.Algebra.MeasureTheory.L1G.fourier_zeroAtInfty μ F

@[simp]
theorem Algebra.MeasureTheory.L1G.coe_fourierC0 (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : ⇑(Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ F) = Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F := rfl

/-- The sup-norm of the bundled Fourier transform is at most the `L¹` norm. -/
theorem Algebra.MeasureTheory.L1G.norm_fourierC0_le (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : ‖Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ F‖ ≤ ‖F‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    fun χ => Pontryagin.Algebra.MeasureTheory.L1G.norm_fourier_apply_le μ F χ

/-- **The Fourier transform as a homomorphism of non-unital star algebras**
`L¹(G) →⋆ₙₐ[ℂ] C₀(Ĝ, ℂ)`. -/
def Algebra.MeasureTheory.L1G.fourierHom : Pontryagin.Algebra.MeasureTheory.L1G μ →⋆ₙₐ[ℂ] C₀(PontryaginDual G, ℂ) where
  toFun := Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ
  map_smul' c F := by
    ext χ
    rw [ZeroAtInftyContinuousMap.smul_apply]
    exact Pontryagin.Algebra.MeasureTheory.L1G.fourier_smul μ c F χ
  map_zero' := by
    ext χ
    rw [ZeroAtInftyContinuousMap.zero_apply]
    exact Pontryagin.Algebra.MeasureTheory.L1G.fourier_zero μ χ
  map_add' F K := by
    ext χ
    rw [ZeroAtInftyContinuousMap.add_apply]
    exact Pontryagin.Algebra.MeasureTheory.L1G.fourier_add μ F K χ
  map_mul' F K := by
    ext χ
    rw [ZeroAtInftyContinuousMap.mul_apply]
    exact Pontryagin.Algebra.MeasureTheory.L1G.fourier_mul μ F K χ
  map_star' F := by
    ext χ
    rw [ZeroAtInftyContinuousMap.star_apply]
    exact Pontryagin.Algebra.MeasureTheory.L1G.fourier_star μ F χ

@[simp]
theorem Algebra.MeasureTheory.L1G.fourierHom_apply (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Pontryagin.Algebra.MeasureTheory.L1G.fourierHom μ F = Pontryagin.Algebra.MeasureTheory.L1G.fourierC0 μ F := rfl

end FourierLp

/-! ### Translation on `L1G` -/

section TranslateL1

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- Translation of a `C_c` class is the class of the translated representative. -/
theorem Spectrum.MeasureTheory.translateLp_toLpCc (a : G) (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)
      = Pontryagin.Algebra.MeasureTheory.toLpCc μ (mtranslate a f) ((Translation.Continuous.mtranslate hfc) a) ((Translation.HasCompactSupport.mtranslate hfs) a) := by
  refine Lp.ext ?_
  have h2 : mtranslate a ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) =ᵐ[μ] mtranslate a f :=
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae_eq_comp
      (Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ f hfc hfs)
  exact ((Translation.MeasureTheory.coeFn_translateLp μ 1 a _).trans h2).trans (Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ _ _ _).symm

/-- Translation commutes with convolution in the first slot, by density from
`mtranslate_mconv`. -/
theorem Spectrum.MeasureTheory.translateLp_mulCLM (a : G) (F K : Lp ℂ 1 μ) :
    Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.mulCLM μ F K) = Pontryagin.Algebra.MeasureTheory.mulCLM μ (Translation.MeasureTheory.translateLp μ 1 a F) K := by
  have step1 : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
      (F : Lp ℂ 1 μ),
      Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.mulCLM μ F (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs))
        = Pontryagin.Algebra.MeasureTheory.mulCLM μ (Translation.MeasureTheory.translateLp μ 1 a F) (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) := by
    intro g hgc hgs
    refine Pontryagin.Algebra.MeasureTheory.funext_of_dense μ
      (fun F => Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.mulCLM μ F (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)))
      (fun F => Pontryagin.Algebra.MeasureTheory.mulCLM μ (Translation.MeasureTheory.translateLp μ 1 a F) (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs))
      ((Translation.MeasureTheory.translateLp μ 1 a).continuous.comp
        ((Pontryagin.Algebra.MeasureTheory.mulCLM μ).flip (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)).continuous)
      (((Pontryagin.Algebra.MeasureTheory.mulCLM μ).flip (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)).continuous.comp
        (Translation.MeasureTheory.translateLp μ 1 a).continuous) ?_
    intro f hfc hfs
    rw [Pontryagin.Algebra.MeasureTheory.mulCLM_toLpCc μ f g hfc hfs hgc hgs,
      Spectrum.MeasureTheory.translateLp_toLpCc μ a (Convolution.MeasureTheory.mconv μ f g) _ _, Spectrum.MeasureTheory.translateLp_toLpCc μ a f hfc hfs,
      Pontryagin.Algebra.MeasureTheory.mulCLM_toLpCc μ (mtranslate a f) g _ _ hgc hgs]
    exact Pontryagin.Algebra.MeasureTheory.toLpCc_congr μ _ _ _ _ (Convolution.MeasureTheory.mtranslate_mconv μ a f g)
  refine Pontryagin.Algebra.MeasureTheory.funext_of_dense μ
    (fun K => Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.mulCLM μ F K))
    (fun K => Pontryagin.Algebra.MeasureTheory.mulCLM μ (Translation.MeasureTheory.translateLp μ 1 a F) K)
    ((Translation.MeasureTheory.translateLp μ 1 a).continuous.comp (Pontryagin.Algebra.MeasureTheory.mulCLM μ F).continuous)
    ((Pontryagin.Algebra.MeasureTheory.mulCLM μ (Translation.MeasureTheory.translateLp μ 1 a F)).continuous) ?_ K
  intro g hgc hgs
  exact step1 g hgc hgs F

/-- Left translation on the convolution algebra `L1G μ`. -/
def Algebra.MeasureTheory.L1G.translate (a : G) (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Pontryagin.Algebra.MeasureTheory.L1G μ :=
  Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F))

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
@[simp]
theorem Algebra.MeasureTheory.L1G.toLp_translate (a : G) (F : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    Pontryagin.Algebra.MeasureTheory.L1G.toLp μ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F) = Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) := rfl

@[simp]
theorem Algebra.MeasureTheory.L1G.norm_translate (a : G) (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : ‖Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F‖ = ‖F‖ :=
  Translation.MeasureTheory.norm_translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
@[simp]
theorem Algebra.MeasureTheory.L1G.translate_one (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Pontryagin.Algebra.MeasureTheory.L1G.translate μ 1 F = F :=
  congrArg (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ) (Translation.MeasureTheory.translateLp_one μ 1 (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F))

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem Algebra.MeasureTheory.L1G.translate_translate (a b : G) (F : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    Pontryagin.Algebra.MeasureTheory.L1G.translate μ a (Pontryagin.Algebra.MeasureTheory.L1G.translate μ b F) = Pontryagin.Algebra.MeasureTheory.L1G.translate μ (a * b) F :=
  (congrArg (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ) (Translation.MeasureTheory.translateLp_mul μ 1 a b (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F))).symm

theorem Algebra.MeasureTheory.L1G.continuous_translate (F : Pontryagin.Algebra.MeasureTheory.L1G μ) : Continuous fun a : G => Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F :=
  Translation.MeasureTheory.continuous_translateLp μ 1 ENNReal.one_ne_top (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)

/-- Translation commutes with multiplication in `L1G μ`. -/
theorem Algebra.MeasureTheory.L1G.translate_mul (a : G) (F K : Pontryagin.Algebra.MeasureTheory.L1G μ) :
    Pontryagin.Algebra.MeasureTheory.L1G.translate μ a (F * K) = Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F * K :=
  congrArg (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ) (Spectrum.MeasureTheory.translateLp_mulCLM μ a (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F) (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ K))

end TranslateL1

/-! ### The Bochner-integral form of convolution -/

section VectorConvolution

omit [T2Space G] in
/-- The vector-valued integrand `a ↦ f a • Lₐ K` is integrable for `f` continuous compactly
supported. -/
theorem Spectrum.MeasureTheory.integrable_smul_translateLp (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (K : Lp ℂ 1 μ) :
    Integrable (fun a => f a • Translation.MeasureTheory.translateLp μ 1 a K) μ := by
  have hc : Continuous fun a => f a • Translation.MeasureTheory.translateLp μ 1 a K :=
    hfc.smul (Translation.MeasureTheory.continuous_translateLp μ 1 ENNReal.one_ne_top K)
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hfs
    fun a ha => subset_tsupport f ?_
  simp only [mem_support] at ha ⊢
  intro hfa
  exact ha (by rw [hfa, zero_smul])

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The product of the coeFn of an `L¹` class with a `C_c` function is integrable. -/
theorem Spectrum.MeasureTheory.integrable_coeFn_mul_of_cc (u : Lp ℂ 1 μ) {h : G → ℂ} (hhc : Continuous h)
    (hhs : HasCompactSupport h) : Integrable (fun x => u x * h x) μ := by
  obtain ⟨C, hC⟩ := hhc.bounded_above_of_compact_support hhs
  exact (L1.integrable_coeFn u).mul_bdd hhc.aestronglyMeasurable (Eventually.of_forall hC)

/-- Testing an `L¹` class against a continuous compactly supported function, as a continuous
linear functional. -/
def Spectrum.MeasureTheory.pairCLM (h : G → ℂ) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    Lp ℂ 1 μ →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u : Lp ℂ 1 μ => ∫ x, u x * h x ∂μ
      map_add' := fun u v => by
        rw [← integral_add (Spectrum.MeasureTheory.integrable_coeFn_mul_of_cc μ u hhc hhs)
          (Spectrum.MeasureTheory.integrable_coeFn_mul_of_cc μ v hhc hhs)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u v] with x hx
        rw [hx, Pi.add_apply, add_mul]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    (by
      obtain ⟨C, hC⟩ := hhc.bounded_above_of_compact_support hhs
      refine ⟨C, fun u => ?_⟩
      calc ‖∫ x, u x * h x ∂μ‖
          ≤ ∫ x, ‖u x‖ * C ∂μ := by
            refine norm_integral_le_of_norm_le
              (((L1.integrable_coeFn u).norm).mul_const C)
              (Eventually.of_forall fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖u‖ := by
            rw [integral_mul_const, ← L1.norm_eq_integral_norm, mul_comm])

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp]
theorem Spectrum.MeasureTheory.pairCLM_apply (h : G → ℂ) (hhc : Continuous h) (hhs : HasCompactSupport h)
    (u : Lp ℂ 1 μ) : Spectrum.MeasureTheory.pairCLM μ h hhc hhs u = ∫ x, u x * h x ∂μ := rfl

/-- **The Bochner-integral form of convolution**: for continuous compactly supported `f`, `g`,
the `L¹` class of `f ⋆ g` is the vector integral `∫ a, f a • Lₐ (class g) ∂μ`. -/
theorem Spectrum.MeasureTheory.toLpCc_mconv_eq_integral (f g : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs)
      = ∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ := by
  have hΦi : Integrable (fun a => f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)) μ :=
    Spectrum.MeasureTheory.integrable_smul_translateLp μ f hfc hfs _
  -- the pointwise description of the integrand
  have hΦcoe : ∀ a : G,
      ⇑(f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs)) =ᵐ[μ] fun x => f a * g (a⁻¹ * x) := by
    intro a
    rw [Spectrum.MeasureTheory.translateLp_toLpCc μ a g hgc hgs]
    filter_upwards [Lp.coeFn_smul (f a)
        (Pontryagin.Algebra.MeasureTheory.toLpCc μ (mtranslate a g) ((Translation.Continuous.mtranslate hgc) a) ((Translation.HasCompactSupport.mtranslate hgs) a)),
      Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ (mtranslate a g) ((Translation.Continuous.mtranslate hgc) a) ((Translation.HasCompactSupport.mtranslate hgs) a)] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2]
    simp [Translation.MeasureTheory.mtranslate_apply, smul_eq_mul]
  rw [← sub_eq_zero]
  -- test the difference against arbitrary C_c functions
  have htest : ∀ h : G → ℂ, Continuous h → HasCompactSupport h →
      ∫ x, (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs)
        - ∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) x * h x ∂μ = 0 := by
    intro h hhc hhs
    have hDpair : ∫ x, (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs)
          - ∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) x * h x ∂μ
        = Spectrum.MeasureTheory.pairCLM μ h hhc hhs
            (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs))
          - Spectrum.MeasureTheory.pairCLM μ h hhc hhs (∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ) := by
      rw [← map_sub]
      rfl
    -- the left pairing is the double integral in one order
    have hL : Spectrum.MeasureTheory.pairCLM μ h hhc hhs
        (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs))
        = ∫ x, Convolution.MeasureTheory.mconv μ f g x * h x ∂μ := by
      rw [Spectrum.MeasureTheory.pairCLM_apply]
      refine integral_congr_ae ?_
      filter_upwards [Pontryagin.Algebra.MeasureTheory.coeFn_toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs)
        (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs)] with x hx
      rw [hx]
    -- the right pairing is the double integral in the other order
    have hR : Spectrum.MeasureTheory.pairCLM μ h hhc hhs (∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ)
        = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ := by
      rw [← ContinuousLinearMap.integral_comp_comm (Spectrum.MeasureTheory.pairCLM μ h hhc hhs) hΦi]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      show Spectrum.MeasureTheory.pairCLM μ h hhc hhs (f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs))
          = ∫ x, f a * g (a⁻¹ * x) * h x ∂μ
      rw [Spectrum.MeasureTheory.pairCLM_apply]
      refine integral_congr_ae ?_
      filter_upwards [hΦcoe a] with x hx
      rw [hx]
    -- Fubini for the jointly continuous compactly supported kernel
    have hkc : Continuous (uncurry fun x a : G => f a * g (a⁻¹ * x) * h x) :=
      (Convolution.MeasureTheory.mconv_kernel_continuous hfc hgc).mul (hhc.comp continuous_fst)
    have hks : HasCompactSupport (uncurry fun x a : G => f a * g (a⁻¹ * x) * h x) := by
      refine HasCompactSupport.of_support_subset_isCompact
        ((hfs.isCompact.mul hgs.isCompact).prod hfs.isCompact) fun p hp => ?_
      have hp' : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
      exact Convolution.MeasureTheory.mconv_kernel_support_subset hp'
    have hswap : ∫ x, Convolution.MeasureTheory.mconv μ f g x * h x ∂μ
        = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ :=
      calc ∫ x, Convolution.MeasureTheory.mconv μ f g x * h x ∂μ
          = ∫ x, ∫ a, f a * g (a⁻¹ * x) * h x ∂μ ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            exact (integral_mul_const _ _).symm
        _ = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ :=
            integral_integral_swap_of_hasCompactSupport hkc hks
    rw [hDpair, hL, hR, hswap, sub_self]
  have hae : ⇑(Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs)
      - ∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) =ᵐ[μ] 0 :=
    Density.MeasureTheory.ae_eq_zero_of_forall_integral_mul_eq_zero (L1.integrable_coeFn _) htest
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 1 μ).symm)

end VectorConvolution

/-! ### Separation and non-vanishing of `C_c` transforms -/

section Separation

omit [μ.Regular] in
/-- **Fourier transforms of `C_c` functions separate characters.** -/
theorem Spectrum.PontryaginDual.fourierTransform_separates {χ χ' : PontryaginDual G} (hne : χ ≠ χ') :
    ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧
      FourierTransform.PontryaginDual.fourierTransform μ f χ ≠ FourierTransform.PontryaginDual.fourierTransform μ f χ' := by
  -- a point where the characters differ, and the difference of conjugates
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, χ x₀ ≠ χ' x₀ := by
    by_contra hcon
    push Not at hcon
    exact hne (PontryaginDual.ext hcon)
  have hucont : Continuous fun x : G => conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ) :=
    (Complex.continuous_conj.comp (continuous_induced_dom.comp (map_continuous χ))).sub
      (Complex.continuous_conj.comp (continuous_induced_dom.comp (map_continuous χ')))
  have hu0 : conj (χ x₀ : ℂ) - conj ((χ' x₀ : Circle) : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr fun heq => hx₀ (Circle.coe_injective ?_)
    have h1 := congrArg (starRingEnd ℂ) heq
    simpa using h1
  set u : G → ℂ := fun x => conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ) with hu
  have hpos : 0 < ‖u x₀‖ := norm_pos_iff.mpr hu0
  -- a neighborhood of `x₀` where `u` is within `‖u x₀‖ / 2` of `u x₀`
  have hV : {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2} ∈ nhds x₀ := by
    have hc : Continuous fun x => ‖u x - u x₀‖ := (hucont.sub continuous_const).norm
    have h0 : Set.Iio (‖u x₀‖ / 2) ∈ nhds ((fun x => ‖u x - u x₀‖) x₀) := by
      simpa using Iio_mem_nhds (half_pos hpos)
    exact hc.continuousAt.preimage_mem_nhds h0
  -- a normalized bump at `x₀`
  have hU : (fun y : G => x₀ * y) ⁻¹' {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2}
      ∈ nhds (1 : G) := by
    refine ((continuous_const.mul continuous_id).continuousAt
      (x := (1 : G))).preimage_mem_nhds ?_
    simpa using hV
  obtain ⟨h₀, hh₀c, hh₀s, hh₀0, hh₀supp, hh₀int⟩ := Translation.MeasureTheory.exists_normalized_bump μ _ hU
  have hψc : Continuous (mtranslate x₀ h₀) := (Translation.Continuous.mtranslate hh₀c) x₀
  have hψs : HasCompactSupport (mtranslate x₀ h₀) := (Translation.HasCompactSupport.mtranslate hh₀s) x₀
  have hψ0 : ∀ x, 0 ≤ mtranslate x₀ h₀ x := fun x => hh₀0 _
  have hψint : ∫ x, mtranslate x₀ h₀ x ∂μ = 1 := by
    rw [Translation.MeasureTheory.integral_mtranslate μ x₀ h₀]
    exact hh₀int
  have hψsupp : tsupport (mtranslate x₀ h₀) ⊆ {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2} := by
    rw [Translation.MeasureTheory.tsupport_mtranslate x₀ h₀]
    rintro z ⟨y, hy, rfl⟩
    simpa [smul_eq_mul] using hh₀supp hy
  -- the complex bump
  have hψcc : Continuous fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hψc
  have hψcs : HasCompactSupport fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) :=
    hψs.comp_left Complex.ofReal_zero
  have hψci : Integrable (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) μ :=
    hψcc.integrable_of_hasCompactSupport hψcs
  have hψcint : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) ∂μ = 1 := by
    rw [show ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) ∂μ
        = ((∫ x, mtranslate x₀ h₀ x ∂μ : ℝ) : ℂ) from integral_ofReal, hψint,
      Complex.ofReal_one]
  refine ⟨fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ), hψcc, hψcs, ?_⟩
  -- the difference of transforms is `∫ ψ·u`
  have hdiff : FourierTransform.PontryaginDual.fourierTransform μ (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) χ
      - FourierTransform.PontryaginDual.fourierTransform μ (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) χ'
      = ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ := by
    rw [FourierTransform.PontryaginDual.fourierTransform_apply, FourierTransform.PontryaginDual.fourierTransform_apply,
      ← integral_sub (FourierTransform.MeasureTheory.Integrable.mul_conj_char (μ := μ) hψci χ) (FourierTransform.MeasureTheory.Integrable.mul_conj_char (μ := μ) hψci χ')]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hu]
    ring
  -- `∫ ψ·u` stays close to `u x₀`
  have hubdd : ∀ x, ‖u x‖ ≤ 2 := fun x => by
    rw [hu]
    calc ‖conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ)‖
        ≤ ‖conj (χ x : ℂ)‖ + ‖conj ((χ' x : Circle) : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [RCLike.norm_conj, RCLike.norm_conj, Circle.norm_coe, Circle.norm_coe]
          norm_num
  have hψui : Integrable (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x) μ :=
    hψci.mul_bdd hucont.aestronglyMeasurable (Eventually.of_forall hubdd)
  have hconst : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀ ∂μ = u x₀ := by
    rw [integral_mul_const, hψcint, one_mul]
  have hsub : (∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ) - u x₀
      = ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x
          - ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀ ∂μ := by
    rw [integral_sub hψui (hψci.mul_const (u x₀)), hconst]
  have hclose : ‖(∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ) - u x₀‖ ≤ ‖u x₀‖ / 2 := by
    rw [hsub]
    have hpt : ∀ x, ‖((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x
        - ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀‖ ≤ mtranslate x₀ h₀ x * (‖u x₀‖ / 2) := by
      intro x
      rw [← mul_sub, norm_mul]
      have hn : ‖((mtranslate x₀ h₀ x : ℝ) : ℂ)‖ = mtranslate x₀ h₀ x := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 x)]
      rw [hn]
      by_cases hx : x ∈ tsupport (mtranslate x₀ h₀)
      · exact mul_le_mul_of_nonneg_left (hψsupp hx).le (hψ0 x)
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    refine (norm_integral_le_of_norm_le
      ((hψc.integrable_of_hasCompactSupport hψs).mul_const _)
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_mul_const, hψint, one_mul]
  -- conclude
  intro heq
  have hzero : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ = 0 := by
    rw [← hdiff, heq, sub_self]
  rw [hzero, zero_sub, norm_neg] at hclose
  linarith

omit [μ.Regular] in
/-- **Non-vanishing**: at every character `χ` there is a `C_c` function whose Fourier
transform equals `1` at `χ` (a normalized bump times the character). -/
theorem Spectrum.PontryaginDual.exists_fourierTransform_eq_one (χ : PontryaginDual G) :
    ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ FourierTransform.PontryaginDual.fourierTransform μ f χ = 1 := by
  obtain ⟨h₀, hc, hs, h0, -, hint⟩ := Translation.MeasureTheory.exists_normalized_bump μ Set.univ Filter.univ_mem
  refine ⟨fun x => ((h₀ x : ℝ) : ℂ) * (χ x : ℂ),
    (Complex.continuous_ofReal.comp hc).mul
      (continuous_induced_dom.comp (map_continuous χ)),
    (hs.comp_left Complex.ofReal_zero).mul_right, ?_⟩
  rw [FourierTransform.PontryaginDual.fourierTransform_apply]
  calc ∫ x, ((h₀ x : ℝ) : ℂ) * (χ x : ℂ) * conj (χ x : ℂ) ∂μ
      = ∫ x, ((h₀ x : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show ((h₀ x : ℝ) : ℂ) * (χ x : ℂ) * conj (χ x : ℂ) = ((h₀ x : ℝ) : ℂ)
        rw [mul_assoc, Complex.mul_conj, Circle.normSq_coe]
        simp
    _ = 1 := by
        rw [show ∫ x, ((h₀ x : ℝ) : ℂ) ∂μ = ((∫ x, h₀ x ∂μ : ℝ) : ℂ) from integral_ofReal,
          hint, Complex.ofReal_one]

end Separation

/-! ### The character space of `L¹(G)` -/

/-- **Classification of the characters of `L¹(G)`**: every character `φ` of the convolution
algebra is evaluation of the Fourier transform at a unique character `χ` of `G`,
`φ F = 𝓕F(χ)`. The proof is the translation-ratio argument: `q a:= φ(Lₐ G₀) / φ(G₀)` is a
bounded continuous multiplicative function of modulus one, hence the conjugate of a character
of `G`, and the Bochner-integral form of convolution identifies `φ` with integration against
`q` on `C_c`; density does the rest. -/
theorem Algebra.MeasureTheory.L1G.characterSpace_exists_char (φ : characterSpace ℂ (Pontryagin.Algebra.MeasureTheory.L1G μ)) :
    ∃! χ : PontryaginDual G, ∀ F : Pontryagin.Algebra.MeasureTheory.L1G μ, φ F = Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ := by
  have hφcont : Continuous (⇑φ : Pontryagin.Algebra.MeasureTheory.L1G μ → ℂ) := map_continuous φ
  -- Step 0: a C_c class on which φ does not vanish
  obtain ⟨g₀, hg₀c, hg₀s, hG₀⟩ :
      ∃ (g₀ : G → ℂ) (hc : Continuous g₀) (hs : HasCompactSupport g₀),
        φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hc hs)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine φ.prop.1 (DFunLike.ext _ _ fun F => ?_)
    have h1 := Pontryagin.Algebra.MeasureTheory.funext_of_dense μ (fun Fp => φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ Fp)) (fun _ => 0)
      hφcont continuous_const (fun f hfc hfs => hcon f hfc hfs) (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)
    exact h1
  set G₀ : Pontryagin.Algebra.MeasureTheory.L1G μ := Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hg₀c hg₀s) with hG₀def
  -- Step 1: the translation ratio and its multiplicativity
  set q : G → ℂ := fun a => φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀) / φ G₀ with hq
  have hkey : ∀ (a : G) (F : Pontryagin.Algebra.MeasureTheory.L1G μ), φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F) = q a * φ F := by
    intro a F
    have h1 : φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a (F * G₀)) = φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F) * φ G₀ := by
      rw [Pontryagin.Algebra.MeasureTheory.L1G.translate_mul μ a F G₀, _root_.map_mul φ]
    have h2 : φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a (F * G₀)) = φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀) * φ F := by
      rw [mul_comm F G₀, Pontryagin.Algebra.MeasureTheory.L1G.translate_mul μ a G₀ F, _root_.map_mul φ]
    have h3 : φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a F) * φ G₀ = φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀) * φ F := h1.symm.trans h2
    simp only [hq]
    field_simp
    linear_combination h3
  have hq1 : q 1 = 1 := by
    simp only [hq]
    rw [Pontryagin.Algebra.MeasureTheory.L1G.translate_one μ G₀, div_self hG₀]
  have hqmul : ∀ a b : G, q (a * b) = q a * q b := by
    intro a b
    have h2 : φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ (a * b) G₀) = q a * q b * φ G₀ := by
      rw [← Pontryagin.Algebra.MeasureTheory.L1G.translate_translate μ a b G₀, hkey a (Pontryagin.Algebra.MeasureTheory.L1G.translate μ b G₀), hkey b G₀]
      ring
    have h3 : q (a * b) * φ G₀ = q a * q b * φ G₀ := by
      rw [← hkey (a * b) G₀, h2]
    exact mul_right_cancel₀ hG₀ h3
  have hqcont : Continuous q := by
    simp only [hq]
    exact (hφcont.comp (Pontryagin.Algebra.MeasureTheory.L1G.continuous_translate μ G₀)).div_const _
  -- Step 2: boundedness forces modulus one
  have hqbdd : ∀ a : G, ‖q a‖ ≤ ‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖ := by
    intro a
    have h1 : ‖φ (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀)‖ ≤ ‖toCLM φ‖ * ‖G₀‖ := by
      have h2 := (toCLM φ).le_opNorm (Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀)
      rwa [coe_toCLM, Pontryagin.Algebra.MeasureTheory.L1G.norm_translate] at h2
    simp only [hq]
    rw [norm_div]
    gcongr
  have hqpow : ∀ (a : G) (n : ℕ), q (a ^ n) = q a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hq1
    | succ n ih => rw [pow_succ, pow_succ, ← ih, ← hqmul]
  have hqle : ∀ a : G, ‖q a‖ ≤ 1 := by
    intro a
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖) hlt
    have h1 : ‖q (a ^ n)‖ ≤ ‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖ := hqbdd (a ^ n)
    rw [hqpow a n, norm_pow] at h1
    exact absurd h1 (not_le.mpr hn)
  have hqinv : ∀ a : G, q a * q a⁻¹ = 1 := by
    intro a
    rw [← hqmul, mul_inv_cancel]
    exact hq1
  have hqnorm : ∀ a : G, ‖q a‖ = 1 := by
    intro a
    refine le_antisymm (hqle a) ?_
    have h1 : ‖q a‖ * ‖q a⁻¹‖ = 1 := by rw [← norm_mul, hqinv a, norm_one]
    nlinarith [hqle a⁻¹, norm_nonneg (q a), norm_nonneg (q a⁻¹)]
  -- Step 3: the character of `G` given by `conj ∘ q`
  set χ : PontryaginDual G :=
    { toFun := fun x => ⟨conj (q x), mem_sphere_zero_iff_norm.mpr
        (by rw [RCLike.norm_conj]; exact hqnorm x)⟩
      map_one' := Circle.ext (show conj (q 1) = 1 by rw [hq1, _root_.map_one])
      map_mul' := fun x y => Circle.ext
        (show conj (q (x * y)) = conj (q x) * conj (q y) by rw [hqmul, _root_.map_mul])
      continuous_toFun := Continuous.subtype_mk
        (Complex.continuous_conj.comp hqcont) _ } with hχ
  have hχconj : ∀ x : G, conj ((χ x : Circle) : ℂ) = q x := fun x => by
    simp only [hχ]
    exact Complex.conj_conj (q x)
  -- Step 4: `φ` is integration against `q` on `C_c`
  have hrep : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f),
      φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) = FourierTransform.PontryaginDual.fourierTransform μ f χ := by
    intro f hfc hfs
    have hΦi : Integrable (fun a => f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hg₀c hg₀s)) μ :=
      Spectrum.MeasureTheory.integrable_smul_translateLp μ f hfc hfs _
    have hkey2 := congrArg (⇑(toCLM φ))
      (Spectrum.MeasureTheory.toLpCc_mconv_eq_integral μ f g₀ hfc hfs hg₀c hg₀s)
    -- the left side is `φ(F_f) · φ(G₀)`
    have h1 : Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g₀) (Convolution.Continuous.mconv (μ := μ) hfc hfs hg₀c hg₀s)
        (Convolution.HasCompactSupport.mconv (μ := μ) hfs hg₀s)) = Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs) * G₀ :=
      (congrArg (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ) (Pontryagin.Algebra.MeasureTheory.mulCLM_toLpCc μ f g₀ hfc hfs hg₀c hg₀s)).symm
    have hL : toCLM φ (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g₀) (Convolution.Continuous.mconv (μ := μ) hfc hfs hg₀c hg₀s)
        (Convolution.HasCompactSupport.mconv (μ := μ) hfs hg₀s)) = φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) * φ G₀ := by
      show φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ (Convolution.MeasureTheory.mconv μ f g₀) _ _)) = _
      rw [h1, _root_.map_mul φ]
    -- the right side is `(∫ f·q) · φ(G₀)`
    have hpt : ∀ a : G, toCLM φ (f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hg₀c hg₀s))
        = f a * q a * φ G₀ := by
      intro a
      have h4 : toCLM φ (f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hg₀c hg₀s))
          = φ (f a • Pontryagin.Algebra.MeasureTheory.L1G.translate μ a G₀) := rfl
      rw [h4, map_smul φ, hkey a G₀, smul_eq_mul]
      ring
    have hR : toCLM φ (∫ a, f a • Translation.MeasureTheory.translateLp μ 1 a (Pontryagin.Algebra.MeasureTheory.toLpCc μ g₀ hg₀c hg₀s) ∂μ)
        = (∫ a, f a * q a ∂μ) * φ G₀ := by
      rw [← ContinuousLinearMap.integral_comp_comm (toCLM φ) hΦi,
        integral_congr_ae (Eventually.of_forall hpt), integral_mul_const]
    have hEq : φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) * φ G₀ = (∫ a, f a * q a ∂μ) * φ G₀ := by
      rw [← hL, ← hR]
      exact hkey2
    have hφf : φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)) = ∫ a, f a * q a ∂μ :=
      mul_right_cancel₀ hG₀ hEq
    rw [hφf, FourierTransform.PontryaginDual.fourierTransform_apply]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show f a * q a = f a * conj ((χ a : Circle) : ℂ)
    rw [hχconj a]
  -- Step 5: density extends the representation to all of L¹
  have hall : ∀ F : Pontryagin.Algebra.MeasureTheory.L1G μ, φ F = Pontryagin.Algebra.MeasureTheory.L1G.fourier μ F χ := fun F =>
    Pontryagin.Algebra.MeasureTheory.funext_of_dense μ (fun Fp => φ (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ Fp)) (fun Fp => FourierTransform.PontryaginDual.fourierTransform μ ⇑Fp χ)
      hφcont (Spectrum.MeasureTheory.continuous_fourierTransform_coeFn μ χ)
      (fun f hfc hfs => by
        rw [Spectrum.MeasureTheory.fourierTransform_coeFn_toLpCc μ f hfc hfs]
        exact hrep f hfc hfs) (Pontryagin.Algebra.MeasureTheory.L1G.toLp μ F)
  -- uniqueness, by separation
  refine ⟨χ, hall, ?_⟩
  intro χ' hχ'
  by_contra hne
  obtain ⟨f, hfc, hfs, hsep⟩ := Spectrum.PontryaginDual.fourierTransform_separates μ hne
  have h1 : FourierTransform.PontryaginDual.fourierTransform μ f χ' = FourierTransform.PontryaginDual.fourierTransform μ f χ := by
    have e1 := (hχ' (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs))).symm.trans
      (hall (Pontryagin.Algebra.MeasureTheory.L1G.ofLp μ (Pontryagin.Algebra.MeasureTheory.toLpCc μ f hfc hfs)))
    rwa [Pontryagin.Algebra.MeasureTheory.L1G.fourier_ofLp_toLpCc μ f hfc hfs] at e1
  exact hsep h1

end

end OAI.Topology.Pontryagin
