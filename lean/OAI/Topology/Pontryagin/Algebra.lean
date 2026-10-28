import OAI.Topology.Pontryagin.Convolution
import OAI.Topology.Pontryagin.Density
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Algebra -/

namespace OAI.Topology.Pontryagin.Algebra.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# The convolution Banach algebra `L¹(G)`

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
equips (a type synonym of) `Lp ℂ 1 μ` with the structure of a commutative non-unital Banach
`*`-algebra whose multiplication is the **density extension** of the convolution of continuous
compactly supported functions. No product measures or product σ-algebras appear anywhere:
convolution is only ever computed pointwise on `C_c × C_c` (where `Pontryagin.Mathlib.CcFubini`
provides the iterated-integral manipulations) and then extended to all of `L¹` by bilinear
continuity along the dense subspace of `C_c` classes.

## Main definitions

* `ccSubmodule μ`: the subspace of `Lp ℂ 1 μ` of classes with a continuous compactly
 supported representative, with `dense_ccSubmodule`;
* `toLpCc μ f hfc hfs`: the `L¹` class of a continuous compactly supported function;
* `mulCLM μ: Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ`: convolution as a continuous bilinear
 map, obtained by extending `C_c` convolution twice along the dense inclusion
 (`ContinuousLinearMap.extend`);
* `L1star μ: Lp ℂ 1 μ → Lp ℂ 1 μ`: the isometric involution induced by
 `mstar f x = conj (f x⁻¹)`;
* `L1G μ`: a type synonym for `Lp ℂ 1 μ` carrying the instances
 `NonUnitalNormedCommRing`, `NormedSpace ℂ`, `IsScalarTower ℂ`, `SMulCommClass ℂ`,
 `StarRing`, `StarModule ℂ`, `NormedStarGroup`, `CompleteSpace`;
 conversions `L1G.ofLp` / `L1G.toLp` are the identity.

## Main results

* `mulCLM_toLpCc`: on `C_c` classes the multiplication is pointwise convolution:
 `mulCLM μ (toLpCc μ f _ _) (toLpCc μ g _ _) = toLpCc μ (mconv μ f g) _ _`;
* `norm_mulCLM_apply_le: ‖mulCLM μ F K‖ ≤ ‖F‖ * ‖K‖`;
* `mulCLM_comm`, `mulCLM_assoc`, `L1star_mulCLM`: the algebra laws, proved on `C_c` triples
 and extended by density and continuity;
* `L1G.norm_star: ‖star F‖ = ‖F‖`;
* `exists_bump_mconv_close`: the `C_c`-level approximate identity: for every continuous
 compactly supported `v` and `ε > 0` there is a neighborhood `U` of `1` such that every
 nonnegative normalized bump supported in `U` satisfies `∫ ‖(h ⋆ v) x - v x‖ ∂μ ≤ ε`;
* `L1G.exists_bump_mul_close`: the `L¹`-level approximate identity, together with
 `L1G.norm_bump: ‖L1G.bump μ h hc hs‖ = 1` for normalized bumps.
-/

open Function Set _root_.Topology Filter
open scoped ENNReal NNReal Pointwise ComplexConjugate

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

-- `show` is used pervasively to cross the definitional equality between the type synonym
-- `L1G μ` and `Lp ℂ 1 μ`, and to beta-reduce integrands.

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### Bilinearity of convolution of continuous compactly supported functions -/

section CcBilinear

variable {f g k : G → ℂ}

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- For `f` continuous compactly supported and `g` continuous, the convolution integrand
`y ↦ f y * g (y⁻¹ * x)` is integrable. -/
theorem integrable_mconv_integrand (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (x : G) : Integrable (fun y => f y * g (y⁻¹ * x)) μ := by
  have hc : Continuous fun y => f y * g (y⁻¹ * x) :=
    hf.mul (hg.comp (continuous_inv.mul continuous_const))
  exact hc.integrable_of_hasCompactSupport hf'.mul_right

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem mconv_add_left (hf : Continuous f) (hf' : HasCompactSupport f)
    (hk : Continuous k) (hk' : HasCompactSupport k) (hg : Continuous g) :
    Convolution.MeasureTheory.mconv μ (f + k) g = Convolution.MeasureTheory.mconv μ f g + Convolution.MeasureTheory.mconv μ k g := by
  funext x
  calc Convolution.MeasureTheory.mconv μ (f + k) g x
      = ∫ y, (f y * g (y⁻¹ * x) + k y * g (y⁻¹ * x)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [add_mul]
    _ = Convolution.MeasureTheory.mconv μ f g x + Convolution.MeasureTheory.mconv μ k g x :=
        integral_add (integrable_mconv_integrand μ hf hf' hg x)
          (integrable_mconv_integrand μ hk hk' hg x)
    _ = (Convolution.MeasureTheory.mconv μ f g + Convolution.MeasureTheory.mconv μ k g) x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
theorem mconv_smul_left (c : ℂ) (f g : G → ℂ) :
    Convolution.MeasureTheory.mconv μ (c • f) g = c • Convolution.MeasureTheory.mconv μ f g := by
  funext x
  calc Convolution.MeasureTheory.mconv μ (c • f) g x
      = ∫ y, c * (f y * g (y⁻¹ * x)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [mul_assoc]
    _ = c * Convolution.MeasureTheory.mconv μ f g x := integral_const_mul c _
    _ = (c • Convolution.MeasureTheory.mconv μ f g) x := rfl

omit [T2Space G] in
theorem mconv_add_right (hf : Continuous f) (hg : Continuous g) (hg' : HasCompactSupport g)
    (hk : Continuous k) (hk' : HasCompactSupport k) :
    Convolution.MeasureTheory.mconv μ f (g + k) = Convolution.MeasureTheory.mconv μ f g + Convolution.MeasureTheory.mconv μ f k := by
  rw [Convolution.MeasureTheory.mconv_comm μ f (g + k), Convolution.MeasureTheory.mconv_comm μ f g, Convolution.MeasureTheory.mconv_comm μ f k]
  exact mconv_add_left μ hg hg' hk hk' hf

omit [T2Space G] in
theorem mconv_smul_right (c : ℂ) (f g : G → ℂ) :
    Convolution.MeasureTheory.mconv μ f (c • g) = c • Convolution.MeasureTheory.mconv μ f g := by
  rw [Convolution.MeasureTheory.mconv_comm μ f (c • g), Convolution.MeasureTheory.mconv_comm μ f g]
  exact mconv_smul_left μ c g f

end CcBilinear

/-! ### The `C_c` classes inside `L¹` -/

section CcClasses

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem memLp_one_of_cc {f : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    MemLp f 1 μ :=
  memLp_one_iff_integrable.mpr (hfc.integrable_of_hasCompactSupport hfs)

/-- The `L¹` class of a continuous compactly supported function. -/
def toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) : Lp ℂ 1 μ :=
  (memLp_one_of_cc μ hfc hfs).toLp f

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem coeFn_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ⇑(toLpCc μ f hfc hfs) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem toLpCc_congr {f g : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hgc : Continuous g) (hgs : HasCompactSupport g) (h : f = g) :
    toLpCc μ f hfc hfs = toLpCc μ g hgc hgs := by
  subst h; rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- The `L¹` norm of a `C_c` class is the integral of the norm. -/
theorem norm_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ‖toLpCc μ f hfc hfs‖ = ∫ x, ‖f x‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toLpCc μ f hfc hfs] with x hx
  rw [hx]

omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The `L¹` norm of a difference, as an integral. -/
theorem norm_sub_eq_integral (F K : Lp ℂ 1 μ) : ‖F - K‖ = ∫ x, ‖F x - K x‖ ∂μ := by
  simpa only [dist_eq_norm] using L1.dist_eq_integral_dist F K

/-- The subspace of `L¹` classes possessing a continuous compactly supported
representative. -/
abbrev ccSubmodule : Submodule ℂ (Lp ℂ 1 μ) where
  carrier := {F | ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ ⇑F =ᵐ[μ] f}
  add_mem' := by
    rintro F K ⟨f, hfc, hfs, hf⟩ ⟨k, hkc, hks, hk⟩
    exact ⟨f + k, hfc.add hkc, hfs.add hks, (Lp.coeFn_add F K).trans (hf.add hk)⟩
  zero_mem' := ⟨0, continuous_const, HasCompactSupport.zero, Lp.coeFn_zero ℂ 1 μ⟩
  smul_mem' := by
    rintro c F ⟨f, hfc, hfs, hf⟩
    exact ⟨c • f, hfc.const_smul c, hfs.mono (support_const_smul_subset c f),
      (Lp.coeFn_smul c F).trans (hf.const_smul c)⟩

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
theorem mem_ccSubmodule_iff {F : Lp ℂ 1 μ} :
    F ∈ ccSubmodule μ ↔
      ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ ⇑F =ᵐ[μ] f :=
  Iff.rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem toLpCc_mem_ccSubmodule (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) : toLpCc μ f hfc hfs ∈ ccSubmodule μ :=
  ⟨f, hfc, hfs, coeFn_toLpCc μ f hfc hfs⟩

omit [IsTopologicalGroup G] in
/-- **Density of the `C_c` classes in `L¹`.** -/
theorem dense_ccSubmodule : Dense (ccSubmodule μ : Set (Lp ℂ 1 μ)) := by
  rw [Metric.dense_iff]
  intro F r hr
  obtain ⟨v, hvc, hvs, -, hv⟩ := Density.MeasureTheory.exists_hasCompactSupport_integral_norm_sub_le
    (memLp_one_iff_integrable.mp (Lp.memLp F)) (half_pos hr)
  have hnorm : ‖F - toLpCc μ v hvc hvs‖ ≤ r / 2 := by
    rw [norm_sub_eq_integral μ]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hv
    filter_upwards [coeFn_toLpCc μ v hvc hvs] with x hx
    rw [hx]
  refine ⟨toLpCc μ v hvc hvs, Metric.mem_ball.mpr ?_, toLpCc_mem_ccSubmodule μ v hvc hvs⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hnorm (half_lt_self hr)

omit [IsTopologicalGroup G] in
theorem denseRange_ccSubtypeL : DenseRange ⇑(ccSubmodule μ).subtypeL :=
  (dense_ccSubmodule μ).denseRange_val

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
theorem isUniformInducing_ccSubtypeL : IsUniformInducing ⇑(ccSubmodule μ).subtypeL :=
  isUniformEmbedding_subtype_val.isUniformInducing

omit [IsTopologicalGroup G] in
/-- A workhorse: two continuous functions on `L¹` agreeing on all `C_c` classes are equal. -/
theorem funext_of_dense {X : Type*} [TopologicalSpace X] [T2Space X]
    (T S : Lp ℂ 1 μ → X) (hT : Continuous T) (hS : Continuous S)
    (h : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f),
      T (toLpCc μ f hfc hfs) = S (toLpCc μ f hfc hfs)) (F : Lp ℂ 1 μ) :
    T F = S F := by
  have hTS : T = S := by
    refine Continuous.ext_on (dense_ccSubmodule μ) hT hS ?_
    intro F₀ hF₀
    obtain ⟨f, hfc, hfs, hf⟩ := (mem_ccSubmodule_iff μ).mp hF₀
    have hrw : F₀ = toLpCc μ f hfc hfs := Lp.ext (hf.trans (coeFn_toLpCc μ f hfc hfs).symm)
    rw [hrw]
    exact h f hfc hfs
  rw [hTS]

end CcClasses

/-! ### Convolution as a bilinear map on the `C_c` subspace -/

section CcMul

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem ccSubmodule_mem_def (F : ccSubmodule μ) :
    ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ ⇑(F : Lp ℂ 1 μ) =ᵐ[μ] f :=
  F.2

/-- A choice of continuous compactly supported representative for an element of
`ccSubmodule μ`. -/
private def ccRep (F : ccSubmodule μ) : G → ℂ :=
  (ccSubmodule_mem_def μ F).choose

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem ccRep_continuous (F : ccSubmodule μ) : Continuous (ccRep μ F) :=
  (ccSubmodule_mem_def μ F).choose_spec.1

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem ccRep_hasCompactSupport (F : ccSubmodule μ) : HasCompactSupport (ccRep μ F) :=
  (ccSubmodule_mem_def μ F).choose_spec.2.1

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem coeFn_ccRep (F : ccSubmodule μ) : ⇑(F : Lp ℂ 1 μ) =ᵐ[μ] ccRep μ F :=
  (ccSubmodule_mem_def μ F).choose_spec.2.2

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem ccRep_add (F K : ccSubmodule μ) :
    ccRep μ (F + K) =ᵐ[μ] ccRep μ F + ccRep μ K :=
  (coeFn_ccRep μ (F + K)).symm.trans
    ((Lp.coeFn_add (F : Lp ℂ 1 μ) (K : Lp ℂ 1 μ)).trans
      ((coeFn_ccRep μ F).add (coeFn_ccRep μ K)))

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem ccRep_smul (c : ℂ) (F : ccSubmodule μ) :
    ccRep μ (c • F) =ᵐ[μ] c • ccRep μ F :=
  (coeFn_ccRep μ (c • F)).symm.trans
    ((Lp.coeFn_smul c (F : Lp ℂ 1 μ)).trans ((coeFn_ccRep μ F).const_smul c))

/-- Convolution of two elements of the `C_c` subspace, as an element of `L¹`. -/
def ccMul (F K : ccSubmodule μ) : Lp ℂ 1 μ :=
  toLpCc μ (Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K))
    (Convolution.Continuous.mconv (μ := μ) (ccRep_continuous μ F) (MeasureTheory.ccRep_hasCompactSupport μ F)
      (MeasureTheory.ccRep_continuous μ K) (MeasureTheory.ccRep_hasCompactSupport μ K))
    (Convolution.HasCompactSupport.mconv (μ := μ) (ccRep_hasCompactSupport μ F) (MeasureTheory.ccRep_hasCompactSupport μ K))

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
theorem coeFn_ccMul (F K : ccSubmodule μ) :
    ⇑(ccMul μ F K) =ᵐ[μ] Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) :=
  coeFn_toLpCc μ _ _ _

omit [T2Space G] in
/-- `ccMul` only depends on (arbitrary continuous compactly supported) representatives. -/
theorem ccMul_eq_toLpCc {F K : ccSubmodule μ} {f k : G → ℂ}
    (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hkc : Continuous k) (hks : HasCompactSupport k)
    (hf : ⇑(F : Lp ℂ 1 μ) =ᵐ[μ] f) (hk : ⇑(K : Lp ℂ 1 μ) =ᵐ[μ] k) :
    ccMul μ F K = toLpCc μ (Convolution.MeasureTheory.mconv μ f k) (Convolution.Continuous.mconv (μ := μ) hfc hfs hkc hks) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hks) := by
  have h : Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) = Convolution.MeasureTheory.mconv μ f k :=
    Convolution.MeasureTheory.mconv_congr_ae μ ((coeFn_ccRep μ F).symm.trans hf) ((coeFn_ccRep μ K).symm.trans hk)
  refine Lp.ext ((coeFn_ccMul μ F K).trans ?_)
  rw [h]
  exact (coeFn_toLpCc μ _ _ _).symm

omit [T2Space G] in
theorem ccMul_add_left (F F' K : ccSubmodule μ) :
    ccMul μ (F + F') K = ccMul μ F K + ccMul μ F' K := by
  have h : Convolution.MeasureTheory.mconv μ (ccRep μ (F + F')) (ccRep μ K)
      = Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) + Convolution.MeasureTheory.mconv μ (ccRep μ F') (ccRep μ K) := by
    rw [Convolution.MeasureTheory.mconv_congr_ae μ (ccRep_add μ F F') (Filter.EventuallyEq.refl _ _)]
    exact mconv_add_left μ (MeasureTheory.ccRep_continuous μ F) (MeasureTheory.ccRep_hasCompactSupport μ F)
      (MeasureTheory.ccRep_continuous μ F') (MeasureTheory.ccRep_hasCompactSupport μ F') (MeasureTheory.ccRep_continuous μ K)
  refine Lp.ext ?_
  filter_upwards [coeFn_ccMul μ (F + F') K,
    Lp.coeFn_add (ccMul μ F K) (ccMul μ F' K), coeFn_ccMul μ F K, coeFn_ccMul μ F' K]
    with x h1 h2 h3 h4
  rw [h1, h, h2, Pi.add_apply, Pi.add_apply, h3, h4]

omit [T2Space G] in
theorem ccMul_smul_left (c : ℂ) (F K : ccSubmodule μ) :
    ccMul μ (c • F) K = c • ccMul μ F K := by
  have h : Convolution.MeasureTheory.mconv μ (ccRep μ (c • F)) (ccRep μ K)
      = c • Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) := by
    rw [Convolution.MeasureTheory.mconv_congr_ae μ (ccRep_smul μ c F) (Filter.EventuallyEq.refl _ _)]
    exact mconv_smul_left μ c _ _
  refine Lp.ext ?_
  filter_upwards [coeFn_ccMul μ (c • F) K, Lp.coeFn_smul c (ccMul μ F K), coeFn_ccMul μ F K]
    with x h1 h2 h3
  rw [h1, h, h2, Pi.smul_apply, Pi.smul_apply, h3]

omit [T2Space G] in
theorem ccMul_add_right (F K K' : ccSubmodule μ) :
    ccMul μ F (K + K') = ccMul μ F K + ccMul μ F K' := by
  have h : Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ (K + K'))
      = Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) + Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K') := by
    rw [Convolution.MeasureTheory.mconv_congr_ae μ (Filter.EventuallyEq.refl _ _) (ccRep_add μ K K')]
    exact mconv_add_right μ (MeasureTheory.ccRep_continuous μ F) (MeasureTheory.ccRep_continuous μ K)
      (MeasureTheory.ccRep_hasCompactSupport μ K) (MeasureTheory.ccRep_continuous μ K') (MeasureTheory.ccRep_hasCompactSupport μ K')
  refine Lp.ext ?_
  filter_upwards [coeFn_ccMul μ F (K + K'),
    Lp.coeFn_add (ccMul μ F K) (ccMul μ F K'), coeFn_ccMul μ F K, coeFn_ccMul μ F K']
    with x h1 h2 h3 h4
  rw [h1, h, h2, Pi.add_apply, Pi.add_apply, h3, h4]

omit [T2Space G] in
theorem ccMul_smul_right (c : ℂ) (F K : ccSubmodule μ) :
    ccMul μ F (c • K) = c • ccMul μ F K := by
  have h : Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ (c • K))
      = c • Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) := by
    rw [Convolution.MeasureTheory.mconv_congr_ae μ (Filter.EventuallyEq.refl _ _) (ccRep_smul μ c K)]
    exact mconv_smul_right μ c _ _
  refine Lp.ext ?_
  filter_upwards [coeFn_ccMul μ F (c • K), Lp.coeFn_smul c (ccMul μ F K), coeFn_ccMul μ F K]
    with x h1 h2 h3
  rw [h1, h, h2, Pi.smul_apply, Pi.smul_apply, h3]

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- The fundamental `L¹` bound `‖F ⋆ K‖₁ ≤ ‖F‖₁ * ‖K‖₁` on the `C_c` subspace. -/
theorem norm_ccMul_le (F K : ccSubmodule μ) : ‖ccMul μ F K‖ ≤ ‖F‖ * ‖K‖ := by
  have h1 : ‖ccMul μ F K‖ = ∫ x, ‖Convolution.MeasureTheory.mconv μ (ccRep μ F) (ccRep μ K) x‖ ∂μ :=
    norm_toLpCc μ _ _ _
  have h2 : ‖F‖ = ∫ x, ‖ccRep μ F x‖ ∂μ := by
    rw [← Submodule.norm_coe, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_ccRep μ F] with x hx
    rw [hx]
  have h3 : ‖K‖ = ∫ x, ‖ccRep μ K x‖ ∂μ := by
    rw [← Submodule.norm_coe, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_ccRep μ K] with x hx
    rw [hx]
  rw [h1, h2, h3]
  exact Convolution.MeasureTheory.integral_norm_mconv_le μ (MeasureTheory.ccRep_continuous μ F) (MeasureTheory.ccRep_hasCompactSupport μ F)
    (MeasureTheory.ccRep_continuous μ K) (MeasureTheory.ccRep_hasCompactSupport μ K)

-- Fix the norm topology on the nested operator space for Lean 4.33.
local instance : NormedAddCommGroup (ccSubmodule μ →L[ℂ] Lp ℂ 1 μ) := inferInstance
local instance : NormedSpace ℂ (ccSubmodule μ →L[ℂ] Lp ℂ 1 μ) := inferInstance

/-- Convolution as a continuous bilinear map on the `C_c` subspace. -/
def ccMulCLM : ccSubmodule μ →L[ℂ] ccSubmodule μ →L[ℂ] Lp ℂ 1 μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (ccMul μ) (fun F F' K => ccMul_add_left μ F F' K)
      (fun c F K => ccMul_smul_left μ c F K) (fun F K K' => ccMul_add_right μ F K K')
      (fun c F K => ccMul_smul_right μ c F K))
    1 (fun F K => by rw [one_mul]; exact norm_ccMul_le μ F K)

omit [T2Space G] in
theorem ccMulCLM_apply (F K : ccSubmodule μ) : ccMulCLM μ F K = ccMul μ F K := rfl

omit [T2Space G] in
theorem norm_ccMulCLM_le : ‖ccMulCLM μ‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end CcMul

/-! ### The multiplication on all of `L¹` by double density extension -/

section MulCLM

local instance : NormedAddCommGroup (ccSubmodule μ →L[ℂ] Lp ℂ 1 μ) := inferInstance
local instance : NormedSpace ℂ (ccSubmodule μ →L[ℂ] Lp ℂ 1 μ) := inferInstance

/-- First extension: `C_c` convolution, extended to an `L¹` first argument. -/
private def mulCLMAux : Lp ℂ 1 μ →L[ℂ] ccSubmodule μ →L[ℂ] Lp ℂ 1 μ :=
  (ccMulCLM μ).extend (ccSubmodule μ).subtypeL

/-- **Convolution as a continuous bilinear multiplication on `L¹(G)`**, obtained from
`C_c × C_c` convolution by extending twice along the dense inclusion of the `C_c`
subspace. -/
def mulCLM : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ :=
  ((mulCLMAux μ).flip.extend (ccSubmodule μ).subtypeL).flip

/-- On the `C_c` subspace, `mulCLM` is `ccMul`. -/
theorem mulCLM_coe_coe (F K : ccSubmodule μ) :
    mulCLM μ (F : Lp ℂ 1 μ) (K : Lp ℂ 1 μ) = ccMul μ F K :=
  calc mulCLM μ (F : Lp ℂ 1 μ) (K : Lp ℂ 1 μ)
      = (mulCLMAux μ).flip.extend (ccSubmodule μ).subtypeL
          ((ccSubmodule μ).subtypeL K) (F : Lp ℂ 1 μ) := rfl
    _ = (mulCLMAux μ).flip K (F : Lp ℂ 1 μ) :=
        DFunLike.congr_fun (((mulCLMAux μ).flip).extend_eq (denseRange_ccSubtypeL μ)
          (isUniformInducing_ccSubtypeL μ) K) (F : Lp ℂ 1 μ)
    _ = (ccMulCLM μ).extend (ccSubmodule μ).subtypeL ((ccSubmodule μ).subtypeL F) K := rfl
    _ = ccMulCLM μ F K :=
        DFunLike.congr_fun ((ccMulCLM μ).extend_eq (denseRange_ccSubtypeL μ)
          (isUniformInducing_ccSubtypeL μ) F) K
    _ = ccMul μ F K := rfl

/-- **Agreement of the extended multiplication with pointwise convolution** on continuous
compactly supported functions. -/
theorem mulCLM_toLpCc (f g : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs)
      = toLpCc μ (Convolution.MeasureTheory.mconv μ f g) (Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs) (Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs) := by
  have h := mulCLM_coe_coe μ ⟨toLpCc μ f hfc hfs, toLpCc_mem_ccSubmodule μ f hfc hfs⟩
    ⟨toLpCc μ g hgc hgs, toLpCc_mem_ccSubmodule μ g hgc hgs⟩
  rw [h]
  exact ccMul_eq_toLpCc μ hfc hfs hgc hgs (coeFn_toLpCc μ f hfc hfs) (coeFn_toLpCc μ g hgc hgs)

theorem opNorm_mulCLM_le : ‖mulCLM μ‖ ≤ 1 := by
  have he : ∀ x : ccSubmodule μ, ‖x‖ ≤ ((1 : ℝ≥0) : ℝ) * ‖(ccSubmodule μ).subtypeL x‖ := by
    intro x
    rw [NNReal.coe_one, one_mul, Submodule.subtypeL_apply, ← Submodule.norm_coe]
  have h2 := (ccMulCLM μ).opNorm_extend_le (N := 1) (denseRange_ccSubtypeL μ) he
  have h3 := ((mulCLMAux μ).flip).opNorm_extend_le (N := 1) (denseRange_ccSubtypeL μ) he
  rw [NNReal.coe_one, one_mul] at h2 h3
  calc ‖mulCLM μ‖
      = ‖(mulCLMAux μ).flip.extend (ccSubmodule μ).subtypeL‖ :=
        ContinuousLinearMap.opNorm_flip _
    _ ≤ ‖(mulCLMAux μ).flip‖ := h3
    _ = ‖mulCLMAux μ‖ := ContinuousLinearMap.opNorm_flip _
    _ ≤ ‖ccMulCLM μ‖ := h2
    _ ≤ 1 := norm_ccMulCLM_le μ

/-- The `L¹` norm bound `‖F * K‖ ≤ ‖F‖ * ‖K‖`. -/
theorem norm_mulCLM_apply_le (F K : Lp ℂ 1 μ) : ‖mulCLM μ F K‖ ≤ ‖F‖ * ‖K‖ := by
  refine ((mulCLM μ).le_opNorm₂ F K).trans ?_
  calc ‖mulCLM μ‖ * ‖F‖ * ‖K‖
      ≤ 1 * ‖F‖ * ‖K‖ := by
        gcongr
        exact opNorm_mulCLM_le μ
    _ = ‖F‖ * ‖K‖ := by rw [one_mul]

/-- Commutativity, by density from `mconv_comm`. -/
theorem mulCLM_comm (F K : Lp ℂ 1 μ) : mulCLM μ F K = mulCLM μ K F := by
  have step1 : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
      (F : Lp ℂ 1 μ),
      mulCLM μ F (toLpCc μ g hgc hgs) = mulCLM μ (toLpCc μ g hgc hgs) F := by
    intro g hgc hgs
    refine funext_of_dense μ (fun F => mulCLM μ F (toLpCc μ g hgc hgs))
      (fun F => mulCLM μ (toLpCc μ g hgc hgs) F)
      (((mulCLM μ).flip (toLpCc μ g hgc hgs)).continuous)
      ((mulCLM μ (toLpCc μ g hgc hgs)).continuous) ?_
    intro f hfc hfs
    rw [mulCLM_toLpCc μ f g hfc hfs hgc hgs, mulCLM_toLpCc μ g f hgc hgs hfc hfs]
    exact toLpCc_congr μ _ _ _ _ (Convolution.MeasureTheory.mconv_comm μ f g)
  refine funext_of_dense μ (fun K => mulCLM μ F K) (fun K => mulCLM μ K F)
    ((mulCLM μ F).continuous) (((mulCLM μ).flip F).continuous) ?_ K
  intro g hgc hgs
  exact step1 g hgc hgs F

/-- Associativity, by density from `mconv_assoc`. -/
theorem mulCLM_assoc (F K H : Lp ℂ 1 μ) :
    mulCLM μ (mulCLM μ F K) H = mulCLM μ F (mulCLM μ K H) := by
  -- all three continuous compactly supported
  have base : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
      (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
      (w : G → ℂ) (hwc : Continuous w) (hws : HasCompactSupport w),
      mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs)) (toLpCc μ w hwc hws)
        = mulCLM μ (toLpCc μ f hfc hfs)
            (mulCLM μ (toLpCc μ g hgc hgs) (toLpCc μ w hwc hws)) := by
    intro f hfc hfs g hgc hgs w hwc hws
    rw [mulCLM_toLpCc μ f g hfc hfs hgc hgs, mulCLM_toLpCc μ g w hgc hgs hwc hws,
      mulCLM_toLpCc μ (Convolution.MeasureTheory.mconv μ f g) w _ _ hwc hws,
      mulCLM_toLpCc μ f (Convolution.MeasureTheory.mconv μ g w) hfc hfs _ _]
    exact toLpCc_congr μ _ _ _ _ (Convolution.MeasureTheory.mconv_assoc μ hfc hfs hgc hgs hwc hws)
  -- extend in the last argument
  have stepH : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
      (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g) (H : Lp ℂ 1 μ),
      mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs)) H
        = mulCLM μ (toLpCc μ f hfc hfs) (mulCLM μ (toLpCc μ g hgc hgs) H) := by
    intro f hfc hfs g hgc hgs
    refine funext_of_dense μ
      (fun H => mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs)) H)
      (fun H => mulCLM μ (toLpCc μ f hfc hfs) (mulCLM μ (toLpCc μ g hgc hgs) H))
      ((mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs))).continuous)
      ((mulCLM μ (toLpCc μ f hfc hfs)).continuous.comp
        (mulCLM μ (toLpCc μ g hgc hgs)).continuous) ?_
    intro w hwc hws
    exact base f hfc hfs g hgc hgs w hwc hws
  -- extend in the middle argument
  have stepK : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
      (K H : Lp ℂ 1 μ),
      mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) K) H
        = mulCLM μ (toLpCc μ f hfc hfs) (mulCLM μ K H) := by
    intro f hfc hfs K H
    refine funext_of_dense μ
      (fun K => mulCLM μ (mulCLM μ (toLpCc μ f hfc hfs) K) H)
      (fun K => mulCLM μ (toLpCc μ f hfc hfs) (mulCLM μ K H))
      ((((mulCLM μ).flip H).continuous).comp (mulCLM μ (toLpCc μ f hfc hfs)).continuous)
      ((mulCLM μ (toLpCc μ f hfc hfs)).continuous.comp (((mulCLM μ).flip H).continuous)) ?_ K
    intro g hgc hgs
    exact stepH f hfc hfs g hgc hgs H
  -- extend in the first argument
  refine funext_of_dense μ
    (fun F => mulCLM μ (mulCLM μ F K) H) (fun F => mulCLM μ F (mulCLM μ K H))
    ((((mulCLM μ).flip H).continuous).comp (((mulCLM μ).flip K).continuous))
    (((mulCLM μ).flip (mulCLM μ K H)).continuous) ?_ F
  intro f hfc hfs
  exact stepK f hfc hfs K H

end MulCLM

/-! ### The star involution on `L¹` -/

section Star

omit [T2Space G] in
theorem mstar_congr_ae {f g : G → ℂ} (h : f =ᵐ[μ] g) : Convolution.MeasureTheory.mstar f =ᵐ[μ] Convolution.MeasureTheory.mstar g := by
  have h2 : (f ∘ fun x : G => x⁻¹) =ᵐ[μ] (g ∘ fun x : G => x⁻¹) :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h2] with x hx
  simp only [Convolution.MeasureTheory.mstar_apply]
  exact congrArg conj hx

/-- The star involution on `L¹`: the class of `mstar` of a representative. -/
def L1star (F : Lp ℂ 1 μ) : Lp ℂ 1 μ :=
  (Convolution.MeasureTheory.MemLp.mstar (μ := μ) (Lp.memLp F)).toLp (Convolution.MeasureTheory.mstar ⇑F)

omit [T2Space G] in
theorem coeFn_L1star (F : Lp ℂ 1 μ) : ⇑(L1star μ F) =ᵐ[μ] Convolution.MeasureTheory.mstar ⇑F :=
  MemLp.coeFn_toLp _

omit [T2Space G] in
theorem L1star_congr {F : Lp ℂ 1 μ} {f : G → ℂ} (h : ⇑F =ᵐ[μ] f) :
    ⇑(L1star μ F) =ᵐ[μ] Convolution.MeasureTheory.mstar f :=
  (coeFn_L1star μ F).trans (mstar_congr_ae μ h)

omit [T2Space G] in
theorem L1star_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    L1star μ (toLpCc μ f hfc hfs) = toLpCc μ (Convolution.MeasureTheory.mstar f) (Convolution.Continuous.mstar hfc) (Convolution.HasCompactSupport.mstar hfs) :=
  Lp.ext ((L1star_congr μ (coeFn_toLpCc μ f hfc hfs)).trans (coeFn_toLpCc μ _ _ _).symm)

omit [T2Space G] in
theorem L1star_add (F K : Lp ℂ 1 μ) :
    L1star μ (F + K) = L1star μ F + L1star μ K := by
  refine Lp.ext ?_
  filter_upwards [L1star_congr μ (Lp.coeFn_add F K),
    Lp.coeFn_add (L1star μ F) (L1star μ K), coeFn_L1star μ F, coeFn_L1star μ K]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4]
  simp [Convolution.MeasureTheory.mstar_apply, Pi.add_apply]

omit [T2Space G] in
theorem L1star_sub (F K : Lp ℂ 1 μ) :
    L1star μ (F - K) = L1star μ F - L1star μ K := by
  refine Lp.ext ?_
  filter_upwards [L1star_congr μ (Lp.coeFn_sub F K),
    Lp.coeFn_sub (L1star μ F) (L1star μ K), coeFn_L1star μ F, coeFn_L1star μ K]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4]
  simp [Convolution.MeasureTheory.mstar_apply, Pi.sub_apply]

omit [T2Space G] in
theorem L1star_smul (c : ℂ) (F : Lp ℂ 1 μ) :
    L1star μ (c • F) = conj c • L1star μ F := by
  refine Lp.ext ?_
  filter_upwards [L1star_congr μ (Lp.coeFn_smul c F),
    Lp.coeFn_smul (conj c) (L1star μ F), coeFn_L1star μ F] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  simp [Convolution.MeasureTheory.mstar_apply, Pi.smul_apply, smul_eq_mul]

omit [T2Space G] in
theorem L1star_L1star (F : Lp ℂ 1 μ) : L1star μ (L1star μ F) = F := by
  refine Lp.ext ?_
  have h1 : ⇑(L1star μ (L1star μ F)) =ᵐ[μ] Convolution.MeasureTheory.mstar (Convolution.MeasureTheory.mstar ⇑F) :=
    L1star_congr μ (coeFn_L1star μ F)
  simpa [Convolution.MeasureTheory.mstar_mstar] using h1

omit [T2Space G] in
theorem norm_L1star (F : Lp ℂ 1 μ) : ‖L1star μ F‖ = ‖F‖ := by
  rw [L1star, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact Convolution.MeasureTheory.eLpNorm_mstar μ (Lp.aestronglyMeasurable F)

omit [T2Space G] in
theorem isometry_L1star : Isometry (L1star μ) :=
  Isometry.of_dist_eq fun F K => by
    rw [dist_eq_norm, dist_eq_norm, ← L1star_sub μ F K, norm_L1star μ]

omit [T2Space G] in
theorem continuous_L1star : Continuous (L1star μ) :=
  (isometry_L1star μ).continuous

/-- The star involution distributes over the extended convolution (the algebra is
commutative, so no order reversal is visible here). -/
theorem L1star_mulCLM (F K : Lp ℂ 1 μ) :
    L1star μ (mulCLM μ F K) = mulCLM μ (L1star μ F) (L1star μ K) := by
  have base : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
      (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g),
      L1star μ (mulCLM μ (toLpCc μ f hfc hfs) (toLpCc μ g hgc hgs))
        = mulCLM μ (L1star μ (toLpCc μ f hfc hfs)) (L1star μ (toLpCc μ g hgc hgs)) := by
    intro f hfc hfs g hgc hgs
    rw [mulCLM_toLpCc μ f g hfc hfs hgc hgs, L1star_toLpCc μ (Convolution.MeasureTheory.mconv μ f g) _ _,
      L1star_toLpCc μ f hfc hfs, L1star_toLpCc μ g hgc hgs,
      mulCLM_toLpCc μ (Convolution.MeasureTheory.mstar f) (Convolution.MeasureTheory.mstar g) _ _ _ _]
    exact toLpCc_congr μ _ _ _ _ (Convolution.MeasureTheory.mstar_mconv μ f g)
  have stepF : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
      (F : Lp ℂ 1 μ),
      L1star μ (mulCLM μ F (toLpCc μ g hgc hgs))
        = mulCLM μ (L1star μ F) (L1star μ (toLpCc μ g hgc hgs)) := by
    intro g hgc hgs
    refine funext_of_dense μ
      (fun F => L1star μ (mulCLM μ F (toLpCc μ g hgc hgs)))
      (fun F => mulCLM μ (L1star μ F) (L1star μ (toLpCc μ g hgc hgs)))
      ((continuous_L1star μ).comp (((mulCLM μ).flip (toLpCc μ g hgc hgs)).continuous))
      ((((mulCLM μ).flip (L1star μ (toLpCc μ g hgc hgs))).continuous).comp
        (continuous_L1star μ)) ?_
    intro f hfc hfs
    exact base f hfc hfs g hgc hgs
  refine funext_of_dense μ
    (fun K => L1star μ (mulCLM μ F K)) (fun K => mulCLM μ (L1star μ F) (L1star μ K))
    ((continuous_L1star μ).comp ((mulCLM μ F).continuous))
    (((mulCLM μ (L1star μ F)).continuous).comp (continuous_L1star μ)) ?_ K
  intro g hgc hgs
  exact stepF g hgc hgs F

end Star

/-! ### The Banach algebra `L1G` -/

/-- Type synonym for `Lp ℂ 1 μ` carrying the convolution Banach-`*`-algebra structure.
Convert with the identity maps `L1G.ofLp` and `L1G.toLp`. -/
def L1G (μ : Measure G) : Type _ := Lp ℂ 1 μ

namespace L1G

instance : NormedAddCommGroup (L1G μ) :=
  inferInstanceAs (NormedAddCommGroup (Lp ℂ 1 μ))

instance : NormedSpace ℂ (L1G μ) :=
  inferInstanceAs (NormedSpace ℂ (Lp ℂ 1 μ))

instance : CompleteSpace (L1G μ) :=
  inferInstanceAs (CompleteSpace (Lp ℂ 1 μ))

/-- Convert an `Lp` class into `L1G` (the identity map). -/
def ofLp (F : Lp ℂ 1 μ) : L1G μ := F

/-- Convert an `L1G` element into an `Lp` class (the identity map). -/
def toLp (F : L1G μ) : Lp ℂ 1 μ := F

omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem toLp_ofLp (F : Lp ℂ 1 μ) : L1G.toLp μ (ofLp μ F) = F := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem ofLp_toLp (F : L1G μ) : ofLp μ (L1G.toLp μ F) = F := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem norm_ofLp (F : Lp ℂ 1 μ) : ‖ofLp μ F‖ = ‖F‖ := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem norm_toLp (F : L1G μ) : ‖L1G.toLp μ F‖ = ‖F‖ := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem ofLp_add (F K : Lp ℂ 1 μ) : ofLp μ (F + K) = ofLp μ F + ofLp μ K := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem ofLp_sub (F K : Lp ℂ 1 μ) : ofLp μ (F - K) = ofLp μ F - ofLp μ K := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem ofLp_smul (c : ℂ) (F : Lp ℂ 1 μ) : ofLp μ (c • F) = c • ofLp μ F := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem toLp_add (F K : L1G μ) : L1G.toLp μ (F + K) = L1G.toLp μ F + L1G.toLp μ K := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem toLp_sub (F K : L1G μ) : L1G.toLp μ (F - K) = L1G.toLp μ F - L1G.toLp μ K := rfl
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
@[simp] theorem toLp_smul (c : ℂ) (F : L1G μ) : L1G.toLp μ (c • F) = c • L1G.toLp μ F := rfl

/-- The commutative non-unital normed ring structure on `L1G μ`: multiplication is the
density extension `mulCLM` of `C_c` convolution. -/
instance : NonUnitalNormedCommRing (L1G μ) :=
  let base : NormedAddCommGroup (L1G μ) := inferInstanceAs (NormedAddCommGroup (L1G μ))
  { base with
    mul := fun F K => ofLp μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K))
    left_distrib := fun F K H => by
      show ofLp μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K + L1G.toLp μ H)) = _
      rw [map_add]
      rfl
    right_distrib := fun F K H => by
      show ofLp μ (mulCLM μ (L1G.toLp μ F + L1G.toLp μ K) (L1G.toLp μ H)) = _
      rw [map_add, add_apply]
      rfl
    zero_mul := fun F => by
      show ofLp μ (mulCLM μ 0 (L1G.toLp μ F)) = 0
      rw [map_zero, zero_apply]
      rfl
    mul_zero := fun F => by
      show ofLp μ (mulCLM μ (L1G.toLp μ F) 0) = 0
      rw [map_zero]
      rfl
    mul_assoc := fun F K H => by
      show ofLp μ (mulCLM μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K)) (L1G.toLp μ H)) = _
      rw [mulCLM_assoc μ]
      rfl
    mul_comm := fun F K => congrArg (ofLp μ) (mulCLM_comm μ (L1G.toLp μ F) (L1G.toLp μ K))
    norm_mul_le := fun F K => norm_mulCLM_apply_le μ (L1G.toLp μ F) (L1G.toLp μ K) }

theorem mul_def (F K : L1G μ) : F * K = ofLp μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K)) := rfl

@[simp] theorem toLp_mul (F K : L1G μ) :
    L1G.toLp μ (F * K) = mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K) := rfl

instance : IsScalarTower ℂ (L1G μ) (L1G μ) where
  smul_assoc c F K := by
    show ofLp μ (mulCLM μ (c • L1G.toLp μ F) (L1G.toLp μ K))
      = c • ofLp μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K))
    rw [map_smul, smul_apply]
    rfl

instance : SMulCommClass ℂ (L1G μ) (L1G μ) where
  smul_comm c F K := by
    show c • ofLp μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K))
      = ofLp μ (mulCLM μ (L1G.toLp μ F) (c • L1G.toLp μ K))
    rw [(mulCLM μ (L1G.toLp μ F)).map_smul]
    rfl

/-- The star ring structure induced by `mstar f x = conj (f x⁻¹)`. -/
instance : StarRing (L1G μ) where
  star F := ofLp μ (L1star μ (L1G.toLp μ F))
  star_involutive F := congrArg (ofLp μ) (L1star_L1star μ (L1G.toLp μ F))
  star_mul F K := by
    show ofLp μ (L1star μ (mulCLM μ (L1G.toLp μ F) (L1G.toLp μ K)))
      = ofLp μ (mulCLM μ (L1star μ (L1G.toLp μ K)) (L1star μ (L1G.toLp μ F)))
    rw [L1star_mulCLM μ, mulCLM_comm μ]
  star_add F K := congrArg (ofLp μ) (L1star_add μ (L1G.toLp μ F) (L1G.toLp μ K))

theorem star_def (F : L1G μ) : star F = ofLp μ (L1star μ (L1G.toLp μ F)) := rfl

instance : StarModule ℂ (L1G μ) where
  star_smul c F := by
    show ofLp μ (L1star μ (c • L1G.toLp μ F)) = star c • ofLp μ (L1star μ (L1G.toLp μ F))
    rw [L1star_smul μ]
    rfl

/-- The star involution is isometric. -/
theorem norm_star (F : L1G μ) : ‖star F‖ = ‖F‖ :=
  norm_L1star μ (L1G.toLp μ F)

instance : NormedStarGroup (L1G μ) :=
  ⟨fun F => le_of_eq (norm_star μ F)⟩

end L1G

/-! ### The approximate identity -/

omit [T2Space G] in
/-- **`C_c`-level approximate identity.** For a continuous compactly supported `v` and
`ε > 0`, there is a neighborhood `U` of `1` such that for every nonnegative continuous
compactly supported `h` supported in `U` with `∫ h ∂μ = 1`, the convolution `h ⋆ v` is
within `ε` of `v` in the `L¹` seminorm. -/
theorem exists_bump_mconv_close (v : G → ℂ) (hv : Continuous v)
    (hv' : HasCompactSupport v) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : G), ∀ h : G → ℝ, Continuous h → HasCompactSupport h →
      (∀ x, 0 ≤ h x) → tsupport h ⊆ U → (∫ x, h x ∂μ) = 1 →
      ∫ x, ‖Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v x - v x‖ ∂μ ≤ ε := by
  obtain ⟨C, hCcomp, hCmem⟩ := exists_compact_mem_nhds (1 : G)
  set V : Lp ℂ 1 μ := toLpCc μ v hv hv' with hVdef
  set φ : G → ℝ := fun y => ‖Translation.MeasureTheory.translateLp μ 1 y V - V‖ with hφdef
  have hφcont : Continuous φ :=
    ((Translation.MeasureTheory.continuous_translateLp μ 1 ENNReal.one_ne_top V).sub continuous_const).norm
  have hφ1 : φ 1 = 0 := by
    simp only [hφdef, Translation.MeasureTheory.translateLp_one, sub_self, norm_zero]
  -- The translation defect in `L¹`, computed as an integral.
  have hφeq : ∀ y : G, ∫ x, ‖v (y⁻¹ * x) - v x‖ ∂μ = φ y := by
    intro y
    have h2 : ⇑(Translation.MeasureTheory.translateLp μ 1 y V) =ᵐ[μ] Translation.MeasureTheory.mtranslate y v :=
      (Translation.MeasureTheory.coeFn_translateLp μ 1 y V).trans
        ((measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae_eq_comp
          (coeFn_toLpCc μ v hv hv'))
    simp only [hφdef]
    rw [L1.norm_eq_integral_norm]
    refine (integral_congr_ae ?_).symm
    filter_upwards [Lp.coeFn_sub (Translation.MeasureTheory.translateLp μ 1 y V) V, h2, coeFn_toLpCc μ v hv hv']
      with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, hx3]
    rfl
  refine ⟨interior C ∩ {y | φ y < ε},
    inter_mem (interior_mem_nhds.mpr hCmem)
      ((isOpen_lt hφcont continuous_const).mem_nhds (by simp [hφ1, hε])), ?_⟩
  intro h hc hs h0 hsupp hint
  have hsuppC : tsupport h ⊆ C :=
    hsupp.trans (inter_subset_left.trans interior_subset)
  have hsuppφ : ∀ y ∈ tsupport h, φ y < ε := fun y hy => (hsupp hy).2
  have hcℂ : Continuous fun y => ((h y : ℝ) : ℂ) := Complex.continuous_ofReal.comp hc
  have hsℂ : HasCompactSupport fun y => ((h y : ℝ) : ℂ) :=
    hs.comp_left Complex.ofReal_zero
  have hintℂ : ∫ y, ((h y : ℝ) : ℂ) ∂μ = 1 := by
    have h1 : ∫ y, ((h y : ℝ) : ℂ) ∂μ = ((∫ y, h y ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [h1, hint, Complex.ofReal_one]
  -- integrability of the difference
  have hdiff_int : Integrable (fun x => ‖Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v x - v x‖) μ :=
    (((Convolution.Continuous.mconv (μ := μ) hcℂ hsℂ hv hv').sub hv).integrable_of_hasCompactSupport
      ((Convolution.HasCompactSupport.mconv (μ := μ) hsℂ hv').sub hv')).norm
  -- the kernel `W x y = h y * ‖v (y⁻¹ x) - v x‖`
  have hWc : Continuous (uncurry fun x y : G => h y * ‖v (y⁻¹ * x) - v x‖) :=
    (hc.comp continuous_snd).mul
      ((hv.comp (continuous_snd.inv.mul continuous_fst)).sub (hv.comp continuous_fst)).norm
  have hWsupp : HasCompactSupport (uncurry fun x y : G => h y * ‖v (y⁻¹ * x) - v x‖) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (((hCcomp.mul hv'.isCompact).union hv'.isCompact).prod hs.isCompact) ?_
    rintro ⟨x, y⟩ hp
    have hp' : h y * ‖v (y⁻¹ * x) - v x‖ ≠ 0 := hp
    have hy : y ∈ tsupport h :=
      subset_tsupport h (mem_support.mpr (left_ne_zero_of_mul hp'))
    have hvxne : v (y⁻¹ * x) - v x ≠ 0 := fun h0 =>
      right_ne_zero_of_mul hp' (by rw [h0, norm_zero])
    refine Set.mem_prod.mpr ⟨?_, hy⟩
    by_cases hx : v x = 0
    · left
      have hne : v (y⁻¹ * x) ≠ 0 := fun h0 => hvxne (by rw [h0, hx, sub_zero])
      have hmem : y⁻¹ * x ∈ tsupport v := subset_tsupport v (mem_support.mpr hne)
      have hprod := Set.mul_mem_mul (hsuppC hy) hmem
      rwa [mul_inv_cancel_left] at hprod
    · right
      exact subset_tsupport v (mem_support.mpr hx)
  -- pointwise bound by the partial integral of the kernel
  have hpt : ∀ x, ‖Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v x - v x‖
      ≤ ∫ y, h y * ‖v (y⁻¹ * x) - v x‖ ∂μ := by
    intro x
    have hint1 : Integrable (fun y => ((h y : ℝ) : ℂ) * v (y⁻¹ * x)) μ :=
      integrable_mconv_integrand μ hcℂ hsℂ hv x
    have hint2 : Integrable (fun y => ((h y : ℝ) : ℂ) * v x) μ :=
      (hcℂ.integrable_of_hasCompactSupport hsℂ).mul_const (v x)
    have hvx : v x = ∫ y, ((h y : ℝ) : ℂ) * v x ∂μ := by
      rw [integral_mul_const, hintℂ, one_mul]
    have hdiff : Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v x - v x
        = ∫ y, ((h y : ℝ) : ℂ) * (v (y⁻¹ * x) - v x) ∂μ := by
      rw [Convolution.MeasureTheory.mconv_apply]
      conv_lhs => rw [hvx]
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      ring
    rw [hdiff]
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Eventually.of_forall fun y => ?_)))
    show ‖((h y : ℝ) : ℂ) * (v (y⁻¹ * x) - v x)‖ = h y * ‖v (y⁻¹ * x) - v x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
  -- integrate, swap, and estimate
  have hinner : ∀ y, ∫ x, h y * ‖v (y⁻¹ * x) - v x‖ ∂μ = h y * φ y := by
    intro y
    rw [integral_const_mul, hφeq y]
  have hle : ∀ y, h y * φ y ≤ h y * ε := by
    intro y
    rcases eq_or_ne (h y) 0 with hy | hy
    · simp [hy]
    · have hymem : y ∈ tsupport h := subset_tsupport h (mem_support.mpr hy)
      exact mul_le_mul_of_nonneg_left (hsuppφ y hymem).le (h0 y)
  have hint_left : Integrable (fun y => h y * φ y) μ :=
    (CcFubini.MeasureTheory.integrable_integral_left hWc hWsupp).congr (Eventually.of_forall hinner)
  have hint_right : Integrable (fun y => h y * ε) μ :=
    (hc.integrable_of_hasCompactSupport hs).mul_const ε
  calc ∫ x, ‖Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v x - v x‖ ∂μ
      ≤ ∫ x, ∫ y, h y * ‖v (y⁻¹ * x) - v x‖ ∂μ ∂μ :=
        integral_mono hdiff_int (CcFubini.MeasureTheory.integrable_integral_right hWc hWsupp) hpt
    _ = ∫ y, ∫ x, h y * ‖v (y⁻¹ * x) - v x‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hWc hWsupp
    _ = ∫ y, h y * φ y ∂μ := integral_congr_ae (Eventually.of_forall hinner)
    _ ≤ ∫ y, h y * ε ∂μ := integral_mono hint_left hint_right hle
    _ = ε := by rw [integral_mul_const, hint, one_mul]

namespace L1G

/-- A continuous compactly supported real bump as an element of `L1G μ`. -/
def bump (h : G → ℝ) (hc : Continuous h) (hs : HasCompactSupport h) : L1G μ :=
  ofLp μ (toLpCc μ (fun y => ((h y : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hc)
    (hs.comp_left Complex.ofReal_zero))

/-- A normalized nonnegative bump has `L¹` norm `1`. -/
theorem norm_bump (h : G → ℝ) (hc : Continuous h) (hs : HasCompactSupport h)
    (h0 : ∀ x, 0 ≤ h x) (h1 : ∫ x, h x ∂μ = 1) : ‖bump μ h hc hs‖ = 1 := by
  show ‖toLpCc μ (fun y => ((h y : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hc)
    (hs.comp_left Complex.ofReal_zero)‖ = 1
  rw [norm_toLpCc]
  calc ∫ x, ‖((h x : ℝ) : ℂ)‖ ∂μ
      = ∫ x, h x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show ‖((h x : ℝ) : ℂ)‖ = h x
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    _ = 1 := h1

/-- **`L¹`-level approximate identity.** For every `F ∈ L¹(G)` and `ε > 0` there is a
neighborhood `U` of `1` such that `‖h * F - F‖ ≤ ε` for every normalized nonnegative bump
`h` supported in `U`. -/
theorem exists_bump_mul_close (F : L1G μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : G), ∀ (h : G → ℝ) (hc : Continuous h) (hs : HasCompactSupport h),
      (∀ x, 0 ≤ h x) → tsupport h ⊆ U → (∫ x, h x ∂μ) = 1 →
      ‖bump μ h hc hs * F - F‖ ≤ ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨v, hvc, hvs, -, hv⟩ := Density.MeasureTheory.exists_hasCompactSupport_integral_norm_sub_le
    (memLp_one_iff_integrable.mp (Lp.memLp (L1G.toLp μ F))) hε3
  obtain ⟨U, hU, hUprop⟩ := exists_bump_mconv_close μ v hvc hvs hε3
  refine ⟨U, hU, ?_⟩
  intro h hc hs h0 hsupp hint
  -- work at the `Lp` level throughout
  set Bp : Lp ℂ 1 μ := toLpCc μ (fun y => ((h y : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hc) (hs.comp_left Complex.ofReal_zero) with hBpdef
  set Fp : Lp ℂ 1 μ := L1G.toLp μ F with hFpdef
  set Vp : Lp ℂ 1 μ := toLpCc μ v hvc hvs with hVpdef
  have hBnorm : ‖Bp‖ = 1 := norm_bump μ h hc hs h0 hint
  have hFV : ‖Fp - Vp‖ ≤ ε / 3 := by
    rw [norm_sub_eq_integral μ]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hv
    filter_upwards [coeFn_toLpCc μ v hvc hvs] with x hx
    rw [hVpdef, hx]
  have hBV : ‖mulCLM μ Bp Vp - Vp‖ ≤ ε / 3 := by
    rw [hBpdef, hVpdef,
      mulCLM_toLpCc μ (fun y => ((h y : ℝ) : ℂ)) v _ _ hvc hvs, norm_sub_eq_integral μ]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hUprop h hc hs h0 hsupp hint)
    filter_upwards [coeFn_toLpCc μ (Convolution.MeasureTheory.mconv μ (fun y => ((h y : ℝ) : ℂ)) v) _ _,
      coeFn_toLpCc μ v hvc hvs] with x h1 h2
    rw [h1, h2]
  show ‖mulCLM μ Bp Fp - Fp‖ ≤ ε
  have hdecomp : mulCLM μ Bp Fp - Fp
      = mulCLM μ Bp (Fp - Vp) + (mulCLM μ Bp Vp - Vp) + (Vp - Fp) := by
    rw [map_sub]
    abel
  calc ‖mulCLM μ Bp Fp - Fp‖
      = ‖mulCLM μ Bp (Fp - Vp) + (mulCLM μ Bp Vp - Vp) + (Vp - Fp)‖ := by rw [hdecomp]
    _ ≤ ‖mulCLM μ Bp (Fp - Vp) + (mulCLM μ Bp Vp - Vp)‖ + ‖Vp - Fp‖ := norm_add_le _ _
    _ ≤ ‖mulCLM μ Bp (Fp - Vp)‖ + ‖mulCLM μ Bp Vp - Vp‖ + ‖Vp - Fp‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖Bp‖ * ‖Fp - Vp‖ + (ε / 3) + (ε / 3) :=
        add_le_add (add_le_add (norm_mulCLM_apply_le μ Bp (Fp - Vp)) hBV)
          (by rw [norm_sub_rev]; exact hFV)
    _ ≤ 1 * (ε / 3) + (ε / 3) + (ε / 3) := by
        rw [hBnorm, one_mul, one_mul]
        exact add_le_add (add_le_add hFV le_rfl) le_rfl
    _ = ε := by ring

end L1G

end

end OAI.Topology.Pontryagin.Algebra.MeasureTheory
