import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.UrysohnsLemma

/-! # Translation -/

namespace OAI.Topology.Pontryagin.Translation.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# Normalized bumps and translation operators

Infrastructure for the approximate-identity arguments in the proof of Pontryagin duality for
locally compact abelian groups, stated multiplicatively throughout.

## Main definitions and results

* `exists_normalized_bump`: for every neighborhood `U` of `1` there is a nonnegative continuous
 compactly supported real function `h` with `tsupport h ⊆ U` and `∫ h ∂μ = 1`;
* `mtranslate a f = fun x ↦ f (a⁻¹ * x)`: left translation of functions on a multiplicative
 group, together with its interaction with continuity, supports, integrals and `MemLp`;
* `translateLp μ p a: Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p μ`: left translation as a linear isometry of
 `Lp`, with the identity/composition laws `translateLp_one`, `translateLp_mul`, the a.e.
 description `coeFn_translateLp`, and continuity in the translation parameter,
 `continuous_translateLp`.
-/

open Function Set _root_.Topology
open scoped ENNReal Pointwise

/-! ### Translation of functions -/

section MtranslateCore

variable {G : Type*} [CommGroup G] {E : Type*}

/-- Left translation of a function on a multiplicative group:
`mtranslate a f x = f (a⁻¹ * x)`. -/
def mtranslate (a : G) (f : G → E) : G → E := fun x ↦ f (a⁻¹ * x)

@[simp]
theorem mtranslate_apply (a : G) (f : G → E) (x : G) : mtranslate a f x = f (a⁻¹ * x) := rfl

@[simp]
theorem mtranslate_one (f : G → E) : mtranslate (1 : G) f = f := by
  funext x
  simp [mtranslate]

theorem mtranslate_mtranslate (a b : G) (f : G → E) :
    mtranslate a (mtranslate b f) = mtranslate (a * b) f := by
  funext x
  simp [mtranslate, mul_assoc]

theorem support_mtranslate [Zero E] (a : G) (f : G → E) :
    support (mtranslate a f) = a • support f := by
  ext x
  simp only [mem_support, mtranslate_apply, mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

end MtranslateCore

section MtranslateTopology

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] {E : Type*}

theorem _root_.OAI.Topology.Pontryagin.Translation.Continuous.mtranslate [TopologicalSpace E] {f : G → E} (hf : Continuous f) (a : G) :
    Continuous (mtranslate a f) :=
  hf.comp (continuous_const_mul a⁻¹)

theorem tsupport_mtranslate [Zero E] (a : G) (f : G → E) :
    tsupport (mtranslate a f) = a • tsupport f :=
  (congrArg closure (support_mtranslate a f)).trans (closure_smul a (support f))

theorem _root_.OAI.Topology.Pontryagin.Translation.HasCompactSupport.mtranslate [Zero E] {f : G → E} (hf : HasCompactSupport f)
    (a : G) :
    HasCompactSupport (mtranslate a f) := by
  have h := IsCompact.smul a hf
  rwa [← tsupport_mtranslate] at h

end MtranslateTopology

/-! ### Normalized bumps subordinate to a neighborhood of the identity -/

section Bump

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- For every neighborhood `U` of `1` there is a nonnegative continuous compactly supported
function with support inside `U`, positive integral, normalized to `∫ h ∂μ = 1`. -/
theorem exists_normalized_bump (U : Set G) (hU : U ∈ nhds (1 : G)) :
    ∃ h : G → ℝ, Continuous h ∧ HasCompactSupport h ∧ (∀ x, 0 ≤ h x) ∧
      tsupport h ⊆ U ∧ ∫ x, h x ∂μ = 1 := by
  -- Shrink `U` to an open set `V ∋ 1` and interpose a compact set `L` with `1 ∈ interior L`.
  obtain ⟨V, hVU, hVopen, hV1⟩ := mem_nhds_iff.mp hU
  obtain ⟨L, hLcomp, hL1, hLV⟩ :=
    exists_compact_between isCompact_singleton hVopen (singleton_subset_iff.mpr hV1)
  -- Urysohn: a continuous `u` with compact support, `u 1 = 1`, `u = 0` outside `interior L`.
  obtain ⟨u, hu1, hu0, hucomp, hu01⟩ :=
    exists_continuous_one_zero_of_isCompact isCompact_singleton
      isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hL1)
  have husupp : tsupport u ⊆ U := by
    have h1 : support u ⊆ interior L := fun x hx ↦ by
      by_contra hxL
      exact hx (hu0 hxL)
    exact ((closure_mono h1).trans
      (closure_minimal interior_subset hLcomp.isClosed)).trans (hLV.trans hVU)
  have hu_int : Integrable (⇑u) μ := u.continuous.integrable_of_hasCompactSupport hucomp
  have hu_one : (u : G → ℝ) 1 = 1 := hu1 rfl
  have hpos : 0 < ∫ x, u x ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero (x := 1) u.continuous hu_int
      (fun x ↦ (hu01 x).1) (by rw [hu_one]; exact one_ne_zero)
  refine ⟨fun x ↦ (∫ y, u y ∂μ)⁻¹ * u x, continuous_const.mul u.continuous, hucomp.mul_left,
    fun x ↦ mul_nonneg (inv_nonneg.mpr hpos.le) (hu01 x).1, ?_, ?_⟩
  · refine (closure_mono fun x hx ↦ ?_).trans husupp
    simp only [mem_support] at hx ⊢
    exact fun h0 ↦ hx (by rw [h0, mul_zero])
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

end Bump

/-! ### Translation, measures and integrals -/

section MtranslateIntegral

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E]

theorem eLpNorm_mtranslate {p : ℝ≥0∞} {f : G → E} (hf : AEStronglyMeasurable f μ) (a : G) :
    eLpNorm (mtranslate a f) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_mul_left μ a⁻¹)

theorem MemLp.mtranslate {p : ℝ≥0∞} {f : G → E} (hf : MemLp f p μ) (a : G) :
    MemLp (mtranslate a f) p μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ a⁻¹)

theorem integral_mtranslate [NormedSpace ℝ E] (a : G) (f : G → E) :
    ∫ x, mtranslate a f x ∂μ = ∫ x, f x ∂μ :=
  integral_mul_left_eq_self f a⁻¹

end MtranslateIntegral

/-! ### Translation as a linear isometry of `Lp` -/

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Left translation `f ↦ f (a⁻¹ * ·)` as a linear isometry of `Lp ℂ p μ`. -/
def translateLp (a : G) : Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p μ where
  toLinearMap :=
    { toFun := Lp.compMeasurePreserving (fun x ↦ a⁻¹ * x) (measurePreserving_mul_left μ a⁻¹)
      map_add' := fun f g ↦ map_add _ f g
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        have h3 := (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_smul c f)
        filter_upwards [Lp.coeFn_compMeasurePreserving (c • f)
            (measurePreserving_mul_left μ a⁻¹),
          Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ a⁻¹), h3,
          Lp.coeFn_smul c (Lp.compMeasurePreserving (fun x ↦ a⁻¹ * x)
            (measurePreserving_mul_left μ a⁻¹) f)] with x hx1 hx2 hx3 hx4
        simp only [RingHom.id_apply]
        rw [hx1, hx3, hx4]
        simp only [Function.comp_apply, Pi.smul_apply, hx2] }
  norm_map' f := Lp.norm_compMeasurePreserving f (measurePreserving_mul_left μ a⁻¹)

theorem translateLp_apply (a : G) (f : Lp ℂ p μ) :
    translateLp μ p a f =
      Lp.compMeasurePreserving (fun x ↦ a⁻¹ * x) (measurePreserving_mul_left μ a⁻¹) f :=
  rfl

/-- Almost everywhere, `translateLp μ p a f` is the translate `mtranslate a ⇑f`. -/
theorem coeFn_translateLp (a : G) (f : Lp ℂ p μ) :
    ⇑(translateLp μ p a f) =ᵐ[μ] mtranslate a ⇑f :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ a⁻¹)

@[simp]
theorem translateLp_one (f : Lp ℂ p μ) : translateLp μ p 1 f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateLp μ p 1 f] with x hx
  simpa using hx

theorem translateLp_mul (a b : G) (f : Lp ℂ p μ) :
    translateLp μ p (a * b) f = translateLp μ p a (translateLp μ p b f) := by
  refine Lp.ext ?_
  have h3 : (⇑(translateLp μ p b f) ∘ fun x : G ↦ a⁻¹ * x)
      =ᵐ[μ] (mtranslate b ⇑f ∘ fun x : G ↦ a⁻¹ * x) :=
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateLp μ p b f)
  filter_upwards [coeFn_translateLp μ p (a * b) f,
    coeFn_translateLp μ p a (translateLp μ p b f), h3] with x hx1 hx2 hx3
  have hx3' : (translateLp μ p b f : G → ℂ) (a⁻¹ * x) = mtranslate b (⇑f) (a⁻¹ * x) := hx3
  rw [hx1, hx2]
  simp only [mtranslate_apply]
  rw [hx3']
  simp [mul_assoc]

@[simp]
theorem norm_translateLp (a : G) (f : Lp ℂ p μ) : ‖translateLp μ p a f‖ = ‖f‖ :=
  (translateLp μ p a).norm_map f

variable [LocallyCompactSpace G] [μ.Regular]

/-- For `p ≠ ∞`, translation on `Lp ℂ p μ` is continuous in the translation parameter. -/
theorem continuous_translateLp (hp : p ≠ ∞) (f : Lp ℂ p μ) :
    Continuous fun a : G ↦ translateLp μ p a f := by
  have hgc : Continuous fun a : G ↦ (⟨fun x : G ↦ a⁻¹ * x, by fun_prop⟩ : C(G, G)) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact continuous_fst.inv.mul continuous_snd
  simp only [translateLp_apply]
  exact Continuous.compMeasurePreservingLp (continuous_const : Continuous fun _ : G ↦ f) hgc
    (fun a ↦ measurePreserving_mul_left μ a⁻¹) hp

end

end OAI.Topology.Pontryagin.Translation.MeasureTheory
