import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! # Alternatization -/

namespace OAI.Analysis.DifferentialForms.Manifold.Alternatization

variable (E F ι : Type*)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] [DecidableEq ι]

/-- Alternation of a continuous multilinear map, as a continuous real-linear map. -/
noncomputable def alternatizationCLM :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) F →L[ℝ] E [⋀^ι]→L[ℝ] F where
  toFun := ContinuousMultilinearMap.alternatization
  map_add' := map_add ContinuousMultilinearMap.alternatization
  map_smul' c f := by
    ext v
    simp only [ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousAlternatingMap.smul_apply, smul_apply,
      RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm _ _ _
  cont := by
    rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
    change Continuous (fun f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F =>
      ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ)
    apply continuous_finsetSum
    intro σ _
    exact (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F σ).continuous.const_smul _

@[simp] theorem alternatizationCLM_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) :
    alternatizationCLM E F ι f = ContinuousMultilinearMap.alternatization f := rfl

theorem alternatizationCLM_on_alternating (f : E [⋀^ι]→L[ℝ] F) :
    alternatizationCLM E F ι f.toContinuousMultilinearMap =
      ((Fintype.card ι).factorial : ℝ) • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simpa only [alternatizationCLM_apply,
    ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul, Nat.cast_smul_eq_nsmul] using
    AlternatingMap.coe_alternatization f.toAlternatingMap

/-- The normalized alternation is a retraction onto the alternating maps. -/
noncomputable def normalizedAlternatizationCLM :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) F →L[ℝ] E [⋀^ι]→L[ℝ] F :=
  (((Fintype.card ι).factorial : ℝ)⁻¹) • alternatizationCLM E F ι

@[simp] theorem normalizedAlternatizationCLM_on_alternating (f : E [⋀^ι]→L[ℝ] F) :
    normalizedAlternatizationCLM E F ι f.toContinuousMultilinearMap = f := by
  have hn : ((Fintype.card ι).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card ι)
  change (((Fintype.card ι).factorial : ℝ)⁻¹) •
    (alternatizationCLM E F ι f.toContinuousMultilinearMap) = f
  rw [alternatizationCLM_on_alternating, smul_smul, inv_mul_cancel₀ hn, one_smul]

variable {E F ι}
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {r : WithTop ℕ∞} {f : D → E [⋀^ι]→L[ℝ] F}

/-- Smoothness of an alternating-map-valued function is detected in multilinear maps. -/
theorem contDiff_alternating_iff :
    ContDiff ℝ r f ↔ ContDiff ℝ r (fun x => (f x).toContinuousMultilinearMap) := by
  constructor
  · intro hf
    exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp hf
  · intro hf
    simpa only [Function.comp_def, normalizedAlternatizationCLM_on_alternating] using
      (normalizedAlternatizationCLM E F ι).contDiff.comp hf

/-- The alternating-to-multilinear smoothness test is local at a point. -/
theorem contDiffAt_alternating_iff {x : D} :
    ContDiffAt ℝ r f x ↔
      ContDiffAt ℝ r (fun y => (f y).toContinuousMultilinearMap) x := by
  constructor
  · intro hf
    exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.contDiffAt.comp x hf
  · intro hf
    simpa only [Function.comp_def, normalizedAlternatizationCLM_on_alternating] using
      (normalizedAlternatizationCLM E F ι).contDiff.contDiffAt.comp x hf

/-- Smoothness on a subset is detected in the ambient multilinear-map space. -/
theorem contDiffOn_alternating_iff {s : Set D} :
    ContDiffOn ℝ r f s ↔
      ContDiffOn ℝ r (fun y => (f y).toContinuousMultilinearMap) s := by
  constructor
  · intro hf
    exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp_contDiffOn hf
  · intro hf
    simpa only [Function.comp_def, normalizedAlternatizationCLM_on_alternating] using
      (normalizedAlternatizationCLM E F ι).contDiff.comp_contDiffOn hf

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pullback of an alternating map varies smoothly with both the map and the
linear map used on its inputs. -/
theorem contDiff_alternating_compContinuousLinearMap
    {form : D → F [⋀^ι]→L[ℝ] G} {linear : D → E →L[ℝ] F}
    (hform : ContDiff ℝ r form) (hlinear : ContDiff ℝ r linear) :
    ContDiff ℝ r (fun x => (form x).compContinuousLinearMap (linear x)) := by
  apply contDiff_alternating_iff.mpr
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : ι => E) (fun _ : ι => F) G).contDiff.comp
      (contDiff_pi.mpr fun _ => hlinear)).clm_apply
    (contDiff_alternating_iff.mp hform)

/-- Local smoothness of pullback on alternating maps. -/
theorem contDiffAt_alternating_compContinuousLinearMap
    {form : D → F [⋀^ι]→L[ℝ] G} {linear : D → E →L[ℝ] F} {x : D}
    (hform : ContDiffAt ℝ r form x) (hlinear : ContDiffAt ℝ r linear x) :
    ContDiffAt ℝ r (fun y => (form y).compContinuousLinearMap (linear y)) x := by
  apply contDiffAt_alternating_iff.mpr
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : ι => E) (fun _ : ι => F) G).contDiff.contDiffAt.comp x
      (contDiffAt_pi.mpr fun _ => hlinear)).clm_apply
    (contDiffAt_alternating_iff.mp hform)

/-- Smoothness on a subset of pullback on alternating maps. -/
theorem contDiffOn_alternating_compContinuousLinearMap
    {form : D → F [⋀^ι]→L[ℝ] G} {linear : D → E →L[ℝ] F} {s : Set D}
    (hform : ContDiffOn ℝ r form s) (hlinear : ContDiffOn ℝ r linear s) :
    ContDiffOn ℝ r (fun y => (form y).compContinuousLinearMap (linear y)) s := by
  apply contDiffOn_alternating_iff.mpr
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : ι => E) (fun _ : ι => F) G).contDiff.comp_contDiffOn
      (contDiffOn_pi.mpr fun _ => hlinear)).clm_apply
    (contDiffOn_alternating_iff.mp hform)

end OAI.Analysis.DifferentialForms.Manifold.Alternatization
