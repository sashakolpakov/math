import OAI.Analysis.Normed.Function.Holder.C2HolderJointBase
import OAI.Analysis.PDE.Dirichlet.Closed.DerivativeTrace

/-! Joint one-sided differentiation on an arbitrary spatial set. The parameter
remainder is controlled in the bounded-function norm; no extension of the
spatial function across the boundary is assumed. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff BoundedContinuousFunction Convex
namespace OAI.Analysis.Normed.Function.Holder

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ Z] in
/-- The mean-value remainder with a moving parameter. This is the real
version of the local helper in Mathlib's partial-derivative proof. -/
theorem joint_parameter_mean_value {A : Type*} {u : Z} {v w : A → Z} {l : Filter A}
    (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    {f : A → Z → F} {f' : A → Z → Z →L[ℝ] F}
    (hd : ∀ᶠ p in l ×ˢ 𝓝 u, HasFDerivAt (f p.1) (f' p.1 p.2) p.2)
    {φ : Z →L[ℝ] F} (hc : Tendsto (Function.uncurry f') (l ×ˢ 𝓝 u) (𝓝 φ)) :
    (fun a => f a (v a) - f a (w a) - φ (v a-w a)) =o[l] (fun a => v a-w a) := by
  rw [isLittleO_iff]
  intro ε hε
  have hd' : ∀ᶠ a in l, ∀ z ∈ [w a -[ℝ] v a], HasFDerivAt (f a) (f' a z) z := by
    have hh : ∀ᶠ p in l ×ˢ 𝓝[univ] u, HasFDerivAt (f p.1) (f' p.1 p.2) p.2 := by
      simpa only [nhdsWithin_univ] using hd
    exact hh.segment_of_prod_nhdsWithin hw hv (by simp)
  have hc' : ∀ᶠ a in l, ∀ z ∈ [w a -[ℝ] v a], ‖f' a z-φ‖ < ε := by
    have hh := (Metric.tendsto_nhds.mp hc) ε hε
    simp only [dist_eq_norm] at hh
    have hh' : ∀ᶠ p in l ×ˢ 𝓝[univ] u, ‖f' p.1 p.2-φ‖ < ε := by
      simpa only [nhdsWithin_univ,Function.uncurry] using! hh
    exact hh'.segment_of_prod_nhdsWithin hw hv (by simp)
  filter_upwards [hd',hc'] with a ha hb
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (ha z hz).hasFDerivWithinAt) (fun z hz => (hb z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

theorem hasFDerivWithinAt_joint_bcf
    {U : Set Z} {S K : Set E} (hU : IsOpen U) (hSK : S ⊆ K)
    (a : Z → K →ᵇ F) (b : Z → K →ᵇ (E →L[ℝ] F))
    (ha : ContDiffOn ℝ 1 a U)
    (p : Z × E) (hp : p ∈ U ×ˢ S)
    (hsp : HasFDerivWithinAt (boundedZeroExtension (a p.1))
      (boundedZeroExtension (b p.1) p.2) S p.2) :
    HasFDerivWithinAt (fun q : Z × E => boundedZeroExtension (a q.1) q.2)
      (jointBCFDerivative a b p) (U ×ˢ S) p := by
  have ha' : ContinuousOn (fderiv ℝ a) U :=
    ha.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hpart : ContinuousOn
      (fun q : Z × E => (zeroEvalCLM K q.2).comp (fderiv ℝ a q.1)) (U ×ˢ S) := by
    apply continuousOn_clm_apply.mpr
    intro v
    simpa only [ContinuousLinearMap.comp_apply,zeroEvalCLM_apply] using
      continuousOn_joint_bcf hSK (fun z => fderiv ℝ a z v) (ha'.clm_apply continuousOn_const)
  let l : Filter (Z × E) := 𝓝 p.1 ×ˢ 𝓝[S] p.2
  have hl : 𝓝[U ×ˢ S] p = l := by
    rw [nhdsWithin_prod_eq, hU.nhdsWithin_eq hp.1]
  have hmap : Tendsto (fun t : (Z × E) × Z => (t.2,t.1.2))
      (l ×ˢ 𝓝 p.1) l :=
    tendsto_snd.prodMk (tendsto_snd.comp tendsto_fst)
  have hc : Tendsto
      (fun t : (Z × E) × Z => (zeroEvalCLM K t.1.2).comp (fderiv ℝ a t.2))
      (l ×ˢ 𝓝 p.1) (𝓝 ((zeroEvalCLM K p.2).comp (fderiv ℝ a p.1))) := by
    have ht := hpart p hp
    rw [ContinuousWithinAt,hl] at ht
    exact ht.comp hmap
  have hparam :
      (fun q : Z × E => boundedZeroExtension (a q.1) q.2 -
        boundedZeroExtension (a p.1) q.2 -
          ((zeroEvalCLM K p.2).comp (fderiv ℝ a p.1)) (q.1-p.1))
        =o[l] (fun q : Z × E => q.1-p.1) := by
    apply joint_parameter_mean_value
      (f := fun q z => boundedZeroExtension (a z) q.2)
      (f' := fun q z => (zeroEvalCLM K q.2).comp (fderiv ℝ a z))
      tendsto_fst tendsto_const_nhds
    · filter_upwards [tendsto_snd.eventually (hU.mem_nhds hp.1)] with t ht
      have hd := (((ha t.2 ht).contDiffAt (hU.mem_nhds ht)).differentiableAt
        (by norm_num)).hasFDerivAt
      have hv := (zeroEvalCLM K t.1.2).hasFDerivAt.comp t.2 hd
      simpa only [Function.comp_def,zeroEvalCLM_apply] using! hv
    · exact hc
  have hspace := hsp.isLittleO.comp_tendsto
    (tendsto_snd : Tendsto (Prod.snd : Z × E → E) l (𝓝[S] p.2))
  have hb₁ : (fun q : Z × E => q.1-p.1) =O[l] (fun q : Z × E => q-p) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun q => by
      simpa only [one_mul,Prod.fst_sub] using! norm_fst_le (q-p))
  have hb₂ : (fun q : Z × E => q.2-p.2) =O[l] (fun q : Z × E => q-p) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun q => by
      simpa only [one_mul,Prod.snd_sub] using! norm_snd_le (q-p))
  rw [hasFDerivWithinAt_iff_isLittleO,hl]
  have hs := (hparam.trans_isBigO hb₁).add (hspace.trans_isBigO hb₂)
  convert hs using 1
  funext q
  simp only [jointBCFDerivative,ContinuousLinearMap.coprod_apply,
    Prod.fst_sub,Prod.snd_sub,ContinuousLinearMap.comp_apply,zeroEvalCLM_apply,
    Function.comp_def]
  abel

theorem joint_bcf_contDiff_one_within [FiniteDimensional ℝ E]
    {U : Set Z} {S K : Set E} (hU : IsOpen U) (hSK : S ⊆ K)
    (a : Z → K →ᵇ F) (b : Z → K →ᵇ (E →L[ℝ] F))
    (ha : ContDiffOn ℝ 1 a U) (hb : ContinuousOn b U)
    (hsp : ∀ z ∈ U, ∀ x ∈ S, HasFDerivWithinAt (boundedZeroExtension (a z))
      (boundedZeroExtension (b z) x) S x) :
    ContDiffOn ℝ 1 (fun q : Z × E => boundedZeroExtension (a q.1) q.2) (U ×ˢ S) := by
  apply OAI.Analysis.PDE.Dirichlet.contDiffOn_succ_of_derivative_field 0 (G := jointBCFDerivative a b)
  · apply contDiffOn_zero.mpr
    apply continuousOn_clm_apply.mpr
    intro v
    have ha' := ha.continuousOn_fderiv_of_isOpen hU (by norm_num)
    have h₁ := continuousOn_joint_bcf hSK (fun z => fderiv ℝ a z v.1)
      (ha'.clm_apply continuousOn_const)
    have h₂ := (continuousOn_joint_bcf hSK b hb).clm_apply (g := fun _ : Z × E => v.2)
      continuousOn_const
    simpa only [jointBCFDerivative_apply,Pi.add_apply] using! h₁.add h₂
  · intro p hp
    exact hasFDerivWithinAt_joint_bcf hU hSK a b ha p hp (hsp p.1 hp.1 p.2 hp.2)

end OAI.Analysis.Normed.Function.Holder
