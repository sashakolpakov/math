import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyRightInverse

/-! # Parametric Vector Cauchy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParametricVectorCauchy.Dolbeault

noncomputable section

section

/-! The actual vector-valued Cauchy operator with smooth parameters,
including its derivative and genuine slice primitive. -/

open _root_.MeasureTheory _root_.ContinuousLinearMap Set
open scoped Convolution ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def parametricVectorCauchyTransform (g : P → ℂ → F) (q : P × ℂ) : F :=
  VectorCauchyTransform.Dolbeault.vectorCauchyTransform (g q.1) q.2

theorem parametricVectorCauchyTransform_smooth {g : P → ℂ → F} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ)) :
    ContDiffOn ℝ ∞ (parametricVectorCauchyTransform g) (S ×ˢ univ) :=
  contDiffOn_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℂ)
    hS hK hsupp DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable hg

theorem parametricVectorCauchyTransform_hasFDerivAt
    {g : P → ℂ → F} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ)) (q : P × ℂ) (hq : q.1 ∈ S) :
    HasFDerivAt (parametricVectorCauchyTransform g)
      ((DivisorClass.Chern.CauchyKernel.cauchyKernel ⋆[(ContinuousLinearMap.lsmul ℝ ℂ).precompR (P × ℂ), volume]
        fun w : ℂ => fderiv ℝ (Function.uncurry g) (q.1, w)) q.2) q :=
  hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℂ)
    hS hK hsupp DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable (hg.of_le (by simp)) q hq

theorem parametricVectorCauchyTransform_slice_primitive [CompleteSpace F]
    {g : P → ℂ → F} {S : Set P} {K : Set ℂ}
    (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ)) {p : P} (hp : p ∈ S) (z : ℂ) :
    VectorDbar.Dolbeault.vectorDbar (fun w => parametricVectorCauchyTransform g (p, w)) z = g p z := by
  have hc : HasCompactSupport (g p) :=
    exists_compact_iff_hasCompactSupport.mp ⟨K, hK, fun w hw => hsupp p w hp hw⟩
  have hs : ContDiff ℝ ∞ (g p) := by
    rw [← contDiffOn_univ]
    exact hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  exact VectorCauchyRightInverse.Dolbeault.vectorDbar_cauchyTransform hs hc z

end

/-! The genuine parameter derivative of the vector Cauchy integral,
including preservation of antiholomorphically constant parameter directions. -/

open _root_.MeasureTheory Set Filter
open scoped ContDiff Convolution _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem vectorParameterDerivativeSlice_hasCompactSupport {g : P → ℂ → F}
    {S : Set P} {K : Set ℂ} (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0) {p : P} (hp : p ∈ S) :
    HasCompactSupport (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨K, hK, fun w hw => ?_⟩
  have he : Function.uncurry g =ᶠ[𝓝 (p, w)] 0 := by
    filter_upwards [(hS.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp, hw⟩] with q hq
    exact hsupp q.1 q.2 hq.1 hq.2
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : F) (p, w)).fderiv

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem vectorParameterDerivativeSlice_continuous {g : P → ℂ → F} {S : Set P}
    (hS : IsOpen S) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    {p : P} (hp : p ∈ S) :
    Continuous (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) := by
  have hd := hg.fderiv_of_isOpen (hS.prod isOpen_univ) (m := ∞) (by simp)
  have hs : ContDiffOn ℝ ∞ (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) univ :=
    hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  exact (contDiffOn_univ.mp hs).continuous

theorem parametricVectorCauchyTransform_fderiv_apply [CompleteSpace F]
    {g : P → ℂ → F} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P × ℂ) :
    fderiv ℝ (parametricVectorCauchyTransform g) q v =
      ∫ w : ℂ, DivisorClass.Chern.CauchyKernel.cauchyKernel w • fderiv ℝ (Function.uncurry g) (q.1, q.2 - w) v := by
  rw [(parametricVectorCauchyTransform_hasFDerivAt hS hK hsupp hg q hq).fderiv]
  have hi := (vectorParameterDerivativeSlice_hasCompactSupport hS hK hsupp hq).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℂ).precompR (P × ℂ)) DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable
    (vectorParameterDerivativeSlice_continuous hS hg hq) q.2
  exact ContinuousLinearMap.integral_apply hi.integrable v

theorem parametricVectorCauchyTransform_preserves_holomorphic_direction
    [CompleteSpace F] [NormedSpace ℂ P]
    {g : P → ℂ → F} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ (Function.uncurry g) (q.1, w) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (Function.uncurry g) (q.1, w) (v, 0)) :
    fderiv ℝ (parametricVectorCauchyTransform g) q (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (parametricVectorCauchyTransform g) q (v, 0) := by
  rw [parametricVectorCauchyTransform_fderiv_apply hS hK hsupp hg q hq,
    parametricVectorCauchyTransform_fderiv_apply hS hK hsupp hg q hq, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  rw [hv, smul_comm]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParametricVectorCauchy.Dolbeault
