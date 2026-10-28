import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalPrimitive

/-! # Vector Cauchy Local Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalNaturality.Dolbeault

noncomputable section

/-! The actual localized vector primitive commutes with continuous
complex-linear coefficient maps, hence preserves their kernels. -/

open Set
open scoped ContDiff _root_.Topology

variable {P F G : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [CompleteSpace G]

theorem localizedVectorCauchyTransform_map (L : F →L[ℂ] G) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    (q : P × ℂ) (hq : q.1 ∈ S) :
    L (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g q) =
      VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ (fun p w => L (g p w)) q := by
  have hcut := VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_smooth hχ hS hU hsub hg
  have hf : ContDiff ℝ ∞ (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ g q.1) := by
    rw [← contDiffOn_univ]
    exact hcut.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hq, mem_univ _⟩)
  have hsupp : HasCompactSupport (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ g q.1) :=
    exists_compact_iff_hasCompactSupport.mp
      ⟨tsupport χ, hc.isCompact, fun w hw => VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_support χ g q.1 w hw⟩
  change L (VectorCauchyTransform.Dolbeault.vectorCauchyTransform (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ g q.1) q.2) = _
  rw [VectorCauchyTransform.Dolbeault.vectorCauchyTransform_map L hsupp hf.continuous]
  have he : L ∘ VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ g q.1 =
      VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ (fun p w => L (g p w)) q.1 := by
    funext w
    exact (L.restrictScalars ℝ).map_smul (χ w) (g q.1 w)
  rw [he]
  rfl

theorem localizedVectorCauchyTransform_kernel (L : F →L[ℂ] G) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    (q : P × ℂ) (hq : q.1 ∈ S) (hzero : ∀ w ∈ U, L (g q.1 w) = 0) :
    L (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g q) = 0 := by
  rw [localizedVectorCauchyTransform_map L hχ hc hS hU hsub hg q hq]
  have he : VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ (fun p w => L (g p w)) q.1 = 0 := by
    funext w
    by_cases hw : w ∈ tsupport χ
    · change χ w • L (g q.1 w) = 0
      rw [hzero w (hsub hw), smul_zero]
    · exact VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_support χ (fun p w => L (g p w)) q.1 w hw
  change VectorCauchyTransform.Dolbeault.vectorCauchyTransform (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ (fun p w => L (g p w)) q.1) q.2 = 0
  rw [he, VectorCauchyTransform.Dolbeault.vectorCauchyTransform_apply]
  simp only [Pi.zero_apply, smul_zero, MeasureTheory.integral_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalNaturality.Dolbeault
