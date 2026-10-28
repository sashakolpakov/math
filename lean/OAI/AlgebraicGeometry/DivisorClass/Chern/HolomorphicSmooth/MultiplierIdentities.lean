import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition

/-! # Multiplier Identities -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.MultiplierIdentities

noncomputable section

/-! Exact absorption and finite partition identities for original smooth bundle multiplication. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (n : ℕ)

theorem holomorphicLineSmoothMul_absorb (f g : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hfg : ∀ x ∈ tsupport f, g x = 1) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a) =
      Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  simp only [Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply]
  exact (smul_comm (f x) (g x) (a.val i x)).trans
    (Holomorphic.SchwartzTestCutoff.complex_smul_fix_inner (g x) (f x) (a.val i x) (fun hfx => hfg x (subset_tsupport f hfx)))

theorem holomorphicLineSmoothMul_partition {ι : Type*} [Fintype ι]
    (f : ι → V.analyticSpace → ℂ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (f i))
    (hsum : ∀ x, ∑ i, f i x = 1) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ∑ i, Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n (f i) (hf i) a = a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  change Holomorphic.FormPartition.holomorphicLineSmoothFormCoordinate u n j x (∑ i, Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n (f i) (hf i) a) = _
  rw [map_sum]
  simp only [Holomorphic.FormPartition.holomorphicLineSmoothFormCoordinate, LinearMap.coe_mk, AddHom.coe_mk,
    Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply]
  rw [← Finset.sum_smul, hsum x, one_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.MultiplierIdentities
