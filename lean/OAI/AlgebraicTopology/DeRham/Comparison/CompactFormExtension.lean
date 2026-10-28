import OAI.AlgebraicTopology.DeRham.Comparison.SmoothLocalExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Compact Form Extension -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CompactFormExtension

noncomputable section

/-!
# Smooth form extensions around a compact set

A smooth scalar cutoff equal to one near a compact subset and zero near the
complement of an open domain makes the actual supported extension smooth.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine smooth cutoff supported in an open set and equal to one on a
neighborhood of a compact subset. -/
theorem exists_contDiff_cutoff_nhdsSet (U : Opens E) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ rho : E → ℝ, ContDiff ℝ ∞ rho ∧ tsupport rho ⊆ U ∧
      rho =ᶠ[𝓝ˢ K] (1 : E → ℝ) := by
  have hdisjoint : Disjoint (U : Set E)ᶜ K := by
    exact disjoint_left.mpr (fun _ hx hk => hx (hKU hk))
  obtain ⟨rho, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
      U.isOpen.isClosed_compl hK.isClosed hdisjoint (n := ⊤)
  refine ⟨rho, rho.contMDiff.contDiff, ?_, hone⟩
  intro x hx
  by_contra hnot
  have hzeroAt : (rho : E → ℝ) =ᶠ[𝓝 x] (0 : E → ℝ) :=
    hzero.filter_mono (nhds_le_nhdsSet hnot)
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzeroAt) hx

/-- Every smooth form on an open domain has an actual global smooth
extension on a neighborhood of any compact subset of that domain. -/
theorem exists_smoothForm_extension_nhdsSet {U : Opens E} {n : ℕ}
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ globalForm : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n,
      (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) =ᶠ[𝓝ˢ K] form.extension := by
  obtain ⟨rho, hrho, hsupport, hone⟩ := exists_contDiff_cutoff_nhdsSet U hK hKU
  refine ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form, ?_⟩
  filter_upwards [hone] with x hx
  change rho x • form.extension x = form.extension x
  change rho x = 1 at hx
  rw [hx, one_smul]

end

end OAI.AlgebraicTopology.DeRham.Comparison.CompactFormExtension
