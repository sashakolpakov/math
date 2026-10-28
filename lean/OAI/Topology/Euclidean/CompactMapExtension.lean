import OAI.AlgebraicTopology.DeRham.Comparison.CompactFormExtension

/-! # Compact Map Extension -/

namespace OAI.Topology.Euclidean.CompactMapExtension.Globalization

noncomputable section

/-!
# Smooth vector-valued extensions near a compact set

A map that is smooth on an open neighborhood of a compact set has a global
smooth representative on a possibly smaller open neighborhood. The proof
uses the already checked scalar cutoff theorem from `CompactFormExtension`.
It applies to arbitrary real normed vector targets, not just form coefficients.

The extension is asserted to agree with the original map only near the
compact set. No global target-range preservation is claimed.
-/

open Filter Set _root_.TopologicalSpace Function
open scoped _root_.Topology ContDiff _root_.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A scalar cutoff whose closed support is contained in the domain of
smoothness removes every defect of an arbitrary extension outside that domain. -/
theorem contDiff_supported_smul {U : Opens E} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) :
    ContDiff ℝ ∞ (fun x => rho x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hrho.contDiffAt.smul (hf.contDiffAt (U.isOpen.mem_nhds hx))
  · have hnot : x ∉ tsupport rho := fun h => hx (hsupport h)
    have hzero : rho =ᶠ[𝓝 x] (0 : E → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    change rho y = 0 at hy
    rw [hy]
    exact zero_smul ℝ (f y)

variable [FiniteDimensional ℝ E]

/-- A smooth map on an open neighborhood of a compact set has a globally
smooth representative with the same germ along that compact set. -/
theorem exists_contDiff_extension_nhdsSet {U : Opens E} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨rho, hrho, hsupport, hone⟩ :=
    AlgebraicTopology.DeRham.Comparison.CompactFormExtension.exists_contDiff_cutoff_nhdsSet U hK hKU
  refine ⟨fun x => rho x • f x, contDiff_supported_smul hf rho hrho hsupport, ?_⟩
  filter_upwards [hone] with x hx
  change rho x = 1 at hx
  rw [hx, one_smul]

/-- The agreement can be exhibited on an actual open neighborhood contained
in the original smoothness domain. -/
theorem exists_contDiff_extension_on_open {U : Opens E} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (g : E → F) (V : Opens E), ContDiff ℝ ∞ g ∧ K ⊆ V ∧ V ≤ U ∧
      EqOn g f V := by
  obtain ⟨g, hg, hagree⟩ := exists_contDiff_extension_nhdsSet hf hK hKU
  have hmem : {x | g x = f x} ∩ (U : Set E) ∈ 𝓝ˢ K :=
    inter_mem hagree (U.isOpen.mem_nhdsSet.mpr hKU)
  obtain ⟨V, hV, hKV, hVsub⟩ := mem_nhdsSet_iff_exists.mp hmem
  exact ⟨g, ⟨V, hV⟩, hg, hKV, fun _ hx => (hVsub hx).2,
    fun _ hx => (hVsub hx).1⟩

omit [FiniteDimensional ℝ E] in
/-- The ordinary zero extension of a map defined on an open subtype is smooth
on that open set. No boundary smoothness is asserted for this raw extension. -/
theorem contDiffOn_subtype_extend_zero {U : Opens E} {f : U → F}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f) :
    ContDiffOn ℝ ∞ (Subtype.val.extend f (0 : E → F)) U := by
  intro x hx
  have hdiff : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞
      (Subtype.val.extend f (0 : E → F)) x := by
    rw [← contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))]
    have heq : (fun y : U => Subtype.val.extend f (0 : E → F) y) = f := by
      funext y
      exact Subtype.val_injective.extend_apply f (0 : E → F) y
    rw [heq]
    exact hf.contMDiffAt
  exact hdiff.contDiffAt.contDiffWithinAt

/-- The same extension theorem for maps whose actual domain is the open
subtype. It agrees with that map on an open neighborhood of the compact set. -/
theorem exists_contDiff_subtype_extension_on_open {U : Opens E} {f : U → F}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (g : E → F) (V : Opens E), ContDiff ℝ ∞ g ∧ K ⊆ V ∧ V ≤ U ∧
      ∀ x : U, (x : E) ∈ V → g x = f x := by
  obtain ⟨g, V, hg, hKV, hVU, hagree⟩ :=
    exists_contDiff_extension_on_open (contDiffOn_subtype_extend_zero hf) hK hKU
  refine ⟨g, V, hg, hKV, hVU, ?_⟩
  intro x hx
  exact (hagree hx).trans (Subtype.val_injective.extend_apply f (0 : E → F) x)

end

end OAI.Topology.Euclidean.CompactMapExtension.Globalization
