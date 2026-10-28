import OAI.Analysis.DifferentialForms.Manifold.LocallyFiniteSum
import OAI.Analysis.DifferentialForms.Manifold.OpenD

/-! # Open Locally Finite Sum -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Locally finite sums on open domains

Local finiteness is required only inside the open domain. No condition is
imposed at its boundary. Neighborhoods transport along the open inclusion, so
the sums are smooth and exterior differentiation commutes with them.
-/

open Function Set Filter _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {ι E F : Type*} [NormedAddCommGroup E] {U V : Opens E}

/-- A property holding near a point in an open subtype also holds in an ambient
neighborhood. -/
theorem OpenLocallyFiniteSum.eventually_of_eventually_onOpen {P : E → Prop} (x : U)
    (h : ∀ᶠ y : U in 𝓝 x, P y) : ∀ᶠ y in 𝓝 (x : E), P y := by
  rw [← U.isOpenEmbedding'.map_nhds_eq x]
  exact h

variable [NormedAddCommGroup F]

/-- Local finiteness on an open domain gives a finite support on an actual
ambient neighborhood of each point in that domain. -/
theorem OpenLocallyFiniteSum.exists_finset_support_onOpen {f : ι → E → F}
    (hlf : LocallyFinite (fun i => support (fun y : U => f i y))) (x : U) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 (x : E), support (fun i => f i y) ⊆ s := by
  obtain ⟨s, hs⟩ := hlf.exists_finset_support x
  exact ⟨s, OpenLocallyFiniteSum.eventually_of_eventually_onOpen x hs⟩

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem OpenLocallyFiniteSum.contDiffOn_finsum_of_locallyFinite_onOpen {r : WithTop ℕ∞} {f : ι → E → F}
    (hf : ∀ i, ContDiffOn ℝ r (f i) (U : Set E))
    (hlf : LocallyFinite (fun i => support (fun y : U => f i y))) :
    ContDiffOn ℝ r (fun y => ∑ᶠ i, f i y) (U : Set E) := by
  intro x hx
  obtain ⟨s, hs⟩ := OpenLocallyFiniteSum.exists_finset_support_onOpen hlf ⟨x, hx⟩
  exact (LocallyFiniteSum.contDiffAt_finsum_of_eventually_support_subset
    (fun i => (hf i).contDiffAt (U.isOpen.mem_nhds hx)) hs).contDiffWithinAt

variable {n : ℕ}

/-- Pointwise sum of forms whose supports are locally finite within the domain. -/
def OpenD.SmoothOpenForm.locallyFiniteSum (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) :
    OpenD.SmoothOpenForm U n :=
  OpenD.SmoothOpenForm.ofRaw U (fun x => ∑ᶠ i, (form i).extension x)
    (OpenLocallyFiniteSum.contDiffOn_finsum_of_locallyFinite_onOpen (fun i => (form i).smooth)
      (by simpa only [OpenD.SmoothOpenForm.extension_apply] using hlf))

@[simp] theorem OpenD.SmoothOpenForm.locallyFiniteSum_apply (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) (x : U) :
    OpenD.SmoothOpenForm.locallyFiniteSum form hlf x = ∑ᶠ i, form i x := by
  change (∑ᶠ i, (form i).extension x) = ∑ᶠ i, form i x
  exact finsum_congr fun i => (form i).extension_apply x

theorem OpenD.SmoothOpenForm.extension_locallyFiniteSum_eventuallyEq (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) (x : U) :
    (OpenD.SmoothOpenForm.locallyFiniteSum form hlf).extension =ᶠ[𝓝 (x : E)]
      (fun y => ∑ᶠ i, (form i).extension y) :=
  OpenD.SmoothOpenForm.extension_ofRaw_eventuallyEq _ _ x

/-- The open-domain derivative has support inside the relative topological
support of the original form. -/
theorem OpenD.SmoothOpenForm.support_d_subset_tsupport (form : OpenD.SmoothOpenForm U n) :
    support (OpenD.SmoothOpenForm.d form : U → Basic.FormValue E (n + 1)) ⊆ tsupport (form : U → Basic.FormValue E n) := by
  intro x hx
  by_contra hnot
  have hz : (form : U → Basic.FormValue E n) =ᶠ[𝓝 x] (0 : U → Basic.FormValue E n) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  have hraw : form.extension =ᶠ[𝓝 (x : E)] (fun _ => (0 : Basic.FormValue E n)) := by
    apply OpenLocallyFiniteSum.eventually_of_eventually_onOpen x
    filter_upwards [hz] with y hy
    simpa only [OpenD.SmoothOpenForm.extension_apply, Pi.zero_apply] using hy
  apply hx
  change extDeriv form.extension (x : E) = 0
  rw [hraw.extDeriv_eq]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (fderiv ℝ (fun _ : E => (0 : Basic.FormValue E n)) (x : E)) = 0
  rw [fderiv_const_apply, map_zero]

theorem OpenD.SmoothOpenForm.locallyFinite_d (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) :
    LocallyFinite (fun i => support (OpenD.SmoothOpenForm.d (form i) : U → Basic.FormValue E (n + 1))) :=
  hlf.closure.subset fun i => OpenD.SmoothOpenForm.support_d_subset_tsupport (form i)

/-- Exterior differentiation commutes with sums locally finite on the open
domain, including families accumulating at its boundary. -/
theorem OpenD.SmoothOpenForm.d_locallyFiniteSum (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) :
    OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.locallyFiniteSum form hlf) =
      OpenD.SmoothOpenForm.locallyFiniteSum (fun i => OpenD.SmoothOpenForm.d (form i)) (OpenD.SmoothOpenForm.locallyFinite_d form hlf) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [OpenD.SmoothOpenForm.locallyFiniteSum_apply, OpenD.SmoothOpenForm.d_apply,
    (OpenD.SmoothOpenForm.extension_locallyFiniteSum_eventuallyEq form hlf x).extDeriv_eq]
  have hlf' : LocallyFinite (fun i => support (fun y : U => (form i).extension y)) := by
    simpa only [OpenD.SmoothOpenForm.extension_apply] using hlf
  obtain ⟨s, hs⟩ := OpenLocallyFiniteSum.exists_finset_support_onOpen hlf' x
  exact LocallyFiniteSum.extDeriv_finsum_of_eventually_support_subset
    (fun i => ((form i).smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt
      (by simp)) hs

/-- Restriction preserves local finiteness of the family of supports. -/
theorem OpenD.SmoothOpenForm.locallyFinite_restrict (h : V ≤ U) (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) :
    LocallyFinite (fun i => support (OpenD.SmoothOpenForm.restrict h (form i) : V → Basic.FormValue E n)) := by
  exact hlf.preimage_continuous (continuous_inclusion h)

/-- Summation commutes with restriction to any smaller open domain. -/
theorem OpenD.SmoothOpenForm.restrict_locallyFiniteSum (h : V ≤ U) (form : ι → OpenD.SmoothOpenForm U n)
    (hlf : LocallyFinite (fun i => support (form i : U → Basic.FormValue E n))) :
    OpenD.SmoothOpenForm.restrict h (OpenD.SmoothOpenForm.locallyFiniteSum form hlf) =
      OpenD.SmoothOpenForm.locallyFiniteSum (fun i => OpenD.SmoothOpenForm.restrict h (form i)) (OpenD.SmoothOpenForm.locallyFinite_restrict h form hlf) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  simp only [OpenD.SmoothOpenForm.restrict_apply, OpenD.SmoothOpenForm.locallyFiniteSum_apply]

end

end OAI.Analysis.DifferentialForms.Manifold
