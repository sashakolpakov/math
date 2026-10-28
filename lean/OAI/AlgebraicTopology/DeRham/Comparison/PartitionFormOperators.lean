import OAI.Analysis.DifferentialForms.Manifold.OpenD
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Partition Form Operators -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.PartitionFormOperators

noncomputable section

/-!
# Actual partition-of-unity operators on open-domain differential forms

Multiplying by a globally smooth function whose topological support lies in U
makes the zero extension of a form on U ∩ V smooth on V. Finite smooth
partitions of unity therefore give explicit complex-linear operators whose
sum on restricted global sections is the identity. No fine-sheaf or acyclicity
assertion is assumed.
-/

open Filter Set _root_.TopologicalSpace Function
open scoped _root_.Topology _root_.Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {U V W : Opens E}

/-- Evaluation of an actual open-domain form is complex-linear. -/
def openFormEvaluation (x : V) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n where
  toFun form := form x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Smoothness of the supported product is proved locally, including outside U. -/
theorem supportedFormExtension_smooth (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n) :
    ContDiffOn ℝ ∞ (fun x => rho x • form.extension x) (V : Set E) := by
  intro x hxV
  by_cases hxU : x ∈ U
  · exact (hrho.contDiffAt.smul
      (form.smooth.contDiffAt ((U ⊓ V).isOpen.mem_nhds ⟨hxU, hxV⟩))).contDiffWithinAt
  · have hnot : x ∉ tsupport rho := fun hx => hxU (hsupport hx)
    have hzero : rho =ᶠ[𝓝 x] (0 : E → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hprod : (fun y => rho y • form.extension y) =ᶠ[𝓝 x]
        (fun _ => (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)) := by
      filter_upwards [hzero] with y hy
      change rho y = 0 at hy
      rw [hy]
      exact zero_smul ℝ (form.extension y)
    exact (contDiffAt_const.congr_of_eventuallyEq hprod).contDiffWithinAt

/-- Multiply on U ∩ V by a supported smooth scalar and extend the result by zero to V. -/
def supportedFormExtension (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n where
  toFun form := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw V (fun x => rho x • form.extension x)
    (supportedFormExtension_smooth rho hrho hsupport form)
  map_add' form other := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change rho x • (form + other).extension x =
      rho x • form.extension x + rho x • other.extension x
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_add]
    exact smul_add _ _ _
  map_smul' c form := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change rho x • (c • form).extension x = c • (rho x • form.extension x)
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_smul]
    change rho x • (c • form.extension x) = c • (rho x • form.extension x)
    exact smul_comm (rho x) c (form.extension x)

@[simp]
theorem supportedFormExtension_apply (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n) (x : V) :
    supportedFormExtension rho hrho hsupport form x = rho x • form.extension x := rfl

/-- On the overlap the extension has the expected pointwise product value. -/
theorem supportedFormExtension_apply_of_mem (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n)
    (x : V) (hxU : (x : E) ∈ U) :
    supportedFormExtension rho hrho hsupport form x =
      rho x • form ⟨x, hxU, x.property⟩ := by
  rw [supportedFormExtension_apply]
  exact congrArg (fun z => rho x • z) (form.extension_apply ⟨x, hxU, x.property⟩)

/-- Off U the supported product is zero, not an arbitrary chosen value. -/
theorem supportedFormExtension_apply_of_notMem (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n)
    (x : V) (hxU : (x : E) ∉ U) :
    supportedFormExtension rho hrho hsupport form x = 0 := by
  have hzero : rho x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hxU (hsupport hx))
  rw [supportedFormExtension_apply, hzero]
  exact zero_smul ℝ (form.extension x)

/-- Supported extension commutes with restriction of the recipient open set. -/
theorem supportedFormExtension_restrict (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (hWV : W ≤ V)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) n) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hWV (supportedFormExtension rho hrho hsupport form) =
      supportedFormExtension rho hrho hsupport
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (inf_le_inf_left U hWV) form) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  by_cases hxU : (x : E) ∈ U
  · rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply,
      supportedFormExtension_apply_of_mem rho hrho hsupport form _ hxU,
      supportedFormExtension_apply_of_mem rho hrho hsupport _ _ hxU]
    rfl
  · rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply,
      supportedFormExtension_apply_of_notMem rho hrho hsupport form _ hxU,
      supportedFormExtension_apply_of_notMem rho hrho hsupport _ _ hxU]

variable {ι : Type*} {s : Set E} (cover : ι → Opens E)
  (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s)
  (hsub : rho.IsSubordinate (fun i => (cover i : Set E)))

/-- The explicit operator associated with one member of a smooth partition. -/
def partitionFormOperator (V : Opens E) (i : ι) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (cover i ⊓ V) n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n :=
  supportedFormExtension (rho i) (rho i).contMDiff.contDiff (hsub i)

@[simp]
theorem partitionFormOperator_apply (V : Opens E) (i : ι)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (cover i ⊓ V) n) (x : V) :
    partitionFormOperator cover rho hsub V i form x = rho i x • form.extension x := rfl

/-- On a restriction of a form from V, this is multiplication by the partition function. -/
theorem partitionFormOperator_restricted_apply (V : Opens E) (i : ι)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) (x : V) :
    partitionFormOperator cover rho hsub V i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form) x = rho i x • form x := by
  by_cases hxi : (x : E) ∈ cover i
  · exact supportedFormExtension_apply_of_mem (rho i) (rho i).contMDiff.contDiff
      (hsub i) _ x hxi
  · have hzero : rho i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx => hxi (hsub i hx))
    rw [partitionFormOperator_apply, hzero]
    calc
      _ = (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := zero_smul ℝ _
      _ = _ := (zero_smul ℝ _).symm

/-- The finite partition operators sum to the identity on genuine restricted forms. -/
theorem sum_partitionFormOperator [Fintype ι] (V : Opens E) (hVs : (V : Set E) ⊆ s)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) :
    (∑ i, partitionFormOperator cover rho hsub V i
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form)) = form := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change openFormEvaluation x (∑ i, partitionFormOperator cover rho hsub V i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form)) = form x
  rw [map_sum]
  change (∑ i, partitionFormOperator cover rho hsub V i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form) x) = form x
  simp only [partitionFormOperator_restricted_apply]
  rw [← Finset.sum_smul]
  have hsum : (∑ i, rho i x) = 1 :=
    rho.sum_finsupport' x (hVs x.property) (Finset.subset_univ _)
  rw [hsum, one_smul]

/-- The partitions used above exist for an actual open cover of a finite-dimensional space. -/
theorem exists_subordinateSmoothPartition [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ cover i) :
    ∃ partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E (Set.univ : Set E),
      partition.IsSubordinate (fun i => (cover i : Set E)) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ
    (fun i => (cover i : Set E)) (fun i => (cover i).isOpen)
  intro x _
  exact Set.mem_iUnion.mpr (hcover x)

end

end OAI.AlgebraicTopology.DeRham.Comparison.PartitionFormOperators
