import OAI.Analysis.DifferentialForms.Manifold.SupportedExtension
import OAI.Analysis.DifferentialForms.Manifold.ManifoldGluing

/-! # Partition Patch -/

namespace OAI.Analysis.DifferentialForms.Manifold.PartitionPatch

noncomputable section

/-!
Explicit finite partition patching of actual smooth manifold forms. The
weighted extension of compatible sections is proved to recover every section.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- Restrict a genuine global form to every member of an open family. -/
def manifoldCoverRestriction (U : ι → Opens M) (p : ℕ) :
    Algebra.SmoothManifoldForm E M p →ₗ[ℂ] (∀ i, Open.SmoothOpenManifoldForm E (U i) p) :=
  LinearMap.pi (fun i => Algebra.SmoothManifoldForm.onOpen (U i))

/-- Sum the actual supported extensions weighted by the partition functions. -/
def manifoldPartitionPatch (U : ι → Opens M) (rho : ι → M → ℂ)
    (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
    (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M)) (p : ℕ) :
    (∀ i, Open.SmoothOpenManifoldForm E (U i) p) →ₗ[ℂ] Algebra.SmoothManifoldForm E M p where
  toFun forms := ∑ i, Open.SmoothOpenManifoldForm.supportedExtension
    (rho i) (hrho i).contMDiffOn (hsupp i) (forms i)
  map_add' forms others := by
    change (∑ i, Open.SmoothOpenManifoldForm.supportedExtension
      (rho i) (hrho i).contMDiffOn (hsupp i) (forms i + others i)) = _
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c forms := by
    change (∑ i, Open.SmoothOpenManifoldForm.supportedExtension
      (rho i) (hrho i).contMDiffOn (hsupp i) (c • forms i)) = _
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

theorem manifoldPartitionPatch_apply (U : ι → Opens M) (rho : ι → M → ℂ)
    (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
    (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M)) (p : ℕ)
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (U i) p) (x : M) :
    manifoldPartitionPatch U rho hrho hsupp p forms x =
      ∑ i, rho i x • (forms i).extension x := by
  change Algebra.SmoothManifoldForm.eval x (∑ i,
    Open.SmoothOpenManifoldForm.supportedExtension (rho i) (hrho i).contMDiffOn (hsupp i)
      (forms i)) = _
  rw [map_sum]
  rfl

/-- A finite subordinate partition gives an explicit left inverse to restriction. -/
theorem manifoldPartitionPatch_restriction (U : ι → Opens M) (rho : ι → M → ℂ)
    (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
    (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))
    (hsum : ∀ x, ∑ i, rho i x = 1) (p : ℕ) (form : Algebra.SmoothManifoldForm E M p) :
    manifoldPartitionPatch U rho hrho hsupp p (manifoldCoverRestriction U p form) = form := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  rw [manifoldPartitionPatch_apply]
  have hterm : ∀ i, rho i x • ((manifoldCoverRestriction U p form) i).extension x =
      rho i x • form x := by
    intro i
    by_cases hx : x ∈ U i
    · exact congrArg (fun value => rho i x • value)
        (Open.SmoothOpenManifoldForm.extension_apply
          (Algebra.SmoothManifoldForm.onOpen (U i) form) ⟨x, hx⟩)
    · have hzero : rho i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsupp i h))
      rw [hzero]
      exact (zero_smul ℂ (((manifoldCoverRestriction U p form) i).extension x)).trans
        (zero_smul ℂ (form x)).symm
  simp_rw [hterm]
  rw [← Finset.sum_smul, hsum x, one_smul]

/-- Compatible local forms are recovered on every open set by the weighted patch. -/
theorem manifoldPartitionPatch_restrict_compatible (U : ι → Opens M) (rho : ι → M → ℂ)
    (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
    (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))
    (hsum : ∀ x, ∑ i, rho i x = 1) (p : ℕ)
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (U i) p)
    (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) (j : ι) :
    Algebra.SmoothManifoldForm.onOpen (U j) (manifoldPartitionPatch U rho hrho hsupp p forms) =
      forms j := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Algebra.SmoothManifoldForm.onOpen_apply, manifoldPartitionPatch_apply]
  have hterm : ∀ i, rho i x • (forms i).extension x = rho i x • forms j x := by
    intro i
    by_cases hx : (x : M) ∈ U i
    · rw [Open.SmoothOpenManifoldForm.extension_apply (forms i) ⟨x, hx⟩]
      exact congrArg (fun value => rho i x • value) (hcompat i j x hx x.property)
    · have hzero : rho i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsupp i h))
      rw [hzero]
      exact (zero_smul ℂ ((forms i).extension x)).trans (zero_smul ℂ (forms j x)).symm
  simp_rw [hterm]
  rw [← Finset.sum_smul, hsum x, one_smul]

theorem manifoldPartitionPatch_comp_restriction (U : ι → Opens M) (rho : ι → M → ℂ)
    (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
    (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))
    (hsum : ∀ x, ∑ i, rho i x = 1) (p : ℕ) :
    (manifoldPartitionPatch U rho hrho hsupp p).comp (manifoldCoverRestriction U p) =
      LinearMap.id := by
  apply LinearMap.ext
  intro form
  exact manifoldPartitionPatch_restriction U rho hrho hsupp hsum p form

end

end OAI.Analysis.DifferentialForms.Manifold.PartitionPatch
