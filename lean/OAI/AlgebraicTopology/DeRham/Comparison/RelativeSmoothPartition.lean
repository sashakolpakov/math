import OAI.Topology.Euclidean.CompactMapExtension
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition

/-! # Relative Smooth Partition -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothPartition

noncomputable section

/-!
# Smooth partitions intrinsic to an open domain

A partition of unity on the induced manifold of an open set gives actual
scalar functions smooth on that domain. Local finiteness and closed-support
containment are stated in the open subspace, where they hold even when
infinitely many supports accumulate at the ambient boundary.
-/

open Set Function _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W V : Opens E}

/-- The ordinary zero extension of an actual smooth partition weight on the
induced open manifold. Smoothness is required only inside that open domain. -/
def relativePartitionWeight (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ)
    (i : ι) : E → ℝ :=
  Subtype.val.extend (rho i) 0

@[simp]
theorem relativePartitionWeight_apply
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) (x : W) :
    relativePartitionWeight rho i x = rho i x :=
  Subtype.val_injective.extend_apply (rho i) 0 x

theorem relativePartitionWeight_restrict
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) :
    (fun x : W => relativePartitionWeight rho i x) = rho i :=
  funext (relativePartitionWeight_apply rho i)

/-- The extension really is zero outside its declared domain. No ambient
smoothness or ambient local finiteness is asserted at boundary points. -/
theorem relativePartitionWeight_eq_zero_of_notMem
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) {x : E} (hx : x ∉ W) :
    relativePartitionWeight rho i x = 0 := by
  apply extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

/-- Manifold smoothness of the intrinsic weight is exactly the needed
ordinary smoothness of its zero extension on the open domain. -/
theorem relativePartitionWeight_smooth
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) :
    ContDiffOn ℝ ∞ (relativePartitionWeight rho i) (W : Set E) :=
  Topology.Euclidean.CompactMapExtension.Globalization.contDiffOn_subtype_extend_zero (rho i).contMDiff

/-- Intrinsic local finiteness is preserved by the proved equality of the
extended weights with the original partition on its domain. -/
theorem relativePartitionWeight_locallyFinite
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) :
    LocallyFinite (fun i => support (fun x : W => relativePartitionWeight rho i x)) := by
  simpa only [relativePartitionWeight_restrict] using rho.locallyFinite

/-- The topological support here is closure in the open subspace `W`. -/
theorem relativePartitionWeight_tsupport
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) :
    tsupport (fun x : W => relativePartitionWeight rho i x) = tsupport (rho i) := by
  rw [relativePartitionWeight_restrict]

theorem relativePartitionWeight_tsupport_subset
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (cover : ι → Opens E)
    (hsub : rho.IsSubordinate (fun i => {x : W | (x : E) ∈ cover i})) (i : ι) :
    tsupport (fun x : W => relativePartitionWeight rho i x) ⊆
      {x : W | (x : E) ∈ cover i} := by
  rw [relativePartitionWeight_tsupport]
  exact hsub i

/-- The actual weights add up to one at every point of the open domain. -/
theorem relativePartitionWeight_finsum
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (x : W) :
    ∑ᶠ i, relativePartitionWeight rho i x = 1 := by
  simpa only [relativePartitionWeight_apply] using rho.sum_eq_one (mem_univ x)

theorem relativePartitionWeight_nonneg
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (i : ι) (x : E) :
    0 ≤ relativePartitionWeight rho i x := by
  by_cases hx : x ∈ W
  · change 0 ≤ relativePartitionWeight rho i (⟨x, hx⟩ : W)
    rw [relativePartitionWeight_apply]
    exact rho.nonneg i ⟨x, hx⟩
  · rw [relativePartitionWeight_eq_zero_of_notMem rho i hx]

/-- Intrinsic local finiteness restricts to any smaller open domain, exactly
as needed for locally finite sums on Čech intersections. -/
theorem relativePartitionWeight_locallyFinite_on
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ) (hVW : V ≤ W) :
    LocallyFinite (fun i => support (fun x : V => relativePartitionWeight rho i x)) := by
  have hinc : Continuous (fun x : V => (⟨(x : E), hVW x.property⟩ : W)) :=
    continuous_subtype_val.subtype_mk _
  have h := (relativePartitionWeight_locallyFinite rho).preimage_continuous hinc
  exact h

/-- Every open cover of an open finite-dimensional domain has a genuine
smooth partition of unity on that domain, subordinate in its own topology.
Cover members may already lie inside `W`; no ambient extension is required. -/
theorem exists_relative_smooth_partition [FiniteDimensional ℝ E]
    (W : Opens E) (cover : ι → Opens E)
    (hcover : ∀ x : W, ∃ i, (x : E) ∈ cover i) :
    ∃ rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ,
      rho.IsSubordinate (fun i => {x : W | (x : E) ∈ cover i}) := by
  let : LocallyCompactSpace W := W.isOpen.locallyCompactSpace
  apply SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
  · intro i
    exact (cover i).isOpen.preimage continuous_subtype_val
  · intro x _
    exact mem_iUnion.mpr (hcover x)

/-- An unpacked version for constructions that use actual ambient scalar
functions smooth on `W` and support/local-finiteness data intrinsic to `W`. -/
theorem exists_relative_smooth_partition_weights [FiniteDimensional ℝ E]
    (W : Opens E) (cover : ι → Opens E)
    (hcover : ∀ x : W, ∃ i, (x : E) ∈ cover i) :
    ∃ weights : ι → E → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (weights i) (W : Set E)) ∧
      LocallyFinite (fun i => support (fun x : W => weights i x)) ∧
      (∀ i, tsupport (fun x : W => weights i x) ⊆ {x : W | (x : E) ∈ cover i}) ∧
      (∀ x : W, ∑ᶠ i, weights i x = 1) ∧
      (∀ i x, 0 ≤ weights i x) := by
  obtain ⟨rho, hsub⟩ := exists_relative_smooth_partition W cover hcover
  exact ⟨relativePartitionWeight rho, relativePartitionWeight_smooth rho,
    relativePartitionWeight_locallyFinite rho,
    relativePartitionWeight_tsupport_subset rho cover hsub,
    relativePartitionWeight_finsum rho, relativePartitionWeight_nonneg rho⟩

end

end OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothPartition
