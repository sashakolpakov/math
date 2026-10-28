import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Finite Partition -/

namespace OAI.Analysis.DifferentialForms.Manifold.FinitePartition

noncomputable section

section

/-!
# Actual smooth complex partitions of unity

The coefficient functions used for patching local complex-valued forms are
complexifications of mathlib's genuine smooth real partitions of unity.
Their topological supports, smoothness, and sum identity are proved here.
-/

open scoped _root_.Manifold ContDiff
open Set Function

variable {ι E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def complexPartitionFunction (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M)
    (i : ι) (x : M) : ℂ := partition i x

theorem complexPartitionFunction_smooth
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) (i : ι) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (complexPartitionFunction partition i) := by
  exact Complex.ofRealCLM.contDiff.contMDiff.comp (partition i).contMDiff

theorem complexPartitionFunction_tsupport
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) (i : ι) :
    tsupport (complexPartitionFunction partition i) = tsupport (partition i) := by
  apply congrArg closure
  ext x
  simp [complexPartitionFunction, Function.mem_support]

theorem complexPartitionFunction_sum [Fintype ι]
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) (x : M) :
    ∑ i, complexPartitionFunction partition i x = 1 := by
  have hreal : ∑ i, partition i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using partition.sum_eq_one (mem_univ x)
  change ∑ i, (partition i x : ℂ) = 1
  exact_mod_cast hreal

/-- Any finite open cover admits an actual smooth complex partition of unity
with each closed support contained in the corresponding member. -/
theorem exists_finite_complex_partition [Fintype ι] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ functions : ι → M → ℂ,
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (functions i)) ∧
      (∀ i, tsupport (functions i) ⊆ U i) ∧
      (∀ x, ∑ i, functions i x = 1) := by
  obtain ⟨partition, hpartition⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_univ U hU (by
      intro x _
      exact mem_iUnion.mpr (hcover x))
  refine ⟨complexPartitionFunction partition, ?_, ?_, ?_⟩
  · exact complexPartitionFunction_smooth partition
  · intro i
    rw [complexPartitionFunction_tsupport]
    exact hpartition i
  · exact complexPartitionFunction_sum partition

end

/-!
# Locally finite complex partitions of unity

These are actual complexifications of smooth real partitions of unity. The
local finiteness and sum identities are inherited by proved equalities, so the
result applies to countable open covers without a finite-index assumption.
-/

open scoped _root_.Manifold ContDiff
open Set Function

variable {ι E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem complexPartitionFunction_support
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) (i : ι) :
    support (complexPartitionFunction partition i) = support (partition i) := by
  ext x
  simp [complexPartitionFunction, Function.mem_support]

theorem complexPartitionFunction_locallyFinite
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) :
    LocallyFinite (fun i => support (complexPartitionFunction partition i)) := by
  simpa only [complexPartitionFunction_support] using partition.locallyFinite

theorem complexPartitionFunction_finsum
    (partition : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M) (x : M) :
    ∑ᶠ i, complexPartitionFunction partition i x = 1 := by
  change (∑ᶠ i, ((partition i x : ℝ) : ℂ)) = 1
  calc
    _ = Complex.ofRealHom (∑ᶠ i, partition i x) :=
      (Complex.ofRealHom.toAddMonoidHom.map_finsum_of_injective
        Complex.ofReal_injective (fun i => partition i x)).symm
    _ = 1 := by rw [partition.sum_eq_one (mem_univ x)]; rfl

/-- Every open cover of a finite-dimensional Hausdorff sigma-compact smooth
manifold admits actual complex smooth subordinate coefficients, with locally
finite supports and pointwise sum one. -/
theorem exists_locallyFinite_complex_partition [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ functions : ι → M → ℂ,
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (functions i)) ∧
      LocallyFinite (fun i => support (functions i)) ∧
      (∀ i, tsupport (functions i) ⊆ U i) ∧
      (∀ x, ∑ᶠ i, functions i x = 1) := by
  obtain ⟨partition, hpartition⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_univ U hU (by
      intro x _
      exact mem_iUnion.mpr (hcover x))
  refine ⟨complexPartitionFunction partition, complexPartitionFunction_smooth partition,
    complexPartitionFunction_locallyFinite partition, ?_,
    complexPartitionFunction_finsum partition⟩
  intro i
  rw [complexPartitionFunction_tsupport]
  exact hpartition i

end

end OAI.Analysis.DifferentialForms.Manifold.FinitePartition
