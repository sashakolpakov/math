import OAI.Topology.Euclidean.BoxBasis
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Encodable.Basic
import Mathlib.Topology.Compactness.Compact

/-! # Box Exhaustion -/

namespace OAI.Topology.Euclidean.BoxExhaustion.Globalization

noncomputable section

/-!
# Exhaustion of an open set by finite unions of rational boxes

For a countably indexed family, a stage uses only the finitely many indices
decoded below its stage number whose carriers lie in the given set. Applied to
rational boxes this gives an increasing open exhaustion of any Euclidean open
set. Every compact subset lies in all sufficiently late stages.

No choice of a point or box inside the open set is required. In particular, the
construction applies unchanged to the empty open set and to zero dimensions.
-/

open Set

namespace CountableFamily

variable {ι X : Type*} [Countable ι]

/-- A partial enumeration, which also works for an empty index type. -/
def enumeration (ι : Type*) [Countable ι] (n : ℕ) : Option ι :=
  @Encodable.decode ι (Encodable.ofCountable ι) n

theorem exists_enumeration_eq (i : ι) :
    ∃ n, enumeration ι n = some i := by
  let : Encodable ι := Encodable.ofCountable ι
  exact ⟨Encodable.encode i, Encodable.encodek i⟩

/-- The first finitely many decoded family members that lie inside `U`. -/
def indices (b : ι → Set X) (U : Set X) (n : ℕ) : Finset ι := by
  classical
  exact ((Finset.range n).biUnion fun k => (enumeration ι k).toFinset).filter
    fun i => b i ⊆ U

theorem mem_indices (b : ι → Set X) (U : Set X) (n : ℕ) (i : ι) :
    i ∈ indices b U n ↔
      (∃ k, k < n ∧ enumeration ι k = some i) ∧ b i ⊆ U := by
  classical
  simp only [indices, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Option.mem_toFinset, Option.mem_def]

theorem indices_mono (b : ι → Set X) (U : Set X) : Monotone (indices b U) := by
  intro n m hnm i hi
  obtain ⟨⟨k, hkn, hki⟩, hiU⟩ := (mem_indices b U n i).mp hi
  exact (mem_indices b U m i).mpr ⟨⟨k, hkn.trans_le hnm, hki⟩, hiU⟩

/-- A literal finite union of family members contained in `U`. -/
def stage (b : ι → Set X) (U : Set X) (n : ℕ) : Set X :=
  ⋃ i ∈ indices b U n, b i

theorem mem_stage (b : ι → Set X) (U : Set X) (n : ℕ) (x : X) :
    x ∈ stage b U n ↔ ∃ i ∈ indices b U n, x ∈ b i := by
  simp only [stage, mem_iUnion, exists_prop]

@[simp]
theorem stage_zero (b : ι → Set X) (U : Set X) : stage b U 0 = ∅ := by
  classical
  simp [stage, indices]

theorem stage_subset (b : ι → Set X) (U : Set X) (n : ℕ) : stage b U n ⊆ U := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := (mem_stage b U n x).mp hx
  exact ((mem_indices b U n i).mp hi).2 hxi

theorem stage_mono (b : ι → Set X) (U : Set X) : Monotone (stage b U) := by
  intro n m hnm x hx
  obtain ⟨i, hi, hxi⟩ := (mem_stage b U n x).mp hx
  exact (mem_stage b U m x).mpr ⟨i, indices_mono b U hnm hi, hxi⟩

/-- Every family member contained in `U` occurs in a finite stage. -/
theorem subset_stage (b : ι → Set X) (U : Set X) (i : ι) (hi : b i ⊆ U) :
    ∃ n, b i ⊆ stage b U n := by
  obtain ⟨k, hki⟩ := exists_enumeration_eq i
  refine ⟨k + 1, ?_⟩
  intro x hx
  exact (mem_stage b U (k + 1) x).mpr
    ⟨i, (mem_indices b U (k + 1) i).mpr ⟨⟨k, Nat.lt_succ_self k, hki⟩, hi⟩, hx⟩

theorem iUnion_stage (b : ι → Set X) (U : Set X)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ b i ∧ b i ⊆ U) :
    (⋃ n, stage b U n) = U := by
  apply Subset.antisymm
  · exact iUnion_subset (stage_subset b U)
  · intro x hx
    obtain ⟨i, hxi, hiU⟩ := hcover x hx
    obtain ⟨n, hin⟩ := subset_stage b U i hiU
    exact mem_iUnion.mpr ⟨n, hin hxi⟩

variable [TopologicalSpace X]

theorem isOpen_stage (b : ι → Set X) (U : Set X)
    (hb : ∀ i, IsOpen (b i)) (n : ℕ) : IsOpen (stage b U n) :=
  isOpen_biUnion fun i _ => hb i

/-- Compactness gives one stage containing the entire compact subset. -/
theorem compact_subset_stage (b : ι → Set X) (U : Set X)
    (hb : ∀ i, IsOpen (b i))
    (hcover : ∀ x ∈ U, ∃ i, x ∈ b i ∧ b i ⊆ U)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ n, K ⊆ stage b U n := by
  apply hK.elim_directed_cover (stage b U) (isOpen_stage b U hb)
  · simpa only [iUnion_stage b U hcover] using hKU
  · intro n m
    exact ⟨max n m, stage_mono b U (le_max_left n m),
      stage_mono b U (le_max_right n m)⟩

theorem compact_eventually_subset_stage (b : ι → Set X) (U : Set X)
    (hb : ∀ i, IsOpen (b i))
    (hcover : ∀ x ∈ U, ∃ i, x ∈ b i ∧ b i ⊆ U)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N, ∀ n, N ≤ n → K ⊆ stage b U n := by
  obtain ⟨N, hN⟩ := compact_subset_stage b U hb hcover hK hKU
  exact ⟨N, fun n hn => hN.trans (stage_mono b U hn)⟩

end CountableFamily

variable {ι : Type*} [Finite ι]

/-- The rational boxes selected for a stage of the exhaustion. -/
def boxExhaustionIndices (U : Set (ι → ℝ)) (n : ℕ) : Finset (BoxBasis.Globalization.RationalBox ι) :=
  CountableFamily.indices BoxBasis.Globalization.RationalBox.carrier U n

/-- Finite union of rational boxes inside `U` with indices below `n`. -/
def boxExhaustion (U : Set (ι → ℝ)) (n : ℕ) : Set (ι → ℝ) :=
  CountableFamily.stage BoxBasis.Globalization.RationalBox.carrier U n

theorem boxExhaustion_eq_biUnion (U : Set (ι → ℝ)) (n : ℕ) :
    boxExhaustion U n = ⋃ B ∈ boxExhaustionIndices U n, B.carrier := rfl

theorem boxExhaustionIndices_carrier_subset (U : Set (ι → ℝ)) (n : ℕ)
    {B : BoxBasis.Globalization.RationalBox ι} (hB : B ∈ boxExhaustionIndices U n) : B.carrier ⊆ U :=
  ((CountableFamily.mem_indices BoxBasis.Globalization.RationalBox.carrier U n B).mp hB).2

@[simp]
theorem boxExhaustion_zero (U : Set (ι → ℝ)) : boxExhaustion U 0 = ∅ :=
  CountableFamily.stage_zero BoxBasis.Globalization.RationalBox.carrier U

theorem boxExhaustion_subset (U : Set (ι → ℝ)) (n : ℕ) : boxExhaustion U n ⊆ U :=
  CountableFamily.stage_subset BoxBasis.Globalization.RationalBox.carrier U n

theorem boxExhaustion_monotone (U : Set (ι → ℝ)) : Monotone (boxExhaustion U) :=
  CountableFamily.stage_mono BoxBasis.Globalization.RationalBox.carrier U

theorem isOpen_boxExhaustion (U : Set (ι → ℝ)) (n : ℕ) :
    IsOpen (boxExhaustion U n) :=
  CountableFamily.isOpen_stage BoxBasis.Globalization.RationalBox.carrier U BoxBasis.Globalization.RationalBox.isOpen_carrier n

/-- The stages cover exactly the original Euclidean open set. -/
theorem iUnion_boxExhaustion {U : Set (ι → ℝ)} (hU : IsOpen U) :
    (⋃ n, boxExhaustion U n) = U :=
  CountableFamily.iUnion_stage BoxBasis.Globalization.RationalBox.carrier U fun _ hx =>
    BoxBasis.Globalization.RationalBox.exists_mem_subset hU hx

theorem exists_boxExhaustion_contains_compact {U K : Set (ι → ℝ)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ n, K ⊆ boxExhaustion U n :=
  CountableFamily.compact_subset_stage BoxBasis.Globalization.RationalBox.carrier U
    BoxBasis.Globalization.RationalBox.isOpen_carrier (fun _ hx => BoxBasis.Globalization.RationalBox.exists_mem_subset hU hx) hK hKU

/-- Every compact subset lies in every sufficiently late finite union of boxes. -/
theorem eventually_boxExhaustion_contains_compact {U K : Set (ι → ℝ)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N, ∀ n, N ≤ n → K ⊆ boxExhaustion U n :=
  CountableFamily.compact_eventually_subset_stage BoxBasis.Globalization.RationalBox.carrier U
    BoxBasis.Globalization.RationalBox.isOpen_carrier (fun _ hx => BoxBasis.Globalization.RationalBox.exists_mem_subset hU hx) hK hKU

end

end OAI.Topology.Euclidean.BoxExhaustion.Globalization
