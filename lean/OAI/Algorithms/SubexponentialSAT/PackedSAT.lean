import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FactorReduction
import OAI.Algorithms.SubexponentialSAT.ChunkPartition
import OAI.Algorithms.SubexponentialSAT.Incidence
import OAI.Algorithms.SubexponentialSAT.Layout
import OAI.Algorithms.SubexponentialSAT.Counting
import OAI.Algorithms.SubexponentialSAT.Interfaces
import OAI.Algorithms.SubexponentialSAT.Sparsify

namespace OAI.Algorithms

/-!
# Concrete packed CNF systems and the counting pipeline

This module records the actual variable partition and bounded factor pattern.
The final counting composition makes no running-time claim.
-/

namespace SubexponentialSAT.PackedSAT

open scoped BigOperators

section Incidence

variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
variable {b : J → ℕ}

/-- The original variable scope of an actual CNF clause. -/
def variableScope (F : SAT.CNF V) (C : {C // C ∈ F}) : Finset V :=
  C.val.image SAT.Literal.variable

omit [Fintype V] in
theorem mem_variableScope (F : SAT.CNF V) (C : {C // C ∈ F}) (v : V) :
    v ∈ variableScope F C ↔ ∃ l ∈ C.val, l.variable = v := by
  simp only [variableScope, Finset.mem_image]

omit [Fintype V] in
/-- Clause-subtype indexing does not change the number of occurrences. -/
theorem degree_variableScope (F : SAT.CNF V) (v : V) :
    Incidence.degree (variableScope F) v = SAT.occurrences v F := by
  classical
  unfold Incidence.degree Incidence.incident SAT.occurrences
  apply Finset.card_bij (fun C _ => C.val)
  · intro C hC
    exact Finset.mem_filter.mpr ⟨C.property,
      (mem_variableScope F C v).mp (Finset.mem_filter.mp hC).2⟩
  · intro C hC D hD h
    exact Subtype.ext h
  · intro C hC
    refine ⟨⟨C, (Finset.mem_filter.mp hC).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_variableScope F _ v).mpr (Finset.mem_filter.mp hC).2⟩

def chunkOf (positions : V ≃ (j : J) × Fin (b j)) (v : V) : J :=
  (positions v).1

omit [DecidableEq V] in
/-- Each chunk fiber contains exactly its declared number of Boolean bits. -/
theorem card_chunkFiber (positions : V ≃ (j : J) × Fin (b j)) (j : J) :
    (Incidence.chunkFiber (chunkOf positions) j).card = b j := by
  classical
  let offset : (v : V) → v ∈ Incidence.chunkFiber (chunkOf positions) j → Fin (b j) :=
    fun v hv => ⟨(positions v).2.val, by
      have hj : (positions v).1 = j :=
        (Incidence.mem_chunkFiber (chunkOf positions) j v).mp hv
      simpa only [← hj] using (positions v).2.isLt⟩
  calc
    (Incidence.chunkFiber (chunkOf positions) j).card =
        (Finset.univ : Finset (Fin (b j))).card := by
      apply Finset.card_bij offset
      · intro v hv
        exact Finset.mem_univ _
      · intro v hv w hw h
        apply positions.injective
        have hvj : (positions v).1 = j :=
          (Incidence.mem_chunkFiber (chunkOf positions) j v).mp hv
        have hwj : (positions w).1 = j :=
          (Incidence.mem_chunkFiber (chunkOf positions) j w).mp hw
        have hhead := hvj.trans hwj.symm
        apply Sigma.ext hhead
        apply (Fin.heq_ext_iff (congrArg b hhead)).mpr
        exact congrArg Fin.val h
      · intro i hi
        have hmem : positions.symm ⟨j, i⟩ ∈ Incidence.chunkFiber (chunkOf positions) j := by
          simp [Incidence.mem_chunkFiber, chunkOf]
        refine ⟨positions.symm ⟨j, i⟩, hmem, ?_⟩
        apply Fin.ext
        change (fun s : (j : J) × Fin (b j) => s.2.val)
          (positions (positions.symm ⟨j, i⟩)) = i.val
        rw [positions.apply_symm_apply]
    _ = b j := by simp

omit [Fintype V] in
theorem cnfScope_eq_packedScope (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) :
    FactorReduction.cnfScope positions F =
      Incidence.packedScope (variableScope F) (chunkOf positions) := by
  funext C
  simp [FactorReduction.cnfScope, Incidence.packedScope, variableScope,
    Finset.image_image, chunkOf, Function.comp_def]

theorem degree_cnfScope_le (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) (ell B : ℕ) (hsize : ∀ j, b j ≤ ell)
    (hocc : SAT.OccurrenceAtMost B F) (j : J) :
    Incidence.degree (FactorReduction.cnfScope positions F) j ≤ ell * B := by
  rw [cnfScope_eq_packedScope]
  apply Incidence.degree_packedScope_le
  · simpa only [card_chunkFiber] using hsize j
  · intro v
    simpa only [degree_variableScope] using hocc v

/-- `FactorReduction` puts unary indices on the left of the sum; the generic
incidence library puts them on the right. This proves the bound for the actual
constructed system without silently identifying those two index types. -/
theorem degree_factorScope [Fintype J] {E : Type*} [Fintype E] [DecidableEq E]
    (scope : E → Finset J) (j : J) :
    Incidence.degree (FactorReduction.factorScope scope) j =
      1 + Incidence.degree scope j := by
  rw [Incidence.degree_eq_sum, Fintype.sum_sum_type]
  simp only [FactorReduction.factorScope, Finset.mem_singleton]
  change ((∑ x : J, if j = x then 1 else 0) +
    ∑ e : E, if j ∈ scope e then 1 else 0) = 1 + Incidence.degree scope j
  rw [← Incidence.degree_eq_sum]
  simp

theorem cnfFactorSystem_bounded [Fintype J] {A : Type*} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V)
    (k ell B : ℕ) (hk : 1 ≤ k) (hwidth : SAT.WidthAtMost k F)
    (hocc : SAT.OccurrenceAtMost B F) (hsize : ∀ j, b j ≤ ell)
    (hne : ∀ C ∈ F, C.Nonempty) :
    (FactorReduction.cnfFactorSystem positions enc F).toPattern.Bounded k (1 + ell * B) := by
  constructor
  · exact FactorReduction.cnfFactorSystem_scope_nonempty positions enc F hne
  · exact FactorReduction.cnfFactorSystem_scope_card_le positions enc F hk hwidth
  · intro j
    change Incidence.degree (FactorReduction.factorScope
      (FactorReduction.cnfScope positions F)) j ≤ _
    rw [degree_factorScope]
    exact Nat.add_le_add_left (degree_cnfScope_le positions F ell B hsize hocc j) 1

end Incidence

section CanonicalPacking

variable {p k ell B n : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem capacity (hcap : 2 ^ ell ≤ p) (j : Fin (ChunkPartition.count n ell)) :
    2 ^ ChunkPartition.size n ell j ≤ p :=
  (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (ChunkPartition.size_le n ell j)).trans hcap

/-- Pack the original `Fin n` coordinates by quotient and remainder. -/
noncomputable def packedSystem (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n)) :
    Factor.System (Fin (ChunkPartition.count n ell))
      (Fin (ChunkPartition.count n ell) ⊕ {C // C ∈ F}) (ZMod p) :=
  FactorReduction.primeLabelCNF (ChunkPartition.indexEquiv n ell hell)
    (capacity hcap) F

theorem packedSystem_count (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (F : SAT.CNF (Fin n)) : Factor.count (packedSystem hell hcap F) = SAT.count F :=
  FactorReduction.primeLabelCNF_count (ChunkPartition.indexEquiv n ell hell)
    (capacity hcap) F

theorem clauses_nonempty_of_empty_not_mem (F : SAT.CNF (Fin n))
    (h : (∅ : SAT.Clause (Fin n)) ∉ F) : ∀ C ∈ F, C.Nonempty := by
  intro C hC
  apply Finset.nonempty_iff_ne_empty.mpr
  intro heq
  exact h (heq ▸ hC)

theorem count_zero_of_empty_mem (F : SAT.CNF (Fin n))
    (h : (∅ : SAT.Clause (Fin n)) ∈ F) : SAT.count F = 0 :=
  (SAT.count_eq_zero_iff F).mpr (SAT.not_satisfiable_of_empty_mem h)

theorem packedSystem_bounded (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (F : SAT.CNF (Fin n)) (hk : 1 ≤ k) (hwidth : SAT.WidthAtMost k F)
    (hocc : SAT.OccurrenceAtMost B F) (hne : (∅ : SAT.Clause (Fin n)) ∉ F) :
    (packedSystem hell hcap F).toPattern.Bounded k (1 + ell * B) :=
  cnfFactorSystem_bounded (ChunkPartition.indexEquiv n ell hell)
    (fun j => BooleanPacking.chunkZModEmbedding (capacity hcap j)) F k ell B hk hwidth hocc
    (ChunkPartition.size_le n ell) (clauses_nonempty_of_empty_not_mem F hne)

/-- The finite layout construction is selected before the input size and CNF. -/
noncomputable def fixedConstruction (hodd : Odd p) (hk : 0 < k) :
    Layout.Construction p k (1 + ell * B) :=
  Classical.choice (Layout.exists_construction p k (1 + ell * B) hodd hk (by omega))

/-- Include dimension zero in the fixed finite fallback range. -/
def smallThreshold (C : Layout.Construction p k (1 + ell * B)) : ℕ :=
  max 1 C.constants.Dstar

theorem small_input_bound (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hsmall : ChunkPartition.count n ell < smallThreshold C) :
    n ≤ ell * smallThreshold C := by
  have h := (ChunkPartition.le_count_mul (n := n) hell).trans
    (Nat.mul_le_mul_right ell hsmall.le)
  simpa only [Nat.mul_comm] using h

theorem large_dimension_pos (C : Layout.Construction p k (1 + ell * B))
    (hlarge : ¬ ChunkPartition.count n ell < smallThreshold C) :
    0 < ChunkPartition.count n ell := by
  have h := le_max_left 1 C.constants.Dstar
  unfold smallThreshold at hlarge
  omega

theorem large_size_ge (C : Layout.Construction p k (1 + ell * B))
    (hlarge : ¬ ChunkPartition.count n ell < smallThreshold C) :
    C.constants.Dstar ≤ ChunkPartition.count n ell := by
  have h := le_max_right 1 C.constants.Dstar
  unfold smallThreshold at hlarge
  omega

/-- The supplied pattern is proved bounded, and the previously fixed universal
construction supplies its actual layout. No layout property is postulated. -/
noncomputable def packedLayout (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F)
    (hne : (∅ : SAT.Clause (Fin n)) ∉ F)
    (hlarge : ¬ ChunkPartition.count n ell < smallThreshold C) :
    LayoutSpec.Layout (E := Layout.Extension p C.constants.h)
      (packedSystem hell hcap F).toPattern C.constants :=
  Classical.choice (C.layout_exists (packedSystem hell hcap F).toPattern
    (packedSystem_bounded hell hcap F C.constants.k_pos hwidth hocc hne)
    (by simpa only [Fintype.card_fin] using large_size_ge C hlarge))

/-- The large-input branch is the defined separated-moment/CRT count, using
the actual prime-power ring and its natural-number decoder. -/
noncomputable def largeCount (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F)
    (hne : (∅ : SAT.Clause (Fin n)) ∉ F)
    (hlarge : ¬ ChunkPartition.count n ell < smallThreshold C) : ℕ :=
  Counting.actualCount (packedSystem hell hcap F)
    (packedLayout C hell hcap F hwidth hocc hne hlarge)

theorem largeCount_eq_count (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F)
    (hne : (∅ : SAT.Clause (Fin n)) ∉ F)
    (hlarge : ¬ ChunkPartition.count n ell < smallThreshold C) :
    largeCount C hell hcap F hwidth hocc hne hlarge = SAT.count F := by
  exact (Counting.actualCount_eq_count (packedSystem hell hcap F)
    (packedLayout C hell hcap F hwidth hocc hne hlarge)
    (by simpa only [Fintype.card_fin] using large_dimension_pos C hlarge)).trans
      (packedSystem_count hell hcap F)

/-- Explicit finite enumeration, used only below the fixed dimension cutoff. -/
def smallCount (F : SAT.CNF (Fin n)) : ℕ :=
  ∑ a : Fin n → Bool, if F.eval a = true then 1 else 0

theorem smallCount_eq_count (F : SAT.CNF (Fin n)) : smallCount F = SAT.count F := by
  simp [smallCount, SAT.count, SAT.satisfyingAssignments]

/-- A bounded-occurrence CNF pipeline. Empty clauses return zero immediately;
the fixed finite dimension range is enumerated; all remaining inputs use the
actual constructed layout, separated jets, CRT, and prime-power decoder. -/
noncomputable def boundedCount (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F) : ℕ :=
  if he : (∅ : SAT.Clause (Fin n)) ∈ F then 0
  else if hs : ChunkPartition.count n ell < smallThreshold C then smallCount F
  else largeCount C hell hcap F hwidth hocc he hs

theorem boundedCount_eq_count (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F) :
    boundedCount C hell hcap F hwidth hocc = SAT.count F := by
  unfold boundedCount
  split
  · rename_i he
    exact (count_zero_of_empty_mem F he).symm
  · split
    · exact smallCount_eq_count F
    · exact largeCount_eq_count C hell hcap F hwidth hocc _ _

noncomputable def boundedDecision (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F) : Bool :=
  decide (0 < boundedCount C hell hcap F hwidth hocc)

theorem boundedDecision_eq_true_iff (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F) :
    boundedDecision C hell hcap F hwidth hocc = true ↔ SAT.Satisfiable F := by
  simp only [boundedDecision, decide_eq_true_eq, boundedCount_eq_count, SAT.count_pos_iff]

theorem zero_input_in_small_range (C : Layout.Construction p k (1 + ell * B))
    (hell : 0 < ell) : ChunkPartition.count 0 ell < smallThreshold C := by
  rw [ChunkPartition.count_zero hell]
  exact lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

/-- One set of finite construction constants works for every input size and
every CNF satisfying the fixed width and occurrence bounds. This is a
mathematical correctness assertion, not a machine-running-time assertion. -/
theorem exists_fixed_counting_pipeline (hodd : Odd p) (hk : 0 < k)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) :
    ∃ C : Layout.Construction p k (1 + ell * B),
      ∀ (n : ℕ) (F : SAT.CNF (Fin n))
        (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F),
        boundedCount C hell hcap F hwidth hocc = SAT.count F := by
  exact ⟨fixedConstruction hodd hk,
    fun _ F hwidth hocc => boundedCount_eq_count _ hell hcap F hwidth hocc⟩

end CanonicalPacking

section SparseDecision

variable {p k ell n : ℕ} [Fact p.Prime]

/-- The occurrence bound is chosen from the width before the input varies. -/
def occurrenceBound (k : ℕ) (hk : 2 ≤ k) : ℕ :=
  SparsificationConstants.occurrenceCap (SparsificationConstants.chooseM k hk) k

abbrev BoundedLeaf (k B n : ℕ) :=
  {F : SAT.CNF (Fin n) // SAT.WidthAtMost k F ∧ SAT.OccurrenceAtMost B F}

/-- The actual deterministic sparsifier's output, carrying its proved bounds.
Attaching these proofs does not alter any leaf formula or duplicate a leaf. -/
def sparseLeaves (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) (hwidth : SAT.WidthAtMost k F) :
    List (BoundedLeaf k (occurrenceBound k hk) n) :=
  (Sparsify.sparsify k hk F).attach.map fun G =>
    (⟨G.val, Sparsify.sparsify_width k hk F hwidth G.val G.property,
      by simpa only [occurrenceBound] using
        Sparsify.sparsify_occurrence k hk F hwidth G.val G.property⟩ :
      BoundedLeaf k (occurrenceBound k hk) n)

theorem mem_sparseLeaves_iff (hk : 2 ≤ k) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) (G : BoundedLeaf k (occurrenceBound k hk) n) :
    G ∈ sparseLeaves hk F hwidth ↔ G.val ∈ Sparsify.sparsify k hk F := by
  simp only [sparseLeaves, List.mem_map]
  constructor
  · rintro ⟨H, hH, heq⟩
    have hval := congrArg Subtype.val heq
    exact hval ▸ H.property
  · intro hG
    refine ⟨⟨G.val, hG⟩, ?_, ?_⟩
    · simp
    · exact Subtype.ext rfl

@[simp] theorem sparseLeaves_length (hk : 2 ≤ k) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) :
    (sparseLeaves hk F hwidth).length = (Sparsify.sparsify k hk F).length := by
  simp [sparseLeaves]

/-- Short-circuit OR of the genuinely computed leaf decisions. Overlapping
leaves are intentionally never summed as counts of the original formula. -/
noncomputable def sparseScan (hk : 2 ≤ k)
    (C : Layout.Construction p k (1 + ell * occurrenceBound k hk))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) : Bool × ℕ :=
  Interfaces.scan
    (fun G : BoundedLeaf k (occurrenceBound k hk) n =>
      boundedDecision C hell hcap G.val G.property.1 G.property.2)
    (sparseLeaves hk F hwidth)

theorem sparseScan_accepts_iff (hk : 2 ≤ k)
    (C : Layout.Construction p k (1 + ell * occurrenceBound k hk))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) :
    (sparseScan hk C hell hcap F hwidth).1 = true ↔ SAT.Satisfiable F := by
  rw [sparseScan, Interfaces.scan_accepts_iff, Sparsify.sparsify_correct k hk F]
  constructor
  · rintro ⟨G, hG, htest⟩
    exact ⟨G.val, (mem_sparseLeaves_iff hk F hwidth G).mp hG,
      (boundedDecision_eq_true_iff C hell hcap G.val G.property.1 G.property.2).mp htest⟩
  · rintro ⟨G, hG, hsat⟩
    let leaf : BoundedLeaf k (occurrenceBound k hk) n :=
      ⟨G, Sparsify.sparsify_width k hk F hwidth G hG,
        Sparsify.sparsify_occurrence k hk F hwidth G hG⟩
    refine ⟨leaf, (mem_sparseLeaves_iff hk F hwidth leaf).mpr hG, ?_⟩
    exact (boundedDecision_eq_true_iff C hell hcap leaf.val
      leaf.property.1 leaf.property.2).mpr hsat

/-- A bound on calls to the leaf test; this is not a bit-runtime bound. -/
theorem sparseScan_calls_le (hk : 2 ≤ k)
    (C : Layout.Construction p k (1 + ell * occurrenceBound k hk))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) :
    (sparseScan hk C hell hcap F hwidth).2 ≤ (Sparsify.sparsify k hk F).length := by
  simpa only [sparseScan, sparseLeaves_length] using
    Interfaces.scan_calls_le_length
      (fun G : BoundedLeaf k (occurrenceBound k hk) n =>
        boundedDecision C hell hcap G.val G.property.1 G.property.2)
      (sparseLeaves hk F hwidth)

/-- All parameters and the universal layout construction are fixed from
`p,k,ell` before the input's variable count and clauses are supplied. -/
noncomputable def fixedDecision (hk : 2 ≤ k) (hodd : Odd p)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) : Bool :=
  (sparseScan hk (fixedConstruction hodd (by omega)) hell hcap F hwidth).1

/-- Mathematical correctness of the specified sparsify/pack/layout/count/OR
pipeline. No time bound or machine implementation is asserted. -/
theorem fixedDecision_correct (hk : 2 ≤ k) (hodd : Odd p)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hwidth : SAT.WidthAtMost k F) :
    fixedDecision hk hodd hell hcap F hwidth = true ↔ SAT.Satisfiable F :=
  sparseScan_accepts_iff hk _ hell hcap F hwidth

end SparseDecision

end SubexponentialSAT.PackedSAT

end OAI.Algorithms
