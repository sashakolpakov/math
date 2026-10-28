import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledLayout
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalTables

namespace OAI.Algorithms

/-! Bounds for the exact scope and Boolean table streams produced for a
sparse leaf. All orders agree with the physical producer. -/

namespace SubexponentialSAT.SubexpMainLayoutSizes

open SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainScheduledLayout

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {er es n k T : ℕ} {alloc : SubexpLayoutPorts.Allocation es}
variable {a : MainState er es} {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n k T G)

theorem scope_count (hk : 1 ≤ k) :
    (scopes input).length ≤ DyadicSchedule.delta k T n *
      SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) := by
  have h := Incidence.bounded_card_factors_le _ k (DyadicSchedule.delta k T n)
    (SubexpMainLayoutPattern.bounded alloc a G input hk)
  simpa only [scopes, Fintype.card_fin] using h

theorem scope_nodup (C : List ℕ) (hC : C ∈ scopes input) : C.Nodup := by
  change C ∈ (SubexpLeafData.factors _ _).values.map
    (fun e => (SubexpLeafData.scopes _ _ (ChunkPartition.indexEquiv _ _ input.ell_pos) e).map Fin.val) at hC
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hC
  exact (SubexpLeafData.scopes_nodup _ _ _ e).map Fin.val_injective

theorem scope_length (hk : 1 ≤ k) (C : List ℕ) (hC : C ∈ scopes input) : C.length ≤ k := by
  obtain ⟨e, rfl⟩ := List.mem_iff_get.mp hC
  let native := SubexpMainLayoutInput.castLeaf input.variableCount.symm G
  let index := SubexpMainPhysicalTables.scopeIndex native input.sparse.clause_sets_nodup
    input.ell_pos input.capacity input.dimension e
  have hc := Fintype.card_congr index
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  have hb := SubexpMainLayoutPattern.bounded alloc a G input hk
  change (Subexp.IncidencePlanSpec.pattern
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
    (SubexpLeafScopeOrder.rawScopes native input.sparse.clause_sets_nodup input.ell_pos)).Bounded
    k (DyadicSchedule.delta k T n) at hb
  rw [← SubexpMainPhysicalSystem.system_toPattern native input.sparse.clause_sets_nodup
    input.ell_pos input.capacity input.dimension] at hb
  exact hc.trans_le (hb.arity_le e)

theorem scope_values (C : List ℕ) (hC : C ∈ scopes input) (v : ℕ) (hv : v ∈ C) :
    v < SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) :=
  SubexpMainLayoutExecution.orderedScopes_valid _ _ input.sparse.clause_sets_nodup
    input.ell_pos input.dimension C hC v hv

theorem scope_bytes (hk : 1 ≤ k) :
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (scopes input)).length ≤
      1 + (2 * (1 + (2 * SubexpLayoutConstruction.dimension
        (SubexpMainLayout.Factors.sourceInputs alloc a) + 2) * k) + 2) * (scopes input).length := by
  apply Encoding.length_encodeList_upper
  intro C hC
  have hb := Encoding.length_encodeList_upper Encoding.encodeNat C
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (by
      intro v hv
      rw [Encoding.length_encodeNat]
      have := scope_values input C hC v hv
      omega)
  exact hb.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (scope_length input hk C hC)) 1)

theorem tables_eq : tables input = List.ofFn
    (SubexpMainPhysicalTables.table
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension) := by
  have hp : BinaryArithmetic.toNat
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus = p n := by
    rw [SubexpMainParameterValues.sourceInputs_modulus_word]
    simpa only [CounterPrograms.value_eq_toNat] using input.prime
  exact (SubexpLayoutTableOrder.table_payloads_eq _ (family input) _
    input.sparse.clause_sets_nodup input.ell_pos input.dimension hp input.capacity).trans
    (SubexpMainPhysicalTables.orderedTables_eq _ input.sparse.clause_sets_nodup
      input.ell_pos input.capacity input.dimension)

theorem table_count : (tables input).length = (scopes input).length := by
  rw [tables_eq input, List.length_ofFn]

theorem table_length (hk : 1 ≤ k) (row : List Bool) (hrow : row ∈ tables input) :
    row.length ≤ (p n)^k := by
  rw [tables_eq input] at hrow
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hrow
  rw [SubexpMainPhysicalTables.table_length]
  apply Nat.pow_le_pow_right (p_prime n).pos
  exact scope_length input hk _ (List.get_mem _ _)

theorem table_bytes (hk : 1 ≤ k) :
    (Encoding.encodeList id (tables input)).length ≤
      1 + (2 * (p n)^k + 2) * (scopes input).length := by
  have hb := Encoding.length_encodeList_upper id (tables input) ((p n)^k)
    (table_length input hk)
  simpa only [table_count input] using hb

theorem raw_leaf_bytes {cfg : Config} {n L : ℕ} (G : SubexpLeafData.Leaf n)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (hnL : n ≤ L) :
    (ExecQuantitativeSparsify.encodeRawFormula G).length ≤
      (8 * cfg.k + 5) * (L + 1)^(2 * cfg.k + 1) :=
  (ExecQuantitativeSparsify.encodeRawFormula_polynomial G cfg.k valid.2.1 valid.2.2.2).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hnL 1) _))

end SubexponentialSAT.SubexpMainLayoutSizes

end OAI.Algorithms
