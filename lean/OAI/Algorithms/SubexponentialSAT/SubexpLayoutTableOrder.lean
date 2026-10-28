import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLeafTableOrder
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutScopeOrder

namespace OAI.Algorithms

/-! The concrete layout constructor's Boolean table bytes are exactly the
ordered LE factor-table payloads of the same typed leaf. Row labels remain
the responsibility of the separate physical label producer. -/

namespace SubexponentialSAT.SubexpLayoutTableOrder

open SubexpLayoutConstruction

variable {p : ℕ} [Fact p.Prime]

noncomputable def orderedTables (x : Inputs)
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p) : List (List Bool) :=
  SubexpLeafTableOrder.orderedTables G hG hell hcap

/-- The actual constructor and the semantic factor system have identical
Boolean payloads in identical factor and local-row order. -/
theorem table_payloads_eq (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell))
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p) :
    SubexpLayoutConstruction.tables x hv G = orderedTables x G hG hell hcap := by
  let cv := SubexpLayoutScopeOrder.canonicalValid x hv hD
  have hD' : dimension x = ChunkPartition.count (variableCount x)
      (BinaryArithmetic.toNat (familyInputs x).binaryEll) := by
    simpa only [familyInputs, CounterPrograms.value_eq_toNat] using hD
  have hcap' : 2 ^ BinaryArithmetic.toNat (familyInputs x).binaryEll ≤ p := by
    simpa only [familyInputs, CounterPrograms.value_eq_toNat] using hcap
  have hfamily := SubexpLeafTableOrder.family_tables_dimension_eq (familyInputs x) hv cv G hD'
  have h := SubexpLeafTableOrder.produced_tables_eq (familyInputs x) cv G hG hcap' hp
  rw [SubexpLayoutConstruction.tables, hfamily]
  simpa only [familyInputs, prefixTables, orderedTables,
    CounterPrograms.value_eq_toNat] using h

/-- Exact equality of the framed table stream consumed by the source builder. -/
theorem table_stream_eq (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell))
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p) :
    Encoding.encodeList id (SubexpLayoutConstruction.tables x hv G) =
      Encoding.encodeList id (orderedTables x G hG hell hcap) := by
  rw [table_payloads_eq x hv G hG hell hD hp hcap]

/-- The byte equality comes from the actual complete constructor trace;
no table-output equality is supplied as a premise. -/
theorem program_tables_correct (regs : Fin 16 → Bool) (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell))
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p)
    (hsource : x.leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes G) :
    ∃ out : Data,
      BitProgram.RunsIn SubexpLayoutConstruction.program (runtimeBound x hv G)
        ((SubexpLayoutRawPreparation.inputState regs x).withPC
          (some SubexpLayoutConstruction.program.entry)) (out.withPC none) ∧
      out.stacks 32 = Encoding.encodeList id (orderedTables x G hG hell hcap) := by
  have hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length := by
    simpa only [familyInputs, SubexpClauseMastersProgram.unary, List.length_replicate] using
      hv.ell_width
  obtain ⟨out, he, ht, _⟩ := SubexpLayoutConstruction.program_runs regs x hell hwidth hv G hsource
  exact ⟨out, he, ht.trans (table_stream_eq x hv G hG hell hD hp hcap)⟩

end SubexponentialSAT.SubexpLayoutTableOrder

end OAI.Algorithms
