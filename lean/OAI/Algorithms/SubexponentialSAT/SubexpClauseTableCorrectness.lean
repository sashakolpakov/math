import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseScopeCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpRankedTable

namespace OAI.Algorithms

/-!
# The actual clause constructor and its canonical LE factor table

The constructor computes the scope and all descending-rank Boolean answers.
Its input representation facts supply the address and width obligations of
the generic materialized-table theorem. Pairing answers with the matching
grid is a mathematical stream interpretation; physical label serialization
remains the interpolation producer's responsibility.
-/

namespace SubexponentialSAT.SubexpClauseTableCorrectness

open BinaryArithmetic SubexpClauseFactorProgram SubexpClauseScopeCorrectness

variable {n p : ℕ} [Fact p.Prime]
variable (c : Inputs) (ls : List (SAT.Literal (Fin n)))
variable (hv : Valid c (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) ls)
variable (F : SAT.CNF (Fin n)) (e : {C // C ∈ F}) (hls : ls.toFinset = e.val)
variable (hcap : 2 ^ BinaryArithmetic.toNat c.binaryEll ≤ p)

/-- The local coordinates use the scope actually emitted by this clause. -/
noncomputable def scopeIndex : Fin (scopeOf c ls hv).length ≃
    {j // j ∈ (SubexpLEFactorSystem.packed hv.ell_pos hcap F).scope (.inr e)} :=
  SubexpLeafTables.scopeOfList (SubexpLEFactorSystem.packed hv.ell_pos hcap F)
    (.inr e) (scopeOf c ls hv) (scopeOf_nodup c ls hv)
    (scopeOf_mem_cnfScope c ls hv.ell_pos hv F e hls)

/-- No scope oracle, label validity premise, or row-result equality is
required: all are derived from the actual constructor inputs. -/
theorem table_eq_orderedRows {C : Type*} (zero one : C)
    (hp : BinaryArithmetic.toNat c.modulus = p) :
    SubexpRankedTable.attachAnswers zero one (table c (scopeOf c ls hv) ls) =
      SubexpLeafTables.orderedRows (SubexpLEFactorSystem.packed hv.ell_pos hcap F)
        (.inr e) (scopeIndex c ls hv F e hls hcap) zero one := by
  let scope := scopeOf c ls hv
  let m := tableMasters c scope
  have hcount : scope.length = m.arity.length := by
    simp [m, tableMasters, fieldMasters]
  have hell : m.ell.length ≤ m.modulus.length := by
    exact hv.ell_width.trans_eq hv.width
  have hn : n ≤ ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll) * m.ell.length := by
    have hcovered := hv.covered
    rw [hv.full] at hcovered
    simpa only [m, tableMasters, fieldMasters] using hcovered
  have hsize : ∀ j : Fin (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)),
      ChunkPartition.size n (BinaryArithmetic.toNat c.binaryEll) j =
        min m.ell.length (n - j.val * m.ell.length) := by
    intro j
    simp only [ChunkPartition.size, hv.ell_value]
    rfl
  have hpositions : ∀ v : Fin n,
      v.val = (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos v).1.val *
        m.ell.length + (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos v).2.val := by
    intro v
    change v.val = (v.val / BinaryArithmetic.toNat c.binaryEll) * c.ellShape.length +
      v.val % BinaryArithmetic.toNat c.binaryEll
    rw [← hv.ell_value]
    exact (Nat.div_add_mod' v.val (BinaryArithmetic.toNat c.binaryEll)).symm
  have h := SubexpRankedTable.attachAnswers_eq_orderedRows
    (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos)
    (PackedSAT.capacity (n := n) hcap) F e m scope (scopeOf_nodup c ls hv)
    (scopeOf_mem_cnfScope c ls hv.ell_pos hv F e hls)
    zero one ls hls hp hcount hell hn hsize hpositions
  simpa only [table, rowCount, hp, SubexpFieldTableEnumeration.rows, scopeIndex,
    SubexpLEFactorSystem.packed] using h

/-- The physical unit trace and the interpretation above refer to the very
same emitted scope and Boolean stream. The trace includes scope generation
and rank enumeration, rather than receiving either as a prepared table. -/
theorem program_correct {C : Type*} (zero one : C)
    (hp : BinaryArithmetic.toNat c.modulus = p) (regs : Fin 11 → Bool) :
    BitProgram.RunsIn program (budget c (scopeOf c ls hv) ls + 1)
      ((data regs c [] [] [] [] [] []).withPC (some program.entry))
      ((data zeroRegs c [] [] [] (scopeBytes c ls) []
        (table c (scopeOf c ls hv) ls)).withPC none) ∧
    SubexpRankedTable.attachAnswers zero one (table c (scopeOf c ls hv) ls) =
      SubexpLeafTables.orderedRows (SubexpLEFactorSystem.packed hv.ell_pos hcap F)
        (.inr e) (scopeIndex c ls hv F e hls hcap) zero one :=
  ⟨program_runsIn_raw c ls hv regs,
    table_eq_orderedRows c ls hv F e hls hcap zero one hp⟩

end SubexponentialSAT.SubexpClauseTableCorrectness

end OAI.Algorithms
