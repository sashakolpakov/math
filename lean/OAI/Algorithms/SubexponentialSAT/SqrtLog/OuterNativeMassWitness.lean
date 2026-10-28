import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeMassQueries
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeBoundedSpec

namespace OAI.Algorithms

/-! Exact marked counts yield the literal score bytes expected by the
selector. The reference stream and its total mass are proved here; no
per-reference semantic oracle remains in the bounded witness interface. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram
noncomputable section

 theorem bounded_mass_witness {n : ℕ} (k : ℕ) (F : OuterQuery.Formula n)
    (hm : 0 < (formulaRecords F).length) (a : Data) (width L Q : ℕ)
    (rows : HashSelectProgram.Records) (bits : List Bool)
    (worker : WorkerEmpty a)
    (sources : ∀ i, LeafOuterNative.MassSource i → (a.stacks i).length ≤ L)
    (hmod : BinaryArithmetic.toNat (a.stacks 782)=(formulaRecords F).length)
    (hamb : BinaryArithmetic.toNat (a.stacks 785)=n)
    (cost widths : List Bool → ℕ)
    (queries : LeafOuterNative.MassQueries k
      (LeafOuterNative.savedRegisters LeafOuterNative.callerRegisters a)
      (referenceCount F hm width (bits::rows)) cost widths (ValidReference hm))
    (bound : ∀ ref, ValidReference hm ref → cost ref ≤ Q) :
    Nonempty (LeafOuterNative.BoundedMassWitness k a
      (massScore (formulaClauses F) width rows bits) L Q) := by
  have hrecords : LeafOuterNative.massRecords a=
      RowSelectionProgram.Index.alphabet (formulaRecords F).length := by
    simp only [LeafOuterNative.massRecords,CounterPrograms.value_eq_toNat,hmod]
  have hp : LeafOuterNative.massPrecision a=LeafParametersProgram.precision n F.length := by
    simp only [LeafOuterNative.massPrecision,hmod,hamb,
      formulaRecords_length]
  refine ⟨{
    count := referenceCount F hm width (bits::rows)
    queryCost := cost
    width := widths
    valid := ValidReference hm
    z := HashSelect.mass (HashSelect.cnfRowAccept (formulaClauses F))
      (HashInput.violationWeight (formulaClauses F))
      ((bits::rows).map (HashFamilyPayload.decodeVariableRow F.length width))
    worker := worker
    sources := sources
    modulus := by rw [hmod]; omega
    queries := queries
    references := by rw [hrecords]; exact alphabet_validReferences hm
    queryBound := by intro ref href; exact bound ref (by
      apply alphabet_validReferences hm ref; simpa only [hrecords] using href)
    sum := by rw [hrecords]; exact referenceCount_sum F hm width (bits::rows)
    capacity := by rw [hp]; exact HashSelect.cnf_mass_lt_binary_capacity (formulaClauses F) _
    bytes := by rw [hp]; rfl
  }⟩

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
