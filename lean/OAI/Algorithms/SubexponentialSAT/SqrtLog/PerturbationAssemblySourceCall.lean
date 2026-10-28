import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyFactorInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyInput

namespace OAI.Algorithms

/-! The actual literal-loop call changes only its key, index and accumulated
table. All physical source masters and blank working cells are preserved. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def sourceCallData (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) : OuterData :=
  ⟨regs,Function.update (literalReady s (List.replicate j true) acc) 555 (Encoding.encodeNat j)⟩

theorem sourceCallData_frame (s : OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) (i : Fin 768) (hk : i≠555) (ha : i≠569) (hj : i≠573) :
    (sourceCallData s j acc regs).stacks i=s i := by
  simp only [sourceCallData,literalReady,Function.update_of_ne hk,
    Function.update_of_ne ha,Function.update_of_ne hj]

theorem sourceCallData_key (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    (sourceCallData s j acc regs).stacks 555=Encoding.encodeNat j := by
  simp [sourceCallData]

theorem sourceCallData_index (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    (sourceCallData s j acc regs).stacks 573=List.replicate j true := by
  simp [sourceCallData,literalReady]

theorem sourceCallData_acc (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    (sourceCallData s j acc regs).stacks 569=acc := by
  simp [sourceCallData,literalReady]

theorem sourceCallData_clean (s : OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool)
    (h : ∀ i : Fin 340,i∉LeafProgram.SourceReady.physicalLive →
      s (LeafProgram.SourceReady.localPort i)=[]) :
    ∀ i : Fin 340,i∉LeafProgram.SourceReady.physicalLive →
      (sourceCallData s j acc regs).stacks (LeafProgram.SourceReady.localPort i)=[] := by
  intro i hi
  have hn : LeafProgram.SourceReady.localPort i≠555 ∧
      LeafProgram.SourceReady.localPort i≠569 ∧ LeafProgram.SourceReady.localPort i≠573 := by
    constructor
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi215 : i = 215 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi215]
    constructor
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi229 : i = 229 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi229]
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi233 : i = 233 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi233]
  exact (sourceCallData_frame s j acc regs _ hn.1 hn.2.1 hn.2.2).trans (h i hi)

theorem sourceCallData_arithmetic {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : OuterData) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : ArithmeticInput t model M cache (LeafProgram.SourceReady.rawLow a)) :
    ArithmeticInput t model M cache
      (LeafProgram.SourceReady.rawLow (sourceCallData a.stacks j acc regs)) := by
  apply h.frame_low
  intro i hi
  have hn : LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠555 ∧
      LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠569 ∧
      LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠573 := by
    constructor
    · intro he
      have hv := congrArg Fin.val he
      simp [LeafProgram.SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv
      omega
    constructor <;> intro he <;>
      have hv := congrArg Fin.val he <;>
      simp [LeafProgram.SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv <;>
      omega
  exact sourceCallData_frame a.stacks j acc regs _ hn.1 hn.2.1 hn.2.2

theorem sourceInput_at_call {r Q d : ℕ} (p : LayoutProgram.SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ))
    (P : Subexp.ConstructivePacking.PackingData (Fin ps.length) (MulticolorTypes.UniversalType r Q 1))
    (a : OuterData) (v n f S j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : LeafProgram.SourceReady.Input p ps P a v n f S)
    (hsize : ∀ i,((sourceCallData a.stacks j acc regs).stacks i).length ≤ S) :
    LeafProgram.SourceReady.Input p ps P (sourceCallData a.stacks j acc regs) j n f S := by
  constructor
  · exact sourceCallData_arithmetic p.model p.modulus p.cache a j acc regs h.arithmetic
  · exact sourceCallData_clean a.stacks j acc regs h.clean
  · simpa [sourceCallData,literalReady] using h.tmp
  · intro i hi
    have hn : i≠555 ∧ i≠569 ∧ i≠573 := by
      simp only [LeafProgram.SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact (sourceCallData_frame a.stacks j acc regs i hn.1 hn.2.1 hn.2.2).trans (h.backups i hi)
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.dimension
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.ambient
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.factor
  · simpa [LeafProgram.SourceReady.localPort,LayoutSourcePlanLookup.unary] using
      sourceCallData_index a.stacks j acc regs
  · simpa [sourceCallData,literalReady] using h.colors
  · simpa [sourceCallData,literalReady] using h.nodes
  · simpa [sourceCallData,literalReady] using h.typeWidth
  · simpa [sourceCallData,literalReady] using h.positive
  · simpa [sourceCallData,literalReady] using h.negative
  · simpa [sourceCallData,literalReady] using h.scalarWidth
  · simpa [sourceCallData,literalReady] using h.power
  · exact h.powerNegative
  · simpa [sourceCallData,literalReady] using h.radius
  · simpa [sourceCallData,literalReady] using h.offset
  · simpa [sourceCallData,literalReady] using h.metadata
  · simpa [sourceCallData,literalReady] using h.plans
  · simpa [sourceCallData,literalReady] using h.inverses
  · simpa [sourceCallData,literalReady] using h.negatives
  · simpa [sourceCallData,literalReady] using h.differences
  · simpa [sourceCallData,literalReady] using h.ringWidth
  · simpa [sourceCallData,literalReady] using h.rowWidth
  · simpa [sourceCallData,literalReady] using h.zero
  · simpa [sourceCallData,literalReady] using h.one
  · simpa [sourceCallData,literalReady] using h.minusOne
  · simpa [sourceCallData,literalReady] using h.inverseDenominator
  · exact hsize
  · exact h.arraySize
  · exact h.countSize
  · exact h.metadataSize
  · exact h.incidenceBound

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
