import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideValue
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMarked

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
variable {X Row : Type*} [Fintype X] {m : ℕ}

theorem value_program_marked (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (reference : Fin m → List Bool) (hvalid : ∀ e, valid (reference e))
    (hcount : ∀ e, count (reference e) = markedCount rowAccept rows bad e)
    (suffix : List Bool) (base : Data) (hb : invariant ready base) (hzero : read base = [])
    (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = HashSelect.mass rowAccept (violationWeight bad) rows ∧
      RunsIn (program query) (valueBudget queryCost width (List.ofFn reference) [])
        ((RecordPrograms.state recordPorts base v pr f
          (Encoding.encodeList id (List.ofFn reference)++suffix) []).withPC (some (program query).entry))
        ((RecordPrograms.state recordPorts next false true false suffix []).withPC none) := by
  obtain ⟨next,hi,hv,ht⟩ := value_program_run query count queryCost width ready valid hq
    (List.ofFn reference) suffix base (by
      intro bits hh
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hh
      exact hvalid e) hb v pr f
  refine ⟨next,hi,?_,by simpa [hzero] using ht⟩
  rw [hv,hzero]
  simp only [BinaryArithmetic.toNat,zero_add,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  simp_rw [hcount]
  exact sum_markedCount rowAccept rows bad

theorem value_primitive_run (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (records : List (List Bool)) (suffix : List Bool) (base : Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : invariant ready base) (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      Computation.RunsIn (BitProgram.primitive (program query)).step
        (BitProgram.primitiveOverhead (program query)*valueBudget queryCost width records (read base))
        (BitProgram.primitiveCfg (program query)
          ((RecordPrograms.state recordPorts base v pr f
            (Encoding.encodeList id records++suffix) []).withPC (some (program query).entry)))
        (BitProgram.primitiveCfg (program query)
          ((RecordPrograms.state recordPorts next false true false suffix []).withPC none)) := by
  obtain ⟨next,hi,hv,ht⟩ := value_program_run query count queryCost width ready valid hq
    records suffix base hrecords hb v pr f
  exact ⟨next,hi,hv,BitProgram.primitive_execution (program query) ht⟩

/-- The exact weighted mass is produced by one finite primitive machine. -/
theorem value_primitive_marked (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (reference : Fin m → List Bool) (hvalid : ∀ e, valid (reference e))
    (hcount : ∀ e, count (reference e) = markedCount rowAccept rows bad e)
    (suffix : List Bool) (base : Data) (hb : invariant ready base) (hzero : read base = [])
    (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = HashSelect.mass rowAccept (violationWeight bad) rows ∧
      Computation.RunsIn (BitProgram.primitive (program query)).step
        (BitProgram.primitiveOverhead (program query)*
          valueBudget queryCost width (List.ofFn reference) [])
        (BitProgram.primitiveCfg (program query)
          ((RecordPrograms.state recordPorts base v pr f
            (Encoding.encodeList id (List.ofFn reference)++suffix) []).withPC (some (program query).entry)))
        (BitProgram.primitiveCfg (program query)
          ((RecordPrograms.state recordPorts next false true false suffix []).withPC none)) := by
  obtain ⟨next,hi,hv,ht⟩ := value_program_marked query count queryCost width ready valid hq
    rowAccept rows bad reference hvalid hcount suffix base hb hzero v pr f
  exact ⟨next,hi,hv,BitProgram.primitive_execution (program query) ht⟩

theorem value_inputSize_le (width : List Bool → ℕ) (records : List (List Bool)) (L W : ℕ)
    (hL : ∀ bits ∈ records, bits.length ≤ L) (hW : ∀ bits ∈ records, width bits ≤ W) :
    valueInputSize width records ≤ records.length*(L+W+1) := by
  induction records with
  | nil => simp [valueInputSize]
  | cons bits rest ih =>
      have hl := hL bits (by simp)
      have hw := hW bits (by simp)
      have hr := ih (fun x hx => hL x (by simp [hx])) (fun x hx => hW x (by simp [hx]))
      simp only [valueInputSize,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

theorem value_querySum_le (queryCost : List Bool → ℕ) (records : List (List Bool))
    (T : ℕ) (hT : ∀ bits ∈ records, queryCost bits ≤ T) :
    (records.map queryCost).sum ≤ records.length*T := by
  induction records with
  | nil => simp
  | cons bits rest ih =>
      have ht := hT bits (by simp)
      have hr := ih (fun x hx => hT x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem value_budget_le (queryCost width : List Bool → ℕ)
    (records : List (List Bool)) (acc : List Bool) (L W T : ℕ)
    (hL : ∀ bits ∈ records, bits.length ≤ L)
    (hW : ∀ bits ∈ records, width bits ≤ W)
    (hT : ∀ bits ∈ records, queryCost bits ≤ T) :
    valueBudget queryCost width records acc ≤
      4+records.length*T+records.length*(22*(acc.length+records.length*(L+W+1))+26) := by
  have hs := value_inputSize_le width records L W hL hW
  have ht := value_querySum_le queryCost records T hT
  dsimp [valueBudget]
  gcongr
end SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide

end OAI.Algorithms
