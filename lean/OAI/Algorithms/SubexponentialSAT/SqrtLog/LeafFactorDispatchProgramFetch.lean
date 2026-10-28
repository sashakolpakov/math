import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

namespace OAI.Algorithms

/-! The selected payload is fetched by scanning the actual source record list. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def masterPort (marked : Bool) : Fin 16 := if marked then 1 else 0
def fetchRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def fetchPorts (marked : Bool) : Fin 6 → Fin 16 := ![masterPort marked,10,6,11,12,15]
def fetch (marked : Bool) : Code := .call
  (ProgramLinking.liftProgram HashInputProgram.Source.fetchProgram fetchRegs (fetchPorts marked))

def fetched (d : Data) (flag : Bool) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 flag,
    Function.update (Function.update d.stacks 6 []) 15 bits⟩

theorem fetch_eval (marked : Bool) (d : Data) (records : List (List Bool))
    (i : Fin records.length)
    (hm : d.stacks (masterPort marked)=Encoding.encodeList id records)
    (hi : d.stacks 6=Encoding.encodeNat i.val)
    (hc : ∀ j ∈ ([10,11,12,15] : List (Fin 16)), d.stacks j=[]) :
    ∃ flag n, n ≤ 23*(Encoding.encodeList id records).length+19 ∧
      Eval (fetch marked) n d (fetched d flag records[i.val]) := by
  have hir : Function.Injective fetchRegs := Fin.castAdd_injective _ _
  have hip : Function.Injective (fetchPorts marked) := by cases marked <;> decide
  let a := HashInputProgram.Source.data (d.regs 0) (d.regs 1) (d.regs 2)
    (Encoding.encodeList id records) [] (Encoding.encodeNat i.val) [] [] []
  obtain ⟨flag,n,hn,ht⟩ := HashInputProgram.Source.fetch_original_runs records i
    (d.regs 0) (d.regs 1) (d.regs 2)
  let b := HashInputProgram.Source.data false false flag (Encoding.encodeList id records)
    [] [] [] [] records[i.val]
  have ha : embedState fetchRegs (fetchPorts marked) d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ hir hip
    · intro j; fin_cases j <;> rfl
    · intros; rfl
    · intro j; fin_cases j <;> simp [a,fetchPorts,HashInputProgram.Source.data,hm,hi,
        hc 10 (by decide),hc 11 (by decide),hc 12 (by decide),hc 15 (by decide)]
    · intros; rfl
  have hb : embedState fetchRegs (fetchPorts marked) d b=fetched d flag records[i.val] := by
    apply embedState_eq_of_ports _ _ _ _ _ hir hip
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h0 : j≠0 := fun h => hj ⟨0,h.symm⟩
      have h1 : j≠1 := fun h => hj ⟨1,h.symm⟩
      have h2 : j≠2 := fun h => hj ⟨2,h.symm⟩
      simp [fetched,h0,h1,h2]
    · intro j; fin_cases j <;> cases marked <;>
        simp [fetched,b,fetchPorts,masterPort,HashInputProgram.Source.data,
          hc 10 (by decide),hc 11 (by decide),hc 12 (by decide)] <;>
        simpa [masterPort] using hm
    · intro j hj
      have h6 : j≠6 := fun h => hj ⟨2,h.symm⟩
      have h15 : j≠15 := fun h => hj ⟨5,h.symm⟩
      simp [fetched,h6,h15]
  have he := eval_call_lifted HashInputProgram.Source.fetchProgram fetchRegs
    (fetchPorts marked) d hir hip (a := a) (b := b) ht
  rw [ha,hb] at he
  exact ⟨flag,n,hn,he⟩

theorem fetched_stable (d : Data) (flag : Bool) (bits : List Bool) :
    Stable d (fetched d flag bits) := by
  intro i hi
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h2 : i≠2 := by intro h; subst i; simp at hi
  simp [fetched,h0,h1,h2]

/-- This is a serialization identity, not an extra preprocessing pass. -/
theorem encode_clausePayloads {n : ℕ} (F : ExecQuantitativeSparsify.Formula n) :
    Encoding.encodeList id (F.map HashInputProgram.clausePayload)=
      ExecQuantitativeSparsify.encodeRawFormula F := by
  rw [ExecSparsifyEncoding.encodeList_map,ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  congr 1
  funext ls
  exact HashInputProgram.clausePayload_codes ls

/-- This specialization starts with the immutable serialized leaf CNF itself. -/
theorem fetch_leaf_eval {n : ℕ} (d : Data) (F : ExecQuantitativeSparsify.Formula n)
    (i : Fin F.length)
    (hm : d.stacks 1=ExecQuantitativeSparsify.encodeRawFormula F)
    (hi : d.stacks 6=Encoding.encodeNat i.val)
    (hc : ∀ j ∈ ([10,11,12,15] : List (Fin 16)),d.stacks j=[]) :
    ∃ flag ticks, ticks ≤ 23*(ExecQuantitativeSparsify.encodeRawFormula F).length+19 ∧
      Eval (fetch true) ticks d (fetched d flag (HashInputProgram.clausePayload F[i.val])) := by
  have heq := encode_clausePayloads F
  let j : Fin (F.map HashInputProgram.clausePayload).length := ⟨i.val,by simp⟩
  have h := fetch_eval true d (F.map HashInputProgram.clausePayload) j
    (by simpa [masterPort,heq] using hm) hi hc
  simpa [heq,j] using h

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
