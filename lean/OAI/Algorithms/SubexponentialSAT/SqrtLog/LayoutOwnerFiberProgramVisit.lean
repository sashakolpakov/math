import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramParse
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramEmit

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

@[simp] theorem unary_eq (v q : ℕ) : unary v=unary q ↔ v=q := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa using hh
  · rintro rfl; rfl

def callback : Code := .seq parseOwner (.seq compareOwner finish)
def callbackCost (query index : ℕ) (p : ℕ × ℕ) : ℕ :=
  47*p.1+34*p.2+9*query+7*index+138

theorem callback_eval (regs : Fin 5 → Bool) (query index count : ℕ)
    (v f : ℕ) (master tail acc out : List Bool) :
    ∃ n ≤ callbackCost query index (v,f), ∃ rr,
      Eval callback n
        (data regs (unary query) master tail (pairPayload v f).reverse [] [] []
          (unary index) acc (unary count) out)
        (data (reset rr) (unary query) master tail [] [] [] [] (unary (index+1))
          (if v=query then (Encoding.encodeNat index).reverse++acc else acc)
          (unary (count+(if v=query then 1 else 0))) out) := by
  have h1 := parseOwner_eval regs v f (unary query) master tail (unary index) acc (unary count) out
  obtain ⟨n2,hn2,r2,h2,hflag⟩ := compareOwner_eval (status regs false false)
    (unary query) master tail (unary v) (unary index) acc (unary count) out
  have hf : r2 4=decide (v=query) := by simpa using hflag
  obtain ⟨n3,hn3,h3⟩ := finish_eval r2 (unary query) master tail acc out index count
    (decide (v=query)) hf
  refine ⟨(36*v+34*f+102)+(n2+n3),?_,r2,?_⟩
  · simp only [List.length_replicate] at hn2
    unfold callbackCost
    omega
  · simpa only [callback,decide_eq_true_eq] using h1.seq (h2.seq h3)

def outerPorts : RecordPrograms.Ports 5 11 where
  tag:=0; present:=1; found:=4; source:=2; payload:=3
  tag_ne_present:=by decide
  found_ne_tag:=by decide
  found_ne_present:=by decide
  source_ne_payload:=by decide

def outerRead : Code := RecordPrograms.reader outerPorts

theorem outerRead_eval (regs : Fin 5 → Bool)
    (q m bits tail i a c o : List Bool) :
    Eval outerRead (6*bits.length+4)
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      (data (status regs false true) q m tail bits.reverse [] [] [] i a c o) := by
  have h := RecordPrograms.reader_eval outerPorts
    (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
    bits tail [] (regs 0) (regs 1) (regs 4)
  have hin : RecordPrograms.state outerPorts
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      (regs 0) (regs 1) (regs 4) (Encoding.frame bits++tail) []=
      data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o := by
    apply RecordPrograms.state_eq_self <;> rfl
  have hout : RecordPrograms.state outerPorts
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      false true (regs 4) tail (bits.reverse++[])=
      data (status regs false true) q m tail bits.reverse [] [] [] i a c o := by
    apply state_ext
    · funext j; fin_cases j <;> simp [RecordPrograms.state,outerPorts,data,status]
    · funext j; fin_cases j <;> simp [RecordPrograms.state,outerPorts,data]
  rw [hin,hout] at h
  exact h

def popScan : Code := .base (.atom (.pop 2 0 1))

theorem popScan_eval (regs : Fin 5 → Bool) (b : Bool)
    (q m tail i a c o : List Bool) :
    Eval popScan 1 (data regs q m (b::tail) [] [] [] [] i a c o)
      (data (status regs b true) q m tail [] [] [] [] i a c o) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 11) (0 : Fin 5) 1)
    (data regs q m (b::tail) [] [] [] [] i a c o))
  convert h using 1
  · rfl
  · apply state_ext
    · funext j; fin_cases j <;> simp [data,status,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext j; fin_cases j <;> simp [data,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
