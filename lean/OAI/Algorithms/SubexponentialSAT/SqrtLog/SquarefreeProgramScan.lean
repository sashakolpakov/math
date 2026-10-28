import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramErase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLookup

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev ByteRecord := List Bool × List Bool

def rawEntries : List ByteRecord → List Bool
  | [] => []
  | (key,payload) :: rest => Encoding.frame key ++ Encoding.frame payload ++ rawEntries rest

def erasedEntries (query : List Bool) (entries : List ByteRecord) : List ByteRecord :=
  entries.filter (fun a => decide (a.1 ≠ query))

abbrev erasedOutput (query : List Bool) : List ByteRecord → List Bool → List Bool
  | [], output => output
  | (key,payload) :: rest, output => erasedOutput query rest
      (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output)

abbrev erasePeek : Cmd 5 7 := storageCall SubexponentialSAT.Subexp.SelectorProgram.peek

abbrev eraseLoop : Cmd 5 7 := .while 1 (.seq eraseOne erasePeek)

abbrev eraseScan : Cmd 5 7 := .seq erasePeek eraseLoop

def eraseReady (regs : Fin 5 → Bool) (entries : List ByteRecord) (query output : List Bool) : StorageData :=
  eraseData (readRegs regs 0 1 (rawEntries entries).head?) (rawEntries entries) query output []

def eraseBudget (query : List Bool) : List ByteRecord → ℕ
  | [] => 1
  | (key,payload) :: rest =>
      28 * key.length + 9 * query.length + 13 * payload.length + 53 + eraseBudget query rest

theorem erasePeek_eval (regs : Fin 5 → Bool) (entries : List ByteRecord) (query output : List Bool) :
    Eval erasePeek 2 (eraseData regs (rawEntries entries) query output [])
      (eraseReady regs entries query output) :=
  storageCall_eval (SubexponentialSAT.Subexp.SelectorProgram.peek_eval regs (rawEntries entries) query.reverse output) []

theorem eraseReady_nil_guard (regs : Fin 5 → Bool) (query output : List Bool) :
    (eraseReady regs [] query output).regs 1 = false := by
  simp [eraseReady,eraseData,extendStorage,readRegs,rawEntries]

theorem eraseReady_cons_guard (regs : Fin 5 → Bool) (key payload query output : List Bool)
    (entries : List ByteRecord) :
    (eraseReady regs ((key,payload)::entries) query output).regs 1 = true := by
  cases key <;> simp [eraseReady,eraseData,extendStorage,readRegs,rawEntries,Encoding.frame]

theorem eraseLoop_eval (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries, ∃ final,
      Eval eraseLoop n (eraseReady regs entries query output)
        (eraseData final [] query (erasedOutput query entries output) []) := by
  induction entries generalizing output regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 1 none,?_⟩
    exact Eval.while_false (eraseReady_nil_guard regs query output)
  | cons a entries ih =>
    rcases a with ⟨key,payload⟩
    let rr := readRegs regs 0 1 (rawEntries ((key,payload)::entries)).head?
    let out := if key=query then output else Encoding.frame key ++ Encoding.frame payload ++ output
    obtain ⟨n,hn,middle,he⟩ := eraseOne_eval rr key query payload (rawEntries entries) output
    obtain ⟨m,hm,final,ht⟩ := ih out middle
    have hp := erasePeek_eval middle entries query out
    refine ⟨(n+2)+m+1,by simp only [eraseBudget]; omega,final,?_⟩
    have hh := Eval.while_true (eraseReady_cons_guard regs key payload query output entries) (he.seq hp) ht
    exact hh

theorem eraseScan_eval (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 2, ∃ final,
      Eval eraseScan n (eraseData regs (rawEntries entries) query output [])
        (eraseData final [] query (erasedOutput query entries output) []) := by
  obtain ⟨n,hn,final,he⟩ := eraseLoop_eval entries query output regs
  exact ⟨2+n,by omega,final,(erasePeek_eval regs entries query output).seq he⟩

theorem rawEntries_append (a b : List ByteRecord) :
    rawEntries (a++b) = rawEntries a ++ rawEntries b := by
  induction a with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨k,c⟩; simp [rawEntries,ih,List.append_assoc]

theorem erasedOutput_eq (query output : List Bool) (entries : List ByteRecord) :
    erasedOutput query entries output = rawEntries (erasedEntries query entries).reverse ++ output := by
  induction entries generalizing output with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨key,payload⟩
    by_cases he : key=query <;>
      simp [erasedOutput,erasedEntries,he,ih,List.reverse_cons,rawEntries_append,rawEntries,List.append_assoc]

def eraseScanProgram := compiled eraseScan 0 5

theorem eraseScan_trace (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 3, ∃ final,
      Trace eraseScanProgram n
        ((eraseData regs (rawEntries entries) query output []).withPC (some eraseScanProgram.entry))
        ((eraseData final [] query (rawEntries (erasedEntries query entries).reverse ++ output) []).withPC none) := by
  obtain ⟨n,hn,final,he⟩ := eraseScan_eval entries query output regs
  rw [erasedOutput_eq] at he
  exact ⟨n+1,by omega,final,compiled_halt_trace he 0 5⟩

theorem eraseBudget_bound (query : List Bool) (entries : List ByteRecord) (W B : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    eraseBudget query entries ≤ entries.length * (28*W+9*query.length+13*B+53)+1 := by
  induction entries with
  | nil => simp [eraseBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [eraseBudget,List.length_cons] at *
    nlinarith
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
