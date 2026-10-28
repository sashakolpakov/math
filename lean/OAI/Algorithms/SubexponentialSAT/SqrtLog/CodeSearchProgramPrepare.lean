import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames

namespace OAI.Algorithms

/-! Fixed physical input preparation for the local-code word checker. The
matrix, row count, and threshold are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev SearchState := State 16 24

def wordRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def wordStacks : Fin 18 → Fin 24 := Fin.castAdd 6

def workPorts : List (Fin 24) := List.ofFn wordStacks

def inputMoves : List (Fin 24 × Fin 24) := [(18,11),(19,15),(20,16)]

abbrev inputCopies : Cmd 16 24 := copyMany 23 inputMoves

abbrev literalCommand : Cmd 16 24 :=
  .seq (.base (.atom (.set 0 false))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.set 0 true))) <|
  .seq (.base (.atom (.push 5 0))) (.base (.atom (.push 5 0)))

def literalState (a : SearchState) : SearchState :=
  (Atom.push 5 0).eval ((Atom.push 5 0).eval ((Atom.set 0 true).eval
    ((Atom.push 14 0).eval ((Atom.push 14 0).eval ((Atom.push 5 0).eval
      ((Atom.set 0 false).eval a))))))

theorem literalCommand_eval (a : SearchState) :
    Eval literalCommand 7 a (literalState a) := by
  exact (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

abbrev prepareWordCommand : Cmd 16 24 :=
  .seq inputCopies (.seq (.call (StackRoutines.transferProgram 22 12 0 1)) literalCommand)

def preparedWord (a : SearchState) : SearchState :=
  literalState (SubexpScanPrimitives.afterTransfer (copyManyState inputMoves a) 22 12 0 1)

def prepareWordCost (a : SearchState) : ℕ :=
  7 * ((a.stacks 18).length + (a.stacks 19).length + (a.stacks 20).length) +
    3 * (a.stacks 22).length + 25

theorem prepareWord_eval (a : SearchState) (ht : a.stacks 23 = []) :
    Eval prepareWordCommand (prepareWordCost a) a (preparedWord a) := by
  have hp : ∀ p ∈ inputMoves, p.1 ≠ p.2 ∧ p.1 ≠ (23 : Fin 24) ∧ 23 ≠ p.2 := by
    intro p hp
    simp only [inputMoves, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  have hc := copyMany_eval 23 inputMoves a hp ht
  have hx := SubexpScanPrimitives.transfer_eval (copyManyState inputMoves a)
    22 12 0 1 (by decide) (by decide)
  have hl := literalCommand_eval (SubexpScanPrimitives.afterTransfer
    (copyManyState inputMoves a) 22 12 0 1)
  have h := hc.seq (hx.seq hl)
  convert h using 1 <;> simp [ preparedWord, prepareWordCost,
    inputMoves, copyManyCost, copyManyState, copyState, StackRoutines.copyStacks,
    Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

def WorkEmpty (a : SearchState) : Prop := ∀ i : Fin 18, a.stacks (wordStacks i) = []

theorem workPorts_mem (i : Fin 24) : i ∈ workPorts ↔ i.val < 18 := by
  simp only [workPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro h; exact ⟨⟨i.val,h⟩, Fin.ext rfl⟩

theorem preparedWord_frame (a : SearchState) (i : Fin 24)
    (hi : 18 ≤ i.val) (hp : i ≠ 22) : (preparedWord a).stacks i = a.stacks i := by
  have h11 : i ≠ 11 := by intro h; subst i; omega
  have h12 : i ≠ 12 := by intro h; subst i; omega
  have h15 : i ≠ 15 := by intro h; subst i; omega
  have h16 : i ≠ 16 := by intro h; subst i; omega
  have h5 : i ≠ 5 := by intro h; subst i; omega
  have h14 : i ≠ 14 := by intro h; subst i; omega
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    h11,h12,h15,h16,h5,h14,hp]

theorem preparedWord_payload (a : SearchState) : (preparedWord a).stacks 22 = [] := by
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg ]

theorem preparedWord_project {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
    project wordRegisters wordStacks (preparedWord a) =
      extendMatrixState (matrixInput Q x ((preparedWord a).regs ∘ wordRegisters)) d [] := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    have hei := he i
    have he5 := he 5
    have he11 := he 11
    have he12 := he 12
    have he14 := he 14
    have he15 := he 15
    have he16 := he 16
    have hv0 : (0 : Fin 18).val = 0 := rfl
    have hv1 : (1 : Fin 18).val = 1 := rfl
    have hv2 : (2 : Fin 18).val = 2 := rfl
    have hv3 : (3 : Fin 18).val = 3 := rfl
    have hv4 : (4 : Fin 18).val = 4 := rfl
    have hv5 : (5 : Fin 18).val = 5 := rfl
    have hv6 : (6 : Fin 18).val = 6 := rfl
    have hv7 : (7 : Fin 18).val = 7 := rfl
    have hv8 : (8 : Fin 18).val = 8 := rfl
    have hv9 : (9 : Fin 18).val = 9 := rfl
    have hv10 : (10 : Fin 18).val = 10 := rfl
    have hv11 : (11 : Fin 18).val = 11 := rfl
    have hv12 : (12 : Fin 18).val = 12 := rfl
    have hv13 : (13 : Fin 18).val = 13 := rfl
    have hv14 : (14 : Fin 18).val = 14 := rfl
    have hv15 : (15 : Fin 18).val = 15 := rfl
    have hv16 : (16 : Fin 18).val = 16 := rfl
    have hv17 : (17 : Fin 18).val = 17 := rfl
    fin_cases i <;>
      simp_all [project, wordStacks, extendMatrixState, matrixInput,
        Subexp.MatrixScalarProgram.state, Subexp.MatrixScalarProgram.scalarStacks, preparedWord, literalState, inputMoves,
        copyManyState, copyState, SubexpScanPrimitives.afterTransfer,
        StackRoutines.transferStacks, StackRoutines.copyStacks,
        Atom.eval, Atom.instr, execInstr, StructuredProgram.State.ofCfg, modulus_three, zero_three]


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
