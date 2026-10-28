import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphWord
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames

namespace OAI.Algorithms

/-! Fixed physical input preparation for the Walsh character checker. The
matrix, row count, and two binary scalar words are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev GraphSearchState := State 16 36

def graphWorkRegisters : Fin 16 → Fin 16 := id
def graphWordStacks : Fin 29 → Fin 36 := Fin.castAdd 7

def graphWorkPorts : List (Fin 36) := List.ofFn graphWordStacks

def graphInputMoves : List (Fin 36 × Fin 36) := [(29,11),(30,15),(31,16),(32,17)]

abbrev graphInputCopies : Cmd 16 36 := copyMany 35 graphInputMoves

abbrev graphLiteralCommand : Cmd 16 36 :=
  .seq (.base (.atom (.set 0 false))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.set 0 true))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 5 0)))

def graphLiteralState (a : GraphSearchState) : GraphSearchState :=
  (Atom.push 5 0).eval ((Atom.set 0 false).eval ((Atom.push 5 0).eval ((Atom.set 0 true).eval
    ((Atom.push 14 0).eval ((Atom.push 14 0).eval ((Atom.push 5 0).eval
      ((Atom.set 0 false).eval a)))))))

theorem graphLiteralCommand_eval (a : GraphSearchState) :
    Eval graphLiteralCommand 8 a (graphLiteralState a) := by
  exact (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

abbrev prepareGraphWordCommand : Cmd 16 36 :=
  .seq graphInputCopies (.seq (.call (StackRoutines.transferProgram 34 12 0 1)) graphLiteralCommand)

def preparedGraphWord (a : GraphSearchState) : GraphSearchState :=
  graphLiteralState (SubexpScanPrimitives.afterTransfer (copyManyState graphInputMoves a) 34 12 0 1)

def prepareGraphWordCost (a : GraphSearchState) : ℕ :=
  7 * ((a.stacks 29).length + (a.stacks 30).length + (a.stacks 31).length + (a.stacks 32).length) +
    3 * (a.stacks 34).length + 31

theorem prepareGraphWord_eval (a : GraphSearchState) (ht : a.stacks 35 = []) :
    Eval prepareGraphWordCommand (prepareGraphWordCost a) a (preparedGraphWord a) := by
  have hp : ∀ p ∈ graphInputMoves, p.1 ≠ p.2 ∧ p.1 ≠ (35 : Fin 36) ∧ 35 ≠ p.2 := by
    intro p hp
    simp only [graphInputMoves, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hc := copyMany_eval 35 graphInputMoves a hp ht
  have hx := SubexpScanPrimitives.transfer_eval (copyManyState graphInputMoves a)
    34 12 0 1 (by decide) (by decide)
  have hl := graphLiteralCommand_eval (SubexpScanPrimitives.afterTransfer
    (copyManyState graphInputMoves a) 34 12 0 1)
  have h := hc.seq (hx.seq hl)
  convert h using 1 <;> simp [ preparedGraphWord, prepareGraphWordCost,
    graphInputMoves, copyManyCost, copyManyState, copyState, StackRoutines.copyStacks,
    Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

def GraphWorkEmpty (a : GraphSearchState) : Prop := ∀ i : Fin 29, a.stacks (graphWordStacks i) = []

theorem graphWorkPorts_mem (i : Fin 36) : i ∈ graphWorkPorts ↔ i.val < 29 := by
  simp only [graphWorkPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro h; exact ⟨⟨i.val,h⟩, Fin.ext rfl⟩

theorem preparedGraphWord_frame (a : GraphSearchState) (i : Fin 36)
    (hi : 29 ≤ i.val) (hp : i ≠ 34) : (preparedGraphWord a).stacks i = a.stacks i := by
  have h11 : i ≠ 11 := by intro h; subst i; omega
  have h12 : i ≠ 12 := by intro h; subst i; omega
  have h15 : i ≠ 15 := by intro h; subst i; omega
  have h16 : i ≠ 16 := by intro h; subst i; omega
  have h17 : i ≠ 17 := by intro h; subst i; omega
  have h5 : i ≠ 5 := by intro h; subst i; omega
  have h14 : i ≠ 14 := by intro h; subst i; omega
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    h11,h12,h15,h16,h17,h5,h14,hp]

theorem preparedGraphWord_payload (a : GraphSearchState) : (preparedGraphWord a).stacks 34 = [] := by
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg]

theorem modulus_two : Subexp.MatrixWordEncoding.modulus 2 = [false,true,false] := by
  norm_num [Subexp.MatrixWordEncoding.modulus,Subexp.MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth,SubexpLiftRing.fixedBits]

theorem zero_two : Subexp.MatrixWordEncoding.zero 2 = [false,false] := by
  norm_num [Subexp.MatrixWordEncoding.zero,Subexp.MatrixWordEncoding.word,Subexp.MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth,SubexpLiftRing.fixedBits]

theorem preparedGraphWord_project {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState) (he : GraphWorkEmpty a)
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
    projectState graphCountRegisters graphCountStacks
      (projectState id graphWordStacks (preparedGraphWord a)) =
      extendPairState (matrixInput s x ((preparedGraphWord a).regs ∘ graphCountRegisters)) qbits Dbits := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    have hei := he ⟨i.val,by omega⟩
    have he5 := he 5
    have he11 := he 11
    have he12 := he 12
    have he14 := he 14
    have he15 := he 15
    have he16 := he 16
    have he17 := he 17
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
      simp_all [projectState,graphCountStacks,graphWordStacks,extendPairState,matrixInput,
        Subexp.MatrixScalarProgram.state,Subexp.MatrixScalarProgram.scalarStacks,
        preparedGraphWord,graphLiteralState,graphInputMoves,
        copyManyState,copyState,SubexpScanPrimitives.afterTransfer,
        StackRoutines.transferStacks,StackRoutines.copyStacks,
        Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,
modulus_two,zero_two]

theorem preparedGraphWord_scratch (a : GraphSearchState) (he : GraphWorkEmpty a)
    (i : Fin 29) (hi : 18 ≤ i.val) :
    (projectState id graphWordStacks (preparedGraphWord a)).stacks i = [] := by
  have h5 : graphWordStacks i ≠ 5 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h11 : graphWordStacks i ≠ 11 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h12 : graphWordStacks i ≠ 12 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h14 : graphWordStacks i ≠ 14 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h15 : graphWordStacks i ≠ 15 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h16 : graphWordStacks i ≠ 16 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h17 : graphWordStacks i ≠ 17 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h34 : graphWordStacks i ≠ 34 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  simpa [projectState,preparedGraphWord,graphLiteralState,graphInputMoves,
    copyManyState,copyState,SubexpScanPrimitives.afterTransfer,
    StackRoutines.transferStacks,StackRoutines.copyStacks,Atom.eval,Atom.instr,
    execInstr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    h5,h11,h12,h14,h15,h16,h17,h34] using he i

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
