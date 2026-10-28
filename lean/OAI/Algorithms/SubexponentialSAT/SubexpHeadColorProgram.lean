import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

namespace OAI.Algorithms

/-!
# Read a head color from its physical one-hot type encoding

Ports 0, 1, and 2 hold the flat type bytes, unary position, and unary color
width. The fixed array reader preserves these inputs. A five-label bit loop
counts the false prefix of the selected one-hot word; the remaining suffix is
cleared. Only output port 3 changes, and scratch ports 4--9 are restored.
-/

namespace SubexponentialSAT.SubexpHeadColorProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.AssignmentAlphabetSemantics

abbrev Data := State 5 10
abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false

namespace Prefix

/-- Each false bit emits one true counter bit; the first true bit terminates. -/
abbrev program : Program 2 2 5 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 0 4 2, .set 0 true 3, .push 1 0 0, .halt]

abbrev cfg := ParserProgram.cfg (l := 5)

theorem cycle (v p : Bool) (input output : List Bool) :
    Trace program 4 (cfg (some 0) v p (false :: input) output)
      (cfg (some 0) true true input (true :: output)) := by
  refine .cons (b := cfg (some 1) false true input output) ?_ ?_
  · simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr,readRegs]
  · refine .cons (b := cfg (some 2) false true input output) ?_ ?_
    · simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr]
    · refine .cons (b := cfg (some 3) true true input output) ?_ ?_
      · simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr]
      · refine .cons (b := cfg (some 0) true true input (true :: output)) ?_ (.refl _)
        simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr]

theorem finish (v p : Bool) (input output : List Bool) :
    Trace program 3 (cfg (some 0) v p (true :: input) output)
      (cfg none true true input output) := by
  refine .cons (b := cfg (some 1) true true input output) ?_ ?_
  · simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr,readRegs]
  · refine .cons (b := cfg (some 4) true true input output) ?_ ?_
    · simp [step,ParserProgram.cfg,ParserProgram.pair,execInstr]
    · refine .cons (b := cfg none true true input output) ?_ (.refl _)
      simp [step,ParserProgram.cfg,execInstr]

theorem trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace program (4*n+3)
      (cfg (some 0) v p (zeros n ++ true :: rest) output)
      (cfg none true true rest (unary n ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa using finish v p rest output
  | succ n ih =>
      have h := (cycle v p (zeros n ++ true :: rest) output).trans
        (ih (true :: output) true true)
      have hn : 4+(4*n+3) = 4*(n+1)+3 := by omega
      have hin : zeros (n+1) ++ true :: rest = false :: (zeros n ++ true :: rest) := by
        simp [zeros,List.replicate_succ]
      have hout : unary (n+1) ++ output = unary n ++ true :: output := by
        simp [unary,List.replicate_succ',List.append_assoc]
      simpa only [hn,hin,hout] using h

end Prefix

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([3,4,5,6,7,8,9] : List (Fin 10)), d.stacks i = []

def result (d : Data) (g : ℕ) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 3 (unary g)⟩

def readPorts : Fin 8 → Fin 10 := ![0,5,4,2,6,7,8,9]

theorem readPorts_injective : Function.Injective readPorts := by decide

abbrev copyIndex : Cmd 5 10 := .call (StackRoutines.copyProgram 1 4 6 (0 : Fin 5) 1)

abbrev readCell : Cmd 5 10 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 5) 1)
    id readPorts)

abbrev select : Cmd 5 10 := .seq copyIndex readCell

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 5 word⟩

theorem select_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hsource : d.stacks 0 = earlier.flatten ++ (word ++ rest))
    (hindex : (d.stacks 1).length = earlier.length)
    (hwidth : word.length = (d.stacks 2).length)
    (hrows : ∀ row ∈ earlier, row.length = (d.stacks 2).length) (hclean : Clean d) :
    Eval select
      (earlier.length * (14*(d.stacks 2).length+17) + 15*(d.stacks 2).length+21)
      d (selected d word) := by
  have h4 := hclean 4 (by simp)
  have h5 := hclean 5 (by simp)
  have h6 := hclean 6 (by simp)
  have h7 := hclean 7 (by simp)
  have h8 := hclean 8 (by simp)
  have h9 := hclean 9 (by simp)
  let b := afterCopy d 1 4 0 1
  have hc := copy_eval d 1 4 6 0 1 (by decide) (by decide) (by decide) (by decide) h6
  let a := projectState id readPorts b
  have hs : a.stacks 0 = earlier.flatten ++ (word ++ rest) := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using hsource
  have hw : a.stacks 3 = d.stacks 2 := by rfl
  have hi : a.stacks 2 = d.stacks 1 := by
    simp [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks,h4]
  have hca : a.stacks 4 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h6
  have hta : a.stacks 5 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h7
  have hba : a.stacks 6 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h8
  have hpa : a.stacks 7 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h9
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 5) 1 (by decide)
    earlier word rest (d.stacks 2) (d.stacks 1) a.regs a.stacks
    hs hw hi hindex hrows hwidth hca hta hba hpa
  let z : State 5 8 :=
    ⟨readRegs a.regs 0 1 none,ArrayUpdatePrograms.readStacks word a.stacks⟩
  have hr := eval_call_from_state (ArrayUpdatePrograms.readProgram (0 : Fin 5) 1)
    id readPorts b Function.injective_id readPorts_injective (b := z) ht
  have hz : embedState id readPorts b z = selected d word := by
    apply embedState_eq_of_ports id readPorts b (selected d word) z
      Function.injective_id readPorts_injective
    · intro i
      simp [selected,z,a,b,projectState,afterCopy,StackRoutines.readRegs_reset]
    · intro i hi
      exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;>
        simp [selected,z,a,b,projectState,afterCopy,StackRoutines.copyStacks,
          ArrayUpdatePrograms.readStacks,readPorts,h4,h5]
    · intro i hi
      have h4' : i ≠ 4 := fun h => hi ⟨2,by simpa [readPorts] using h.symm⟩
      have h5' : i ≠ 5 := fun h => hi ⟨1,by simpa [readPorts] using h.symm⟩
      simp [selected,b,afterCopy,StackRoutines.copyStacks,h4',h5']
  rw [hz] at hr
  have he := hc.seq hr
  have hn : (7*(d.stacks 1).length+5)+
      (earlier.length*(14*(d.stacks 2).length+10)+15*(d.stacks 2).length+16) =
      earlier.length*(14*(d.stacks 2).length+17)+15*(d.stacks 2).length+21 := by
    rw [hindex]
    ring
  simpa only [select,copyIndex,readCell,hn] using he

def countRegs : Fin 2 → Fin 5 := Fin.castAdd 3
def countPorts : Fin 2 → Fin 10 := ![5,3]

theorem countRegs_injective : Function.Injective countRegs := Fin.castAdd_injective _ _
theorem countPorts_injective : Function.Injective countPorts := by decide

abbrev countPrefix : Cmd 5 10 :=
  .call (ProgramLinking.liftProgram Prefix.program countRegs countPorts)

def counted (d : Data) (g : ℕ) (rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some true),
    Function.update (Function.update d.stacks 5 rest) 3 (unary g ++ d.stacks 3)⟩

theorem countPrefix_eval (d : Data) (g : ℕ) (rest : List Bool)
    (hsource : d.stacks 5 = zeros g ++ true :: rest) :
    Eval countPrefix (4*g+3) d (counted d g rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (zeros g ++ true :: rest) (d.stacks 3)⟩
  let b : State 2 2 := ⟨ParserProgram.pair true true,
    ParserProgram.pair rest (unary g ++ d.stacks 3)⟩
  have ha : embedState countRegs countPorts d a = d := by
    apply embedState_eq_of_ports countRegs countPorts d d a
      countRegs_injective countPorts_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hsource
      · rfl
    · intros; rfl
  have hb : embedState countRegs countPorts d b = counted d g rest := by
    apply embedState_eq_of_ports countRegs countPorts d (counted d g rest) b
      countRegs_injective countPorts_injective
    · intro i; fin_cases i <;> simp [counted,b,countRegs,readRegs,ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [countRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [countRegs] using h.symm⟩
      simp [counted,readRegs,h0,h1]
    · intro i; fin_cases i <;> simp [counted,b,countPorts,ParserProgram.pair]
    · intro i hi
      have h5 : i ≠ 5 := fun h => hi ⟨0,by simpa [countPorts] using h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨1,by simpa [countPorts] using h.symm⟩
      simp [counted,h5,h3]
  have ht := Prefix.trace g rest (d.stacks 3) (d.regs 0) (d.regs 1)
  have he := eval_call_lifted Prefix.program countRegs countPorts d
    countRegs_injective countPorts_injective (a := a) (b := b) ht
  simpa only [ha,hb,countPrefix] using he

abbrev clearRest : Cmd 5 10 := .call (StackRoutines.clearProgram 5 (0 : Fin 5) 1)

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 5 []⟩

theorem clearRest_eval (d : Data) :
    Eval clearRest (2*(d.stacks 5).length+3) d (cleared d) := by
  apply Eval.call
  have ht := StackRoutines.clearProgram_trace (5 : Fin 10) (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

abbrev command : Cmd 5 10 := .seq select (.seq countPrefix clearRest)

def budget (t r : ℕ) : ℕ := t*(14*r+17)+21*r+30

/-- A generic valid one-hot cell is decoded by the actual selected-bit loop. -/
theorem command_eval_oneHot {r : ℕ} (d : Data) (earlier : List (List Bool))
    (g : Fin r) (rest : List Bool)
    (hsource : d.stacks 0 = earlier.flatten ++ (oneHot g ++ rest))
    (hindex : (d.stacks 1).length = earlier.length)
    (hwidth : (d.stacks 2).length = r)
    (hrows : ∀ row ∈ earlier, row.length = r) (hclean : Clean d) :
    ∃ n ≤ budget earlier.length r, Eval command n d (result d g.val) := by
  have h3 := hclean 3 (by simp)
  have h5 := hclean 5 (by simp)
  have hs := select_eval d earlier (oneHot g) rest hsource hindex
    (by simp [oneHot,hwidth]) (by simpa only [hwidth] using hrows) hclean
  rw [hwidth] at hs
  let a := selected d (oneHot g)
  let tail := zeros (r-g.val-1)
  have ha : a.stacks 5 = zeros g.val ++ true :: tail := by
    simpa [a,selected,tail,hotAt] using oneHot_eq g
  have hc := countPrefix_eval a g.val tail ha
  let b := counted a g.val tail
  have hz := clearRest_eval b
  have hzLen : (b.stacks 5).length = r-g.val-1 := by
    simp [b,counted,tail]
  have hzEnd : cleared b = result d g.val := by
    apply state_ext
    · simp [cleared,b,counted,a,selected,result,StackRoutines.readRegs_reset]
    · funext i
      by_cases h : i = 3
      · subst i; simp [cleared,b,counted,a,selected,result,h3]
      · by_cases h' : i = 5
        · subst i; simp [cleared,b,counted,a,selected,result,h5]
        · simp [cleared,b,counted,a,selected,result,h,h']
  rw [hzLen,hzEnd] at hz
  refine ⟨(earlier.length*(14*r+17)+15*r+21)+((4*g.val+3)+(2*(r-g.val-1)+3)),?_,
    hs.seq (hc.seq hz)⟩
  unfold budget
  have hg := g.isLt
  omega

/-- Decompose the serialized type at the requested head-position cell. -/
theorem encodeType_head_split {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) :
    ∃ (earlier : List (List Bool)) (rest : List Bool), earlier.length = t.val ∧
      (∀ row ∈ earlier, row.length = r) ∧
      Subexp.CollisionProgram.encodeType u =
        earlier.flatten ++ (oneHot (u.head t) ++ rest) := by
  let rows := List.ofFn (fun q : Fin Q => oneHot (u.head q))
  let tail := (List.ofFn (fun i : Fin Δ =>
    Subexp.ReadPlan.encodeWord (u.slot i))).flatten
  have htype : Subexp.CollisionProgram.encodeType u = rows.flatten ++ tail := by
    rw [Subexp.ReadPlan.encodeType_eq_words,List.ofFn_succ,List.flatten_cons]
    rfl
  have ht : t.val < rows.length := by simp [rows]
  have he := List.take_append_drop t.val rows
  rw [List.drop_eq_getElem_cons ht] at he
  have hcell : rows[t.val] = oneHot (u.head t) := by simp [rows]
  rw [hcell] at he
  refine ⟨rows.take t.val,(rows.drop (t.val+1)).flatten ++ tail,?_,?_,?_⟩
  · simp [List.length_take,rows]
  · intro row hr
    have hm : row ∈ rows := List.mem_of_mem_take hr
    obtain ⟨q,hq⟩ := List.mem_ofFn.mp hm
    rw [← hq]
    simp [oneHot]
  · calc
      Subexp.CollisionProgram.encodeType u = rows.flatten ++ tail := htype
      _ = (rows.take t.val ++ oneHot (u.head t) :: rows.drop (t.val+1)).flatten ++ tail :=
        congrArg (fun xs : List (List Bool) => xs.flatten ++ tail) he.symm
      _ = _ := by simp [List.flatten_append,List.flatten_cons,List.append_assoc]

/-- The typed endpoint obtains the head color from encoded input bytes. -/
theorem command_eval {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) (d : Data)
    (hsource : d.stacks 0 = Subexp.CollisionProgram.encodeType u)
    (hindex : d.stacks 1 = unary t.val) (hwidth : d.stacks 2 = unary r)
    (hclean : Clean d) :
    ∃ n ≤ budget t.val r, Eval command n d (result d (u.head t).val) := by
  obtain ⟨earlier,rest,hlen,hrows,hsplit⟩ := encodeType_head_split u t
  have h := command_eval_oneHot d earlier (u.head t) rest (hsource.trans hsplit)
    (by simpa only [hindex,List.length_replicate] using hlen.symm)
    (by simp [hwidth]) hrows hclean
  simpa only [hlen] using h

abbrev program : Program 5 10 (size command+1) := compiled command 0 3

theorem program_run {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) (d : Data)
    (hsource : d.stacks 0 = Subexp.CollisionProgram.encodeType u)
    (hindex : d.stacks 1 = unary t.val) (hwidth : d.stacks 2 = unary r)
    (hclean : Clean d) :
    RunsIn program (budget t.val r+1)
      (d.withPC (some program.entry)) ((result d (u.head t).val).withPC none) := by
  obtain ⟨n,hn,he⟩ := command_eval u t d hsource hindex hwidth hclean
  exact ⟨n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 0 3⟩

theorem result_frame (d : Data) (g : ℕ) (i : Fin 10) (hi : i ≠ 3) :
    (result d g).stacks i = d.stacks i := by simp [result,hi]

theorem budget_polynomial (t r L : ℕ) :
    budget t r + 1 ≤ 100*(L+t+r+1)^2 := by
  let S := L+t+r+1
  have ht : t ≤ S := by dsimp [S]; omega
  have hr : r ≤ S := by dsimp [S]; omega
  have h1 : 1 ≤ S := by dsimp [S]; omega
  have hS : S ≤ S^2 := by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left S h1
  have htr : t*r ≤ S^2 := by simpa only [pow_two] using Nat.mul_le_mul ht hr
  have ht' := ht.trans hS
  have hr' := hr.trans hS
  have h1' := h1.trans hS
  change budget t r + 1 ≤ 100*S^2
  unfold budget
  nlinarith only [htr,ht',hr',h1']

/-- A uniform polynomial in the lengths of the three actual input words. -/
theorem program_run_raw_lengths {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) (d : Data)
    (hsource : d.stacks 0 = Subexp.CollisionProgram.encodeType u)
    (hindex : d.stacks 1 = unary t.val) (hwidth : d.stacks 2 = unary r)
    (hclean : Clean d) :
    RunsIn program
      (100*((d.stacks 0).length+(d.stacks 1).length+(d.stacks 2).length+1)^2)
      (d.withPC (some program.entry)) ((result d (u.head t).val).withPC none) := by
  obtain ⟨n,hn,he⟩ := program_run u t d hsource hindex hwidth hclean
  refine ⟨n,hn.trans ?_,he⟩
  simpa only [hindex,hwidth,List.length_replicate] using
    budget_polynomial t.val r (d.stacks 0).length

end SubexponentialSAT.SubexpHeadColorProgram

end OAI.Algorithms
