import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO
import OAI.Algorithms.SubexponentialSAT.SubexpExponentProgram
import OAI.Algorithms.SubexponentialSAT.SubexpDenseKeyProgram
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatFrame
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProjection
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRecordCalls
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticDenseCall

namespace OAI.Algorithms

/-! Concrete nested pair-loop table for dense multiplication. Its arithmetic
calls are the published finite key-adder and flat quartic multiplier. -/

namespace SubexponentialSAT.SubexpDenseProgram.Product

open BitProgram StructuredCalls

def lowFive : Fin 5 → Fin 16 := Fin.castAdd 11
def lowEight : Fin 8 → Fin 16 := Fin.castAdd 8
def lowTwo : Fin 2 → Fin 16 := Fin.castAdd 14

def leftParserPorts : Fin 6 → Fin 128 := ![16, 93, 94, 18, 19, 25]
def rightParserPorts : Fin 6 → Fin 128 := ![17, 95, 96, 18, 19, 25]
def emitterPorts : Fin 6 → Fin 128 := ![13, 16, 25, 99, 18, 19]
def keyPorts : Fin 4 → Fin 128 := ![0, 1, 2, 16]

def mulPorts : Fin 77 → Fin 128 :=
  SubexpQuarticFlatLift.densePorts

abbrev copy (src dst : Fin 128) : Cmd 16 128 :=
  .call (StackRoutines.copyProgram src dst 24 0 1)

abbrev clear (src : Fin 128) : Cmd 16 128 :=
  .call (StackRoutines.clearProgram src 0 1)

abbrev parseLeft : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram RawParser.unpackProgram lowFive leftParserPorts)

abbrev parseRight : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram RawParser.unpackProgram lowFive rightParserPorts)

abbrev keyCall : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram SubexpExponentProgram.keyAddProgram lowTwo keyPorts)

/-- Preserve both key masters and the width master, and clear any padding
tails that the width-bounded adder leaves in its two working inputs. -/
abbrev addKeys : Cmd 16 128 :=
  SubexpDenseKeyProgram.addKeys

abbrev mulCall : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram SubexpQuarticFlatMul.program lowEight mulPorts)

abbrev multiplyMasters : Cmd 16 128 := SubexpQuarticDenseCall.command

abbrev emit : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram RawEmitter.emitRawTermProgram lowFive emitterPorts)

abbrev resetOuter : Cmd 16 128 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 7 false))))

abbrev resetInner : Cmd 16 128 :=
  .seq (.base (.atom (.set 8 false)))
    (.seq (.base (.atom (.set 9 true))) (.base (.atom (.set 15 false))))

def innerPorts : RecordPrograms.Ports 16 128 where
  tag := 8
  present := 9
  found := 15
  source := 97
  payload := 17
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def outerPorts : RecordPrograms.Ports 16 128 where
  tag := 0
  present := 1
  found := 7
  source := 98
  payload := 16
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- One actual product pair: parse the right record, add its key, execute all
49 base multiplications/additions in the quartic service, and emit the term. -/
abbrev pairCallback : Cmd 16 128 :=
  .seq parseRight (.seq addKeys (.seq multiplyMasters
    (.seq emit (.seq (clear 95) (.seq (clear 96) resetInner)))))

abbrev inner : Cmd 16 128 := RecordPrograms.iterate innerPorts pairCallback

/-- For each left term, consume a preserving copy of the entire right list. -/
abbrev rowCallback : Cmd 16 128 :=
  .seq parseLeft (.seq (copy 23 97) (.seq inner
    (.seq (clear 93) (.seq (clear 94) resetOuter))))

abbrev outer : Cmd 16 128 := RecordPrograms.iterate outerPorts rowCallback

abbrev command : Cmd 16 128 := .seq (copy 22 98) outer
def program := StructuredCalls.compiled command 22 99

/-- Projection reads the generated pair list at 99, while the original left
operand at 22 remains outside its assigned port set. -/
def projectionPorts (i : Fin 26) : Fin 128 :=
  if i = 22 then 99 else ⟨i.val, by omega⟩

theorem projectionPorts_injective : Function.Injective projectionPorts := by decide

abbrev projectPairs : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram Projection.projectProgram lowEight projectionPorts)

abbrev initializePairs : Cmd 16 128 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 99 0)))

/-- The physical arithmetic core leaves the two operand masters unchanged.
The final clear restores the only remaining pair-list work stack. -/
abbrev mulCore : Cmd 16 128 :=
  .seq initializePairs (.seq command (.seq projectPairs (clear 99)))

def mulCoreProgram := StructuredCalls.compiled mulCore 22 21

abbrev Data := State 16 128

def leftEmbedding : Fin 6 ↪ Fin 128 := ⟨leftParserPorts, by decide⟩
def rightEmbedding : Fin 6 ↪ Fin 128 := ⟨rightParserPorts, by decide⟩
def emitEmbedding : Fin 6 ↪ Fin 128 := ⟨emitterPorts, by decide⟩

theorem parseRight_eval (d : Data) (key coefficient : List Bool)
    (hin : d.stacks 17 = (SubexpArgumentProgram.recordBody key coefficient).reverse)
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) :
    ∃ e : Data, Eval parseRight (15*key.length+15*coefficient.length+24) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 17 [])
        95 key) 96 coefficient := by
  exact SubexpDenseRecordCalls.parse_eval rightEmbedding d key coefficient hin h95 h96 h18 h19

theorem parseLeft_eval (d : Data) (key coefficient : List Bool)
    (hin : d.stacks 16 = (SubexpArgumentProgram.recordBody key coefficient).reverse)
    (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) :
    ∃ e : Data, Eval parseLeft (15*key.length+15*coefficient.length+24) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 16 [])
        93 key) 94 coefficient := by
  exact SubexpDenseRecordCalls.parse_eval leftEmbedding d key coefficient hin h93 h94 h18 h19

theorem emit_eval (d : Data) (key coefficient : List Bool)
    (hin : d.stacks 13 = coefficient) (hkey : d.stacks 16 = key.reverse)
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) :
    ∃ e : Data, Eval emit (37*coefficient.length+21*key.length+57) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 13 []) 16 [])
        99 (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++
          d.stacks 99)) := by
  exact SubexpDenseRecordCalls.emit_eval emitEmbedding d key coefficient hin hkey h18 h19

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 8 false) 9 true) 15 false, d.stacks⟩

theorem resetInner_eval (d : Data) : Eval resetInner 3 d (resetState d) := by
  let a : StructuredProgram.Atom 16 128 := .set 8 false
  let b : StructuredProgram.Atom 16 128 := .set 9 true
  let c : StructuredProgram.Atom 16 128 := .set 15 false
  have ha := Eval.base (StructuredProgram.Eval.atom a d)
  have hb := Eval.base (StructuredProgram.Eval.atom b (a.eval d))
  have hc := Eval.base (StructuredProgram.Eval.atom c (b.eval (a.eval d)))
  simpa [resetInner, resetState, a, b, c, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using ha.seq (hb.seq hc)

theorem mulPort_range : ∀ i : Fin 77,
    (SubexpQuarticFlatLift.densePorts i).val ≤ 15 ∨
      (30 ≤ (SubexpQuarticFlatLift.densePorts i).val ∧
        (SubexpQuarticFlatLift.densePorts i).val ≤ 91) := by decide

theorem mulPort_ne (i : Fin 77) (j : Fin 128)
    (hj : (15 < j.val ∧ j.val < 30) ∨ 91 < j.val) :
    SubexpQuarticFlatLift.densePorts i ≠ j := by
  intro he
  have h := mulPort_range i
  rw [he] at h
  omega

theorem sumKey_length {D : ℕ} (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b) :
    (SubexpSymbolicCost.fixedKey (a+b)).length = SubexpSymbolicCost.indexBits D := by
  have h := SubexpSymbolicCost.retained_sum_key_length a b ha hb
  simp only [SubexpSymbolicCost.fixedKey, List.length_append, List.length_replicate]
  omega

def pairBudget (B I : ℕ) : ℕ := 400000*(B+1)^2+80*I+280*B+150

section PairExecution

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift

theorem pairCallback_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t x y : QuarticCode p D)
    (a b : RawIndex D) (ha : Retained D a) (hb : Retained D b)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hleft : d.stacks 93 = fixedKey a) (hvalue : d.stacks 94 = flat x)
    (hinput : d.stacks 17 = (SubexpArgumentProgram.recordBody (fixedKey b) (flat y)).reverse)
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h16 : d.stacks 16 = []) (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = [])
    (h24 : d.stacks 24 = []) (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) :
    ∃ n e, n ≤ pairBudget (baseWidth p (D+1)) (indexBits D) ∧
      Eval pairCallback n d e ∧
      e.stacks = Function.update (Function.update d.stacks 17 []) 99
        (true :: (Encoding.frame (SubexpArgumentProgram.recordBody (fixedKey (a+b))
          (flat (SubexpPreparedQuartic.binaryMul p (D+1) M t x y).1)) ++ d.stacks 99)) ∧
      e.regs 8 = false ∧ e.regs 9 = true ∧ e.regs 15 = false := by
  obtain ⟨d1,hparse,hs1⟩ := parseRight_eval d (fixedKey b) (flat y) hinput h95 h96 h18 h19
  have work1 : ∀ i, d1.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    rw [hs1]
    simpa only [Function.update_of_ne (mulPort_ne i 96 (by decide)),
      Function.update_of_ne (mulPort_ne i 95 (by decide)),
      Function.update_of_ne (mulPort_ne i 17 (by decide))] using hwork i
  obtain ⟨nk,d2,hk,hkey,hs2⟩ := SubexpDenseKeyProgram.fixedKey_eval d1 a b ha hb
    (by simpa [hs1] using hleft) (by simp [hs1]) (by simpa [hs1] using hkeywidth)
    (work1 61) (work1 62) (work1 63) (by simpa [hs1] using h24)
  have work2 : ∀ i, d2.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    rw [hs2]
    simpa only [Function.update_of_ne (mulPort_ne i 16 (by decide))] using work1 i
  obtain ⟨nm,rm,hm,hmul⟩ := SubexpQuarticDenseCall.command_eval p (D+1) M t x y width hw
    d2.regs d2.stacks work2 (by simpa [hs2,hs1] using hvalue)
    (by simp [hs2,hs1]) (by simpa [hs2,hs1] using h24)
  let product := (SubexpPreparedQuartic.binaryMul p (D+1) M t x y).1
  let d3 : Data := ⟨resultRegs denseRegisters rm d2.regs, Function.update d2.stacks 13 (flat product)⟩
  obtain ⟨d4,hemit,hs4⟩ := emit_eval d3 (fixedKey (a+b)) (flat product) rfl
    (by simp [d3,hs2,hs1,h16]) (by simpa [d3,hs2,hs1] using h18)
    (by simpa [d3,hs2,hs1] using h19)
  let d5 := SubexpDenseKeyProgram.cleared 95 d4
  let d6 := SubexpDenseKeyProgram.cleared 96 d5
  have hc95 := SubexpDenseKeyProgram.clear_eval 95 d4
  have hc96 := SubexpDenseKeyProgram.clear_eval 96 d5
  have hreset := resetInner_eval d6
  have htotal := hparse.seq (hkey.seq (hmul.seq (hemit.seq (hc95.seq (hc96.seq hreset)))))
  refine ⟨_, resetState d6, ?_, htotal, ?_, by simp [resetState],
    by simp [resetState], by simp [resetState]⟩
  · have hklen := fixedKey_length b hb
    have hslen := sumKey_length a b ha hb
    have hc95len : (d4.stacks 95).length = indexBits D := by
      simp [hs4,d3,hs2,hs1,hklen]
    have hc96len : (d5.stacks 96).length = 4*baseWidth p (D+1) := by
      simp [d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,flat_length]
    simp only [flat_length, hklen, hslen, hc95len, hc96len]
    unfold pairBudget
    omega
  · have h13 : d.stacks 13 = [] := hwork 72
    funext i
    by_cases h17i : i=17
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1]
    by_cases h99i : i=99
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,product]
    by_cases h13i : i=13
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,h13]
    by_cases h16i : i=16
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,h16]
    by_cases h95i : i=95
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,h95]
    by_cases h96i : i=96
    · subst i; simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,h96]
    simp [resetState,d6,d5,SubexpDenseKeyProgram.cleared,hs4,d3,hs2,hs1,
      h17i,h99i,h13i,h16i,h95i,h96i]

end PairExecution

section EncodedTerms

open SymbolicCost SubexpSymbolicCost SubexpQuarticRing SubexpQuarticFlatMul

def encodeTerm {p D : ℕ} (q : RawIndex D × QuarticCode p D) : List Bool :=
  SubexpArgumentProgram.recordBody (fixedKey q.1) (flat q.2)

theorem flat_eq_block (p D : ℕ) (q : QuarticCode p D) :
    flat q = (quarticCodeBlockCode p D).block q := by
  simp [flat, wordLists, FourWordPrograms.flatWords, Quad.toFn,
    quarticCodeBlockCode, wordBlockCode, recordBlockCode, quadToPair, List.append_assoc]

theorem encodeTerm_injective (p D : ℕ) :
    Function.Injective (@encodeTerm p D) := by
  intro a b h
  have hp : (fixedKey a.1, flat a.2) = (fixedKey b.1, flat b.2) :=
    framedRecord_injective h
  apply Prod.ext
  · exact fixedKey_injective (congrArg Prod.fst hp)
  · apply (quarticCodeBlockCode p D).injective_block
    simpa only [flat_eq_block] using congrArg Prod.snd hp

def pairValue (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a b : RawIndex D × QuarticCode p D) : RawIndex D × QuarticCode p D :=
  (a.1+b.1, (SubexpPreparedQuartic.binaryMul p (D+1) M t a.2 b.2).1)

/-- A proof-only extension of the effect to malformed record bytes. The
machine never evaluates this function: its code is the concrete callback.
The typed iterator uses it only to record the output of actual valid calls. -/
noncomputable def pairRecordEffect (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a : RawIndex D × QuarticCode p D) : List Bool → List Bool :=
  Function.extend encodeTerm (fun b => encodeTerm (pairValue p D M t a b)) (fun _ => [])

theorem pairRecordEffect_apply (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a b : RawIndex D × QuarticCode p D) :
    pairRecordEffect p D M t a (encodeTerm b) = encodeTerm (pairValue p D M t a b) :=
  (encodeTerm_injective p D).extend_apply _ _ _

def validTerm (p D : ℕ) (bits : List Bool) : Prop :=
  ∃ q : RawIndex D × QuarticCode p D, Retained D q.1 ∧ encodeTerm q = bits

end EncodedTerms

section InnerExecution

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift

/-- The iterator may change its cursor, its parsed payload, and the output.
Every other stack is framed, including the outer iterator's cursor. -/
def innerFrame (initial current : Data) : Prop :=
  ∀ i, i ≠ 97 → i ≠ 17 → i ≠ 99 → current.stacks i = initial.stacks i

def rowBytes (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a : RawIndex D × QuarticCode p D) (Q : CoeffList D (QuarticCode p D)) :
    List (List Bool) := Q.map (fun b => encodeTerm (pairValue p D M t a b))

def prependAll (records : List (List Bool)) (output : List Bool) : List Bool :=
  records.foldl (fun acc bits => prependRecord bits acc) output

theorem encodeTerm_length (p D : ℕ) (a : RawIndex D × QuarticCode p D)
    (ha : Retained D a.1) :
    (encodeTerm a).length = 2*indexBits D+8*baseWidth p (D+1)+2 := by
  simp [encodeTerm, SubexpArgumentProgram.recordBody, Encoding.length_frame,
    fixedKey_length a.1 ha, flat_length]
  omega

theorem recordBudget_uniform (cost : ℕ) (records : List (List Bool)) (L : ℕ)
    (hL : ∀ bits ∈ records, bits.length = L) :
    RecordPrograms.budget (fun _ => cost) records = records.length*(6*L+cost+7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
    have hb := hL bits (by simp)
    have hr := ih (fun b h => hL b (by simp [h]))
    simp only [RecordPrograms.budget, List.length_cons, hb, hr]
    ring

def innerBudget (B I count : ℕ) : ℕ :=
  3+count*(pairBudget B I+12*I+48*B+19)

theorem pairCallback_contract (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a : RawIndex D × QuarticCode p D) (ha : Retained D a.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hleft : d.stacks 93 = fixedKey a.1) (hvalue : d.stacks 94 = flat a.2)
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h16 : d.stacks 16 = []) (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = [])
    (h24 : d.stacks 24 = []) (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) :
    RecordPrograms.CallbackContractWithOn innerPorts pairCallback (fun _ => false)
      (fun _ => pairBudget (baseWidth p (D+1)) (indexBits D)) (innerFrame d)
      (PrependEffect 99 (pairRecordEffect p D M t a)) (validTerm p D) := by
  intro bits tail base hbits hbase
  obtain ⟨b, hb, rfl⟩ := hbits
  let input := RecordPrograms.state innerPorts base false true false tail (encodeTerm b).reverse
  have hframe : ∀ i, i ≠ 97 → i ≠ 17 → i ≠ 99 → input.stacks i = d.stacks i := by
    intro i hi97 hi17 hi99
    simpa [input, RecordPrograms.state, innerPorts, hi97, hi17] using
      hbase i hi97 hi17 hi99
  have work : ∀ i, input.stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    rw [hframe _ (mulPort_ne i 97 (by decide)) (mulPort_ne i 17 (by decide))
      (mulPort_ne i 99 (by decide))]
    exact hwork i
  obtain ⟨n, e, hn, he, hs, hr8, hr9, hr15⟩ := pairCallback_eval p D M t a.2 b.2
    a.1 b.1 ha hb input width hw work
    ((hframe 93 (by decide) (by decide) (by decide)).trans hleft)
    ((hframe 94 (by decide) (by decide) (by decide)).trans hvalue)
    (by simp [input, RecordPrograms.state, innerPorts, encodeTerm])
    ((hframe 92 (by decide) (by decide) (by decide)).trans hkeywidth)
    ((hframe 16 (by decide) (by decide) (by decide)).trans h16)
    ((hframe 18 (by decide) (by decide) (by decide)).trans h18)
    ((hframe 19 (by decide) (by decide) (by decide)).trans h19)
    ((hframe 24 (by decide) (by decide) (by decide)).trans h24)
    ((hframe 95 (by decide) (by decide) (by decide)).trans h95)
    ((hframe 96 (by decide) (by decide) (by decide)).trans h96)
  refine ⟨n, e, hn, ?_, ?_, ?_⟩
  · intro i hi97 hi17 hi99
    simpa [hs, hi17, hi99] using hframe i hi97 hi17 hi99
  · change e.stacks 99 = prependRecord
      (pairRecordEffect p D M t a (encodeTerm b)) (base.stacks 99)
    rw [pairRecordEffect_apply]
    simp [prependRecord, hs, encodeTerm, pairValue, input,
      RecordPrograms.state, innerPorts]
  · have hself : RecordPrograms.state innerPorts e false true false tail [] = e := by
      apply RecordPrograms.state_eq_self
      · exact hr8
      · exact hr9
      · exact hr15
      · simp [hs, input, RecordPrograms.state, innerPorts]
      · simp [hs, innerPorts]
    simpa only [hself] using he

/-- The whole right-operand scan, with all physical cursor and frame costs.
The output is a fold over actual product records; no semantic operation is
executed by the iterator specification. -/
theorem inner_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a : RawIndex D × QuarticCode p D) (ha : Retained D a.1)
    (Q : CoeffList D (QuarticCode p D)) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hleft : d.stacks 93 = fixedKey a.1) (hvalue : d.stacks 94 = flat a.2)
    (hsource : d.stacks 97 = Encoding.encodeList id (Q.map encodeTerm))
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = [])
    (h24 : d.stacks 24 = []) (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) :
    ∃ n e, n ≤ innerBudget (baseWidth p (D+1)) (indexBits D) Q.length ∧
      Eval inner n d e ∧
      e.stacks = Function.update (Function.update d.stacks 97 []) 99
        (prependAll (rowBytes p D M t a Q) (d.stacks 99)) ∧
      e.regs 8 = false ∧ e.regs 9 = true ∧ e.regs 15 = false := by
  have hvalid : ∀ bits ∈ Q.map encodeTerm, validTerm p D bits := by
    intro bits hbits
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hbits
    exact ⟨b,hQ b hb,rfl⟩
  obtain ⟨n,next,hn,hnext,hvis,hloop⟩ := RecordPrograms.iterate_run_with_on
    innerPorts pairCallback (fun _ => false)
    (fun _ => pairBudget (baseWidth p (D+1)) (indexBits D)) (innerFrame d)
    (PrependEffect 99 (pairRecordEffect p D M t a)) (validTerm p D)
    (pairCallback_contract p D M t a ha d width hw hwork hleft hvalue hkeywidth
      h16 h18 h19 h24 h95 h96)
    (Q.map encodeTerm) [] d hvalid (fun _ _ _ _ => rfl)
    (d.regs 8) (d.regs 9) (d.regs 15)
  have hstart : RecordPrograms.state innerPorts d (d.regs 8) (d.regs 9) (d.regs 15)
      (Encoding.encodeList id (Q.map encodeTerm) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa only [innerPorts, List.append_nil] using hsource
    · simpa only [innerPorts] using h17
  have hfold := hvis.fold_of_false (fun _ _ => rfl) (fun s => s.stacks 99)
    (fun acc bits => prependRecord (pairRecordEffect p D M t a bits) acc)
    (fun _ _ _ h => h)
  have hout : next.stacks 99 = prependAll (rowBytes p D M t a Q) (d.stacks 99) := by
    simpa only [List.foldl_map, pairRecordEffect_apply, prependAll, rowBytes] using hfold
  let e := RecordPrograms.state innerPorts next false true false [] []
  refine ⟨n,e,?_,?_,?_,by simp [e,RecordPrograms.state,innerPorts],
    by simp [e,RecordPrograms.state,innerPorts],by simp [e,RecordPrograms.state,innerPorts]⟩
  · have hb := recordBudget_uniform (pairBudget (baseWidth p (D+1)) (indexBits D))
      (Q.map encodeTerm) (2*indexBits D+8*baseWidth p (D+1)+2) (by
        intro bits hbits
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hbits
        exact encodeTerm_length p D b (hQ b hb))
    rw [hb, List.length_map] at hn
    unfold innerBudget
    nlinarith
  · simpa only [inner, hstart, any_false, unread_false] using hloop
  · funext i
    by_cases hi97 : i=97
    · subst i; simp [e,RecordPrograms.state,innerPorts]
    by_cases hi17 : i=17
    · subst i; simp [e,RecordPrograms.state,innerPorts,h17]
    by_cases hi99 : i=99
    · subst i; simpa [e,RecordPrograms.state,innerPorts] using hout
    · simpa [e,RecordPrograms.state,innerPorts,hi97,hi17,hi99] using
        hnext i hi97 hi17 hi99

end InnerExecution

section RowExecution

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift

def resetOuterState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 7 false, d.stacks⟩

theorem resetOuter_eval (d : Data) : Eval resetOuter 3 d (resetOuterState d) := by
  let a : StructuredProgram.Atom 16 128 := .set 0 false
  let b : StructuredProgram.Atom 16 128 := .set 1 true
  let c : StructuredProgram.Atom 16 128 := .set 7 false
  have ha := Eval.base (StructuredProgram.Eval.atom a d)
  have hb := Eval.base (StructuredProgram.Eval.atom b (a.eval d))
  have hc := Eval.base (StructuredProgram.Eval.atom c (b.eval (a.eval d)))
  simpa [resetOuter, resetOuterState, a, b, c, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using ha.seq (hb.seq hc)

def rowBudget (B I count inputBits : ℕ) : ℕ :=
  innerBudget B I count+7*inputBits+20*I+70*B+50

theorem rowCallback_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (a : RawIndex D × QuarticCode p D) (ha : Retained D a.1)
    (Q : CoeffList D (QuarticCode p D)) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hinput : d.stacks 16 = (encodeTerm a).reverse)
    (hright : d.stacks 23 = Encoding.encodeList id (Q.map encodeTerm))
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = [])
    (h24 : d.stacks 24 = []) (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) (h97 : d.stacks 97 = []) :
    ∃ n e, n ≤ rowBudget (baseWidth p (D+1)) (indexBits D) Q.length
        (Encoding.encodeList id (Q.map encodeTerm)).length ∧
      Eval rowCallback n d e ∧
      e.stacks = Function.update (Function.update d.stacks 16 []) 99
        (prependAll (rowBytes p D M t a Q) (d.stacks 99)) ∧
      e.regs 0 = false ∧ e.regs 1 = true ∧ e.regs 7 = false := by
  obtain ⟨d1,hparse,hs1⟩ := parseLeft_eval d (fixedKey a.1) (flat a.2)
    hinput h93 h94 h18 h19
  let d2 := SubexpDenseKeyProgram.copied 23 97 d1
  have hcopy := SubexpDenseKeyProgram.copy_eval 23 97 d1
    (by decide) (by decide) (by decide) (by simpa [hs1] using h24)
  have hs2 : d2.stacks = Function.update d1.stacks 97 (d1.stacks 23) := by
    simp [d2,SubexpDenseKeyProgram.copied,StackRoutines.copyStacks,hs1,h97]
  have work2 : ∀ i, d2.stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    rw [hs2,hs1]
    simpa only [Function.update_of_ne (mulPort_ne i 97 (by decide)),
      Function.update_of_ne (mulPort_ne i 94 (by decide)),
      Function.update_of_ne (mulPort_ne i 93 (by decide)),
      Function.update_of_ne (mulPort_ne i 16 (by decide))] using hwork i
  obtain ⟨ni,d3,hi,hinner,hs3,_,_,_⟩ := inner_eval p D M t a ha Q hQ d2 width hw work2
    (by simp [hs2,hs1]) (by simp [hs2,hs1])
    (by simpa [hs2,hs1] using hright) (by simpa [hs2,hs1] using hkeywidth)
    (by simp [hs2,hs1]) (by simpa [hs2,hs1] using h17)
    (by simpa [hs2,hs1] using h18) (by simpa [hs2,hs1] using h19)
    (by simpa [hs2,hs1] using h24) (by simpa [hs2,hs1] using h95)
    (by simpa [hs2,hs1] using h96)
  let d4 := SubexpDenseKeyProgram.cleared 93 d3
  let d5 := SubexpDenseKeyProgram.cleared 94 d4
  have h93clear := SubexpDenseKeyProgram.clear_eval 93 d3
  have h94clear := SubexpDenseKeyProgram.clear_eval 94 d4
  have hreset := resetOuter_eval d5
  have htotal := hparse.seq (hcopy.seq (hinner.seq (h93clear.seq (h94clear.seq hreset))))
  refine ⟨_,resetOuterState d5,?_,htotal,?_,by simp [resetOuterState],
    by simp [resetOuterState],by simp [resetOuterState]⟩
  · have hcopylen : (d1.stacks 23).length = (Encoding.encodeList id (Q.map encodeTerm)).length := by
      simp [hs1,hright]
    have h93len : (d3.stacks 93).length = indexBits D := by
      simp [hs3,hs2,hs1,fixedKey_length a.1 ha]
    have h94len : (d4.stacks 94).length = 4*baseWidth p (D+1) := by
      simp [d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1,flat_length]
    simp only [flat_length,fixedKey_length a.1 ha,hcopylen,h93len,h94len]
    unfold rowBudget
    omega
  · funext i
    by_cases hi16 : i=16
    · subst i; simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1]
    by_cases hi99 : i=99
    · subst i; simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1]
    by_cases hi93 : i=93
    · subst i; simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1,h93]
    by_cases hi94 : i=94
    · subst i; simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1,h94]
    by_cases hi97 : i=97
    · subst i; simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1,h97]
    simp [resetOuterState,d5,d4,SubexpDenseKeyProgram.cleared,hs3,hs2,hs1,
      hi16,hi99,hi93,hi94,hi97]

end RowExecution

section OuterExecution

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift

def outerFrame (initial current : Data) : Prop :=
  ∀ i, i ≠ 98 → i ≠ 16 → i ≠ 99 → current.stacks i = initial.stacks i

/-- This extension is used only by the proof of the typed iterator. The
runtime executes `rowCallback`, which contains only fixed finite programs. -/
noncomputable def rowRecordEffect (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (Q : CoeffList D (QuarticCode p D)) : List Bool → List (List Bool) :=
  Function.extend encodeTerm (fun a => rowBytes p D M t a Q) (fun _ => [])

theorem rowRecordEffect_apply (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (Q : CoeffList D (QuarticCode p D)) (a : RawIndex D × QuarticCode p D) :
    rowRecordEffect p D M t Q (encodeTerm a) = rowBytes p D M t a Q :=
  (encodeTerm_injective p D).extend_apply _ _ _

def BlockEffect (f : List Bool → List (List Bool)) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 99 = prependAll (f bits) (a.stacks 99)

theorem rowCallback_contract (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (Q : CoeffList D (QuarticCode p D)) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hright : d.stacks 23 = Encoding.encodeList id (Q.map encodeTerm))
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = [])
    (h24 : d.stacks 24 = []) (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) (h97 : d.stacks 97 = []) :
    RecordPrograms.CallbackContractWithOn outerPorts rowCallback (fun _ => false)
      (fun _ => rowBudget (baseWidth p (D+1)) (indexBits D) Q.length
        (Encoding.encodeList id (Q.map encodeTerm)).length)
      (outerFrame d) (BlockEffect (rowRecordEffect p D M t Q)) (validTerm p D) := by
  intro bits tail base hbits hbase
  obtain ⟨a,ha,rfl⟩ := hbits
  let input := RecordPrograms.state outerPorts base false true false tail (encodeTerm a).reverse
  have hframe : ∀ i, i ≠ 98 → i ≠ 16 → i ≠ 99 → input.stacks i = d.stacks i := by
    intro i hi98 hi16 hi99
    simpa [input,RecordPrograms.state,outerPorts,hi98,hi16] using hbase i hi98 hi16 hi99
  have work : ∀ i, input.stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    rw [hframe _ (mulPort_ne i 98 (by decide)) (mulPort_ne i 16 (by decide))
      (mulPort_ne i 99 (by decide))]
    exact hwork i
  obtain ⟨n,e,hn,he,hs,hr0,hr1,hr7⟩ := rowCallback_eval p D M t a ha Q hQ input width hw
    work (by simp [input,RecordPrograms.state,outerPorts])
    ((hframe 23 (by decide) (by decide) (by decide)).trans hright)
    ((hframe 92 (by decide) (by decide) (by decide)).trans hkeywidth)
    ((hframe 17 (by decide) (by decide) (by decide)).trans h17)
    ((hframe 18 (by decide) (by decide) (by decide)).trans h18)
    ((hframe 19 (by decide) (by decide) (by decide)).trans h19)
    ((hframe 24 (by decide) (by decide) (by decide)).trans h24)
    ((hframe 93 (by decide) (by decide) (by decide)).trans h93)
    ((hframe 94 (by decide) (by decide) (by decide)).trans h94)
    ((hframe 95 (by decide) (by decide) (by decide)).trans h95)
    ((hframe 96 (by decide) (by decide) (by decide)).trans h96)
    ((hframe 97 (by decide) (by decide) (by decide)).trans h97)
  refine ⟨n,e,hn,?_,?_,?_⟩
  · intro i hi98 hi16 hi99
    simpa [hs,hi16,hi99] using hframe i hi98 hi16 hi99
  · simp [BlockEffect,hs,rowRecordEffect_apply,input,RecordPrograms.state,outerPorts]
  · have hself : RecordPrograms.state outerPorts e false true false tail [] = e := by
      apply RecordPrograms.state_eq_self
      · exact hr0
      · exact hr1
      · exact hr7
      · simp [hs,input,RecordPrograms.state,outerPorts]
      · simp [hs,outerPorts]
    simpa only [hself] using he

theorem prependAll_flatMap {α : Type*} (records : List α) (f : α → List (List Bool))
    (output : List Bool) :
    records.foldl (fun acc a => prependAll (f a) acc) output =
      prependAll (records.flatMap f) output := by
  induction records generalizing output with
  | nil => rfl
  | cons a rest ih =>
    simpa only [List.foldl_cons,List.flatMap_cons,prependAll,List.foldl_append] using
      ih (prependAll (f a) output)

def allPairs (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) : CoeffList D (QuarticCode p D) :=
  P.flatMap (fun a => Q.map (pairValue p D M t a))

def outerBudget (B I leftCount rightCount rightBits : ℕ) : ℕ :=
  3+leftCount*(rowBudget B I rightCount rightBits+12*I+48*B+19)

theorem outer_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hsource : d.stacks 98 = Encoding.encodeList id (P.map encodeTerm))
    (hright : d.stacks 23 = Encoding.encodeList id (Q.map encodeTerm))
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) (h24 : d.stacks 24 = [])
    (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) (h97 : d.stacks 97 = []) :
    ∃ n e, n ≤ outerBudget (baseWidth p (D+1)) (indexBits D) P.length Q.length
        (Encoding.encodeList id (Q.map encodeTerm)).length ∧
      Eval outer n d e ∧
      e.stacks = Function.update (Function.update d.stacks 98 []) 99
        (prependAll ((allPairs p D M t P Q).map encodeTerm) (d.stacks 99)) ∧
      e.regs 0 = false ∧ e.regs 1 = true ∧ e.regs 7 = false := by
  have hvalid : ∀ bits ∈ P.map encodeTerm, validTerm p D bits := by
    intro bits hbits
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hbits
    exact ⟨a,hP a ha,rfl⟩
  obtain ⟨n,next,hn,hnext,hvis,hloop⟩ := RecordPrograms.iterate_run_with_on
    outerPorts rowCallback (fun _ => false)
    (fun _ => rowBudget (baseWidth p (D+1)) (indexBits D) Q.length
      (Encoding.encodeList id (Q.map encodeTerm)).length) (outerFrame d)
    (BlockEffect (rowRecordEffect p D M t Q)) (validTerm p D)
    (rowCallback_contract p D M t Q hQ d width hw hwork hright hkeywidth
      h17 h18 h19 h24 h93 h94 h95 h96 h97)
    (P.map encodeTerm) [] d hvalid (fun _ _ _ _ => rfl)
    (d.regs 0) (d.regs 1) (d.regs 7)
  have hstart : RecordPrograms.state outerPorts d (d.regs 0) (d.regs 1) (d.regs 7)
      (Encoding.encodeList id (P.map encodeTerm) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa only [outerPorts, List.append_nil] using hsource
    · simpa only [outerPorts] using h16
  have hfold := hvis.fold_of_false (fun _ _ => rfl) (fun s => s.stacks 99)
    (fun acc bits => prependAll (rowRecordEffect p D M t Q bits) acc)
    (fun _ _ _ h => h)
  have hout : next.stacks 99 =
      prependAll ((allPairs p D M t P Q).map encodeTerm) (d.stacks 99) := by
    simpa only [List.foldl_map,rowRecordEffect_apply,prependAll_flatMap,
      allPairs,List.map_flatMap,List.map_map,Function.comp_def,rowBytes] using hfold
  let e := RecordPrograms.state outerPorts next false true false [] []
  refine ⟨n,e,?_,?_,?_,by simp [e,RecordPrograms.state,outerPorts],
    by simp [e,RecordPrograms.state,outerPorts],by simp [e,RecordPrograms.state,outerPorts]⟩
  · have hb := recordBudget_uniform
      (rowBudget (baseWidth p (D+1)) (indexBits D) Q.length
        (Encoding.encodeList id (Q.map encodeTerm)).length)
      (P.map encodeTerm) (2*indexBits D+8*baseWidth p (D+1)+2) (by
        intro bits hbits
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hbits
        exact encodeTerm_length p D a (hP a ha))
    rw [hb,List.length_map] at hn
    unfold outerBudget
    nlinarith
  · simpa only [outer,hstart,any_false,unread_false] using hloop
  · funext i
    by_cases hi98 : i=98
    · subst i; simp [e,RecordPrograms.state,outerPorts]
    by_cases hi16 : i=16
    · subst i; simp [e,RecordPrograms.state,outerPorts,h16]
    by_cases hi99 : i=99
    · subst i; simpa [e,RecordPrograms.state,outerPorts] using hout
    · simpa [e,RecordPrograms.state,outerPorts,hi98,hi16,hi99] using hnext i hi98 hi16 hi99

end OuterExecution

section PairListExecution

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift SubexpDenseSerialization

theorem encodeTerms_eq (p D : ℕ) (P : CoeffList D (QuarticCode p D)) :
    Encoding.encodeList id (P.map encodeTerm) = encodeFixedQuarticCoefficients p D P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    simp only [List.map_cons,Encoding.encodeList] at ih ⊢
    simpa only [encodeTerm,flat_eq_block,encodeFixedQuarticCoefficients,
      encodeFixedCoefficients,Encoding.encodeList,encodeFixedRecord,
      SubexpArgumentProgram.recordBody,framedRecord,id_eq] using congrArg
        (fun tail => true :: (Encoding.frame (encodeTerm a) ++ tail)) ih

def pairListTime (p D : ℕ) (P Q : CoeffList D (QuarticCode p D)) : ℕ :=
  7*(encodeFixedQuarticCoefficients p D P).length+5+
    outerBudget (baseWidth p (D+1)) (indexBits D) P.length Q.length
      (encodeFixedQuarticCoefficients p D Q).length

/-- Copy the left input once, then execute the two complete finite scans.
Only the generated-list stack changes at this boundary. -/
theorem command_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hleft : d.stacks 22 = encodeFixedQuarticCoefficients p D P)
    (hright : d.stacks 23 = encodeFixedQuarticCoefficients p D Q)
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) (h24 : d.stacks 24 = [])
    (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) (h97 : d.stacks 97 = [])
    (h98 : d.stacks 98 = []) (h99 : d.stacks 99 = [false]) :
    ∃ n e, n ≤ pairListTime p D P Q ∧ Eval command n d e ∧
      e.stacks = Function.update d.stacks 99
        (encodeFixedQuarticCoefficients p D (allPairs p D M t P Q).reverse) := by
  let d1 := SubexpDenseKeyProgram.copied 22 98 d
  have hcopy := SubexpDenseKeyProgram.copy_eval 22 98 d (by decide) (by decide) (by decide) h24
  have hs1 : d1.stacks = Function.update d.stacks 98 (d.stacks 22) := by
    simp [d1,SubexpDenseKeyProgram.copied,StackRoutines.copyStacks,h98]
  have work1 : ∀ i, d1.stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    simpa only [hs1,Function.update_of_ne (mulPort_ne i 98 (by decide))] using hwork i
  obtain ⟨n,e,hn,he,hs,_,_,_⟩ := outer_eval p D M t P Q hP hQ d1 width hw work1
    (by simpa [hs1,encodeTerms_eq] using hleft)
    (by simpa [hs1,encodeTerms_eq] using hright)
    (by simpa [hs1] using hkeywidth)
    (by simpa [hs1] using h16) (by simpa [hs1] using h17)
    (by simpa [hs1] using h18) (by simpa [hs1] using h19)
    (by simpa [hs1] using h24) (by simpa [hs1] using h93)
    (by simpa [hs1] using h94) (by simpa [hs1] using h95)
    (by simpa [hs1] using h96) (by simpa [hs1] using h97)
  refine ⟨_,e,?_,hcopy.seq he,?_⟩
  · simpa [pairListTime,hleft,encodeTerms_eq] using Nat.add_le_add_left hn
      (7*(d.stacks 22).length+5)
  · have hout : prependAll ((allPairs p D M t P Q).map encodeTerm) (d1.stacks 99) =
        encodeFixedQuarticCoefficients p D (allPairs p D M t P Q).reverse := by
      have hf := fold_prependRecord id ((allPairs p D M t P Q).map encodeTerm) []
      simpa [prependAll,hs1,h99,Encoding.encodeList,← List.map_reverse,encodeTerms_eq]
        using hf
    rw [hs,hout,hs1]
    funext i
    by_cases h99i : i=99
    · subst i; simp
    by_cases h98i : i=98
    · subst i; simp [h98]
    simp [h99i,h98i]

end PairListExecution

section ProjectionCall

def projectionRegisters : Fin 8 ↪ Fin 16 := ⟨lowEight, by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h⟩

def projectionEmbedding : Fin 26 ↪ Fin 128 := ⟨projectionPorts,projectionPorts_injective⟩

def localProjectionState (d : Data) : State 8 26 :=
  ⟨d.regs ∘ lowEight,d.stacks ∘ projectionPorts⟩

def projectedState (d : Data) (regs : Fin 8 → Bool) (bits : List Bool) : Data :=
  ⟨Fin.addCases (m := 8) (n := 8) (motive := fun _ => Bool)
      regs (fun i : Fin 8 => d.regs (Fin.natAdd 8 i)),
    Function.update (Function.update d.stacks 20 []) 21 bits⟩

theorem projectPairs_call (d : Data) (n : ℕ) (regs : Fin 8 → Bool) (bits : List Bool)
    (ht : Trace Projection.projectProgram n
      ((localProjectionState d).withPC (some Projection.projectProgram.entry))
      ((⟨regs,Function.update (Function.update (localProjectionState d).stacks 20 []) 21 bits⟩ :
        State 8 26).withPC none)) :
    Eval projectPairs n d (projectedState d regs bits) := by
  have hi : embedState lowEight projectionPorts d (localProjectionState d) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ projectionRegisters.injective projectionPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; rfl
    · intros; rfl
  have ho : embedState lowEight projectionPorts d
      (⟨regs,Function.update (Function.update (localProjectionState d).stacks 20 []) 21 bits⟩ :
        State 8 26) = projectedState d regs bits := by
    apply embedState_eq_of_ports _ _ _ _ _ projectionRegisters.injective projectionPorts_injective
    · intro i
      exact Fin.addCases_left (m := 8) (n := 8) (motive := fun _ => Bool)
        (left := regs) (right := fun j : Fin 8 => d.regs (Fin.natAdd 8 j)) i
    · intro j hj
      revert hj
      refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) j
      · intro hj; exact False.elim (hj ⟨i,rfl⟩)
      · intro _
        exact Fin.addCases_right (m := 8) (n := 8) (motive := fun _ => Bool)
          (left := regs) (right := fun j : Fin 8 => d.regs (Fin.natAdd 8 j)) i
    · intro i; fin_cases i <;> rfl
    · intro j hj
      have h20 : j ≠ 20 := fun h => hj ⟨20,by simpa [projectionPorts] using h.symm⟩
      have h21 : j ≠ 21 := fun h => hj ⟨21,by simpa [projectionPorts] using h.symm⟩
      simp [projectedState,h20,h21]
  simpa only [projectPairs,hi,ho] using eval_call_lifted Projection.projectProgram
    lowEight projectionPorts d projectionRegisters.injective projectionPorts_injective ht

end ProjectionCall

section CompleteMultiplication

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpQuarticFlatLift SubexpDenseSerialization SubexpCanonicalWords

theorem controller_input_update (regs : Fin 8 → Bool)
    (modulus width queries output input right master : List Bool) :
    (Projection.controllerState regs modulus [] width [] [] queries output input right master).stacks =
      Function.update
        (Projection.controllerState regs modulus [] width [] [] queries output [] right master).stacks
        22 input := by
  funext i
  fin_cases i <;> simp [Projection.controllerState,Projection.extendState,
    Fin.addCases,Fin.coe_ofNat_eq_mod]

theorem controller_output_update (regs regs' : Fin 8 → Bool)
    (modulus width queries input right master output : List Bool) :
    (Projection.controllerState regs' modulus [] width [] [] [] output input right master).stacks =
      Function.update (Function.update
        (Projection.controllerState regs modulus [] width [] [] queries [false] input right master).stacks
        20 []) 21 output := by
  funext i
  fin_cases i <;> simp [Projection.controllerState,Projection.extendState,
    SubexpCoefficientLookup.state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,
    Fin.addCases,Fin.coe_ofNat_eq_mod]

theorem projectPairs_exact (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (c : Fin 4 → ZMod (p^(D+1)))
    (t z o : QuarticCode p D) (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (d : Data) (width right : List Bool) (hw : width.length = baseWidth p (D+1))
    (hlocal : localProjectionState d = Projection.controllerState (d.regs ∘ lowEight)
      M.bits [] width [] [] (Projection.queryBytes slots) [false]
      (encodeFixedQuarticCoefficients p D P) right (Projection.queryBytes slots)) :
    ∃ n regs, n ≤ Projection.projectionTime p D M P slots ∧
      Eval projectPairs n d (projectedState d regs
        (encodeFixedQuarticCoefficients p D
          (programProject (preparedProgram p D M t z o) slots P).1)) := by
  obtain ⟨rf,n,hn,ht⟩ := Projection.projectProgram_exact p D M c t z o hz hcanonical
    P slots width right hw (d.regs ∘ lowEight)
  refine ⟨n,SubexpCoefficientLookup.normalized rf false true false,hn,?_⟩
  apply projectPairs_call
  rw [hlocal]
  have hout := controller_output_update (d.regs ∘ lowEight)
    (SubexpCoefficientLookup.normalized rf false true false) M.bits width
    (Projection.queryBytes slots) (encodeFixedQuarticCoefficients p D P) right
    (Projection.queryBytes slots)
    (encodeFixedQuarticCoefficients p D (programProject (preparedProgram p D M t z o) slots P).1)
  convert ht using 1
  apply congrArg (fun s : State 8 26 => s.withPC none)
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · exact hout.symm

def initializedPairs (d : Data) : Data :=
  ⟨Function.update d.regs 0 false,Function.update d.stacks 99 (false :: d.stacks 99)⟩

theorem initializePairs_eval (d : Data) : Eval initializePairs 2 d (initializedPairs d) := by
  let a : StructuredProgram.Atom 16 128 := .set 0 false
  let b : StructuredProgram.Atom 16 128 := .push 99 0
  have ha := Eval.base (StructuredProgram.Eval.atom a d)
  have hb := Eval.base (StructuredProgram.Eval.atom b (a.eval d))
  simpa [initializePairs,initializedPairs,a,b,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC,execInstr] using ha.seq hb

def multiplicationTime (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) : ℕ :=
  2+pairListTime p D P Q+
    Projection.projectionTime p D M (allPairs p D M t P Q).reverse slots+
    2*(encodeFixedQuarticCoefficients p D (allPairs p D M t P Q).reverse).length+4

/-- A complete physical multiplication core. The workspace premises name
actual stored words, counters, and empty scratch stacks; the three code
phases are pair generation, projection, and cleanup. -/
theorem mulCore_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (c : Fin 4 → ZMod (p^(D+1)))
    (t z o : QuarticCode p D) (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (width : List Bool) (hw : width.length = baseWidth p (D+1))
    (hwork : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace M.bits width t i)
    (hleft : d.stacks 22 = encodeFixedQuarticCoefficients p D P)
    (hright : d.stacks 23 = encodeFixedQuarticCoefficients p D Q)
    (hkeywidth : d.stacks 92 = List.replicate (indexBits D) true)
    (hlocal : localProjectionState d = Projection.controllerState (d.regs ∘ lowEight)
      M.bits [] width [] [] (Projection.queryBytes slots) [false] []
      (encodeFixedQuarticCoefficients p D Q) (Projection.queryBytes slots))
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) (h24 : d.stacks 24 = [])
    (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = [])
    (h95 : d.stacks 95 = []) (h96 : d.stacks 96 = []) (h97 : d.stacks 97 = [])
    (h98 : d.stacks 98 = []) (h99 : d.stacks 99 = []) :
    ∃ n e, n+1 ≤ multiplicationTime p D M t P Q slots ∧ Eval mulCore n d e ∧
      e.stacks = Function.update (Function.update d.stacks 20 []) 21
        (encodeFixedQuarticCoefficients p D
          (programMul (preparedProgram p D M t z o) slots P Q).1) := by
  let d1 := initializedPairs d
  have hi := initializePairs_eval d
  have work1 : ∀ i, d1.stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace M.bits width t i := by
    intro i
    simpa only [d1,initializedPairs,
      Function.update_of_ne (mulPort_ne i 99 (by decide))] using hwork i
  obtain ⟨ng,d2,hg,hgen,hs2⟩ := command_eval p D M t P Q hP hQ d1 width hw work1
    (by simpa [d1,initializedPairs] using hleft) (by simpa [d1,initializedPairs] using hright)
    (by simpa [d1,initializedPairs] using hkeywidth)
    (by simpa [d1,initializedPairs] using h16) (by simpa [d1,initializedPairs] using h17)
    (by simpa [d1,initializedPairs] using h18) (by simpa [d1,initializedPairs] using h19)
    (by simpa [d1,initializedPairs] using h24) (by simpa [d1,initializedPairs] using h93)
    (by simpa [d1,initializedPairs] using h94) (by simpa [d1,initializedPairs] using h95)
    (by simpa [d1,initializedPairs] using h96) (by simpa [d1,initializedPairs] using h97)
    (by simpa [d1,initializedPairs] using h98) (by simp [d1,initializedPairs,h99])
  let generated := (allPairs p D M t P Q).reverse
  have hstacks : d2.stacks = Function.update d.stacks 99 (encodeFixedQuarticCoefficients p D generated) := by
    simpa [d1,initializedPairs,generated] using hs2
  have hlocal2 : localProjectionState d2 = Projection.controllerState (d2.regs ∘ lowEight)
      M.bits [] width [] [] (Projection.queryBytes slots) [false]
      (encodeFixedQuarticCoefficients p D generated)
      (encodeFixedQuarticCoefficients p D Q) (Projection.queryBytes slots) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · have hbase := congrArg StructuredProgram.State.stacks hlocal
      rw [controller_input_update]
      have hregfree :
          (Projection.controllerState (d.regs ∘ lowEight)
            M.bits [] width [] [] (Projection.queryBytes slots) [false] []
            (encodeFixedQuarticCoefficients p D Q) (Projection.queryBytes slots)).stacks =
          (Projection.controllerState (d2.regs ∘ lowEight)
            M.bits [] width [] [] (Projection.queryBytes slots) [false] []
            (encodeFixedQuarticCoefficients p D Q) (Projection.queryBytes slots)).stacks := by
        rfl
      rw [hregfree] at hbase
      funext i
      have hb := congrFun hbase i
      fin_cases i
      all_goals
        simp [localProjectionState,hstacks,projectionPorts,
          Projection.controllerState,Projection.extendState,Fin.addCases,
          Fin.coe_ofNat_eq_mod] at hb ⊢
      all_goals exact hb
  obtain ⟨np,rp,hp,hproj⟩ := projectPairs_exact p D M c t z o hz hcanonical generated slots
    d2 width (encodeFixedQuarticCoefficients p D Q) hw hlocal2
  have hvalue : (programProject (preparedProgram p D M t z o) slots generated).1 =
      (programMul (preparedProgram p D M t z o) slots P Q).1 := by
    exact SubexpCanonicalDense.reversed_pairs_mul p D M t z o c hz hcanonical P Q slots
  rw [hvalue] at hproj
  let result := encodeFixedQuarticCoefficients p D
    (programMul (preparedProgram p D M t z o) slots P Q).1
  let d3 := projectedState d2 rp result
  let d4 := SubexpDenseKeyProgram.cleared 99 d3
  have hc := SubexpDenseKeyProgram.clear_eval 99 d3
  have htotal := hi.seq (hgen.seq (hproj.seq hc))
  refine ⟨_,d4,?_,htotal,?_⟩
  · have hl : (d3.stacks 99).length = (encodeFixedQuarticCoefficients p D generated).length := by
      simp [d3,projectedState,hstacks]
    simp only [hl]
    unfold multiplicationTime
    dsimp only [generated] at hp ⊢
    omega
  · funext i
    by_cases hi99 : i=99
    · subst i; simp [d4,d3,result,SubexpDenseKeyProgram.cleared,projectedState,hstacks,h99]
    by_cases hi20 : i=20
    · subst i; simp [d4,d3,result,SubexpDenseKeyProgram.cleared,projectedState,hstacks]
    by_cases hi21 : i=21
    · subst i; simp [d4,d3,result,SubexpDenseKeyProgram.cleared,projectedState,hstacks]
    simp [d4,d3,result,SubexpDenseKeyProgram.cleared,projectedState,hstacks,hi99,hi20,hi21]

end CompleteMultiplication

section ExplicitCosts

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpDenseSerialization

def recordBits (B I : ℕ) : ℕ := 4*I+16*B+6

theorem serialized_length_le (p D : ℕ) (P : CoeffList D (QuarticCode p D))
    (hkey : ∀ a ∈ P, (fixedKey a.1).length ≤ indexBits D) :
    (encodeFixedQuarticCoefficients p D P).length ≤
      1+recordBits (baseWidth p (D+1)) (indexBits D)*P.length := by
  calc
    _ ≤ 1+(4*indexBits D+4*(4*baseWidth p (D+1))+6)*P.length := by
      apply encodeFixedCoefficients_length_le _ P (indexBits D) (4*baseWidth p (D+1)) hkey
      intro a _
      rw [← flat_eq_block]
      exact (flat_length a.2).le
    _ = _ := by unfold recordBits; ring

theorem retained_serialized_length_le (p D : ℕ) (P : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) :
    (encodeFixedQuarticCoefficients p D P).length ≤
      1+recordBits (baseWidth p (D+1)) (indexBits D)*P.length :=
  serialized_length_le p D P (fun a ha => (fixedKey_length a.1 (hP a ha)).le)

theorem allPairs_length (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) :
    (allPairs p D M t P Q).length = P.length*Q.length := by
  induction P with
  | nil => simp [allPairs]
  | cons a P ih =>
    simp only [allPairs,List.flatMap_cons,List.length_append,List.length_map,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem allPairs_serialized_length_le (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1) :
    (encodeFixedQuarticCoefficients p D (allPairs p D M t P Q).reverse).length ≤
      1+recordBits (baseWidth p (D+1)) (indexBits D)*(P.length*Q.length) := by
  have hkey : ∀ a ∈ (allPairs p D M t P Q).reverse,
      (fixedKey a.1).length ≤ indexBits D := by
    intro a ha
    have ham : a ∈ allPairs p D M t P Q := by simpa only [List.mem_reverse] using ha
    obtain ⟨x,hx,hrow⟩ := List.mem_flatMap.mp ham
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hrow
    exact (sumKey_length x.1 y.1 (hP x hx) (hQ y hy)).le
  simpa only [List.length_reverse,allPairs_length] using
    serialized_length_le p D (allPairs p D M t P Q).reverse hkey

def projectionEnvelope (B I count inputBits : ℕ) : ℕ :=
  4+count*(6*I+Projection.scanFactor B I*(inputBits+1)+7)

theorem projectionTime_le (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hslots : ∀ a ∈ slots, Retained D a) :
    Projection.projectionTime p D M P slots ≤
      projectionEnvelope (baseWidth p (D+1)) (indexBits D) slots.length
        (encodeFixedQuarticCoefficients p D P).length := by
  have hquery : ∀ q ∈ (slots.map fixedKey).reverse, q.length ≤ indexBits D := by
    intro q hq
    have hqm : q ∈ slots.map fixedKey := by simpa only [List.mem_reverse] using hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hqm
    exact (fixedKey_length a (hslots a ha)).le
  have hcost : ∀ q ∈ (slots.map fixedKey).reverse,
      Projection.singleSlotCost p (D+1) M q (Projection.encodedRaw P) ≤
        Projection.scanFactor (baseWidth p (D+1)) (indexBits D)*
          ((encodeFixedQuarticCoefficients p D P).length+1) := by
    intro q hq
    simpa only [Projection.encodedRaw_bytes] using
      Projection.singleSlotCost_le_serialized p (D+1) M q (Projection.encodedRaw P)
        (indexBits D) (hquery q hq)
  simpa only [Projection.projectionTime,projectionEnvelope,List.length_reverse,List.length_map] using
    projectionController_cost (slots.map fixedKey).reverse
      (fun q => Projection.singleSlotCost p (D+1) M q (Projection.encodedRaw P))
      (indexBits D) _ hquery hcost

/-- An explicit fixed polynomial in physical word/key widths and the three
list lengths. In particular, no coefficient depends on the SAT clause width. -/
def denseEnvelope (B I leftCount rightCount slotCount : ℕ) : ℕ :=
  let leftBits := 1+recordBits B I*leftCount
  let rightBits := 1+recordBits B I*rightCount
  let pairBits := 1+recordBits B I*(leftCount*rightCount)
  2+(7*leftBits+5+outerBudget B I leftCount rightCount rightBits)+
    projectionEnvelope B I slotCount pairBits+2*pairBits+4

theorem multiplicationTime_le_envelope (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a) :
    multiplicationTime p D M t P Q slots ≤
      denseEnvelope (baseWidth p (D+1)) (indexBits D) P.length Q.length slots.length := by
  have hl := retained_serialized_length_le p D P hP
  have hr := retained_serialized_length_le p D Q hQ
  have hg := allPairs_serialized_length_le p D M t P Q hP hQ
  have hp := projectionTime_le p D M (allPairs p D M t P Q).reverse slots hslots
  have hl7 := Nat.mul_le_mul_left 7 hl
  have hr7 := Nat.mul_le_mul_left 7 hr
  have hrP := Nat.mul_le_mul_left P.length hr7
  have hg2 := Nat.mul_le_mul_left 2 hg
  have hgF := Nat.mul_le_mul_left (Projection.scanFactor (baseWidth p (D+1)) (indexBits D))
    (Nat.add_le_add_right hg 1)
  have hgS := Nat.mul_le_mul_left slots.length hgF
  unfold multiplicationTime pairListTime denseEnvelope outerBudget rowBudget projectionEnvelope at *
  nlinarith

end ExplicitCosts

end SubexponentialSAT.SubexpDenseProgram.Product

end OAI.Algorithms
