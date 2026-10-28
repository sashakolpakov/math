import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightGather
import OAI.Algorithms.SubexponentialSAT.SubexpWeightLiteralProgram

namespace OAI.Algorithms

/-! A complete current-exponent weight service.  It gathers selected entries
from X, reads and pads the selected Fp coordinates, computes the weight at the
supplied lifted modulus, and constructs the raw constant-polynomial literal.
The support and point bank are data; no weight is supplied by the caller. -/

namespace SubexponentialSAT.SubexpWeightDescriptorProgram

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Word := List Bool
abbrev Data := State 8 38
abbrev Code := Cmd 8 38

def gatherPorts : Fin 24 → Fin 38 :=
  ![0,20,21,22,23,24,25,1,26,27,2,28,29,30,31,32,10,33,34,8,35,3,36,37]
def literalPorts : Fin 24 → Fin 38 :=
  ![11,20,21,22,23,4,24,25,26,27,28,10,3,6,7,9,29,30,31,32,33,34,35,36]

private def gatherInverse (i : Fin 38) : Fin 24 := match i.val with
  | 0 => 0 | 20 => 1 | 21 => 2 | 22 => 3 | 23 => 4 | 24 => 5 | 25 => 6
  | 1 => 7 | 26 => 8 | 27 => 9 | 2 => 10 | 28 => 11 | 29 => 12 | 30 => 13
  | 31 => 14 | 32 => 15 | 10 => 16 | 33 => 17 | 34 => 18 | 8 => 19
  | 35 => 20 | 3 => 21 | 36 => 22 | 37 => 23 | _ => 0

private def literalInverse (i : Fin 38) : Fin 24 := match i.val with
  | 11 => 0 | 20 => 1 | 21 => 2 | 22 => 3 | 23 => 4 | 4 => 5 | 24 => 6
  | 25 => 7 | 26 => 8 | 27 => 9 | 28 => 10 | 10 => 11 | 3 => 12 | 6 => 13
  | 7 => 14 | 9 => 15 | 29 => 16 | 30 => 17 | 31 => 18 | 32 => 19
  | 33 => 20 | 34 => 21 | 35 => 22 | 36 => 23 | _ => 0

theorem gatherPorts_injective : Function.Injective gatherPorts :=
  (show Function.LeftInverse gatherInverse gatherPorts from by intro i; fin_cases i <;> rfl).injective
theorem literalPorts_injective : Function.Injective literalPorts :=
  (show Function.LeftInverse literalInverse literalPorts from by intro i; fin_cases i <;> rfl).injective

/-- X0, bank1, widths2/3, modulus4, unit5, dimension6, key width7,
support8, result9, weight records10, and accumulator11. -/
def state (r : Fin 8 → Bool) (X bank width target modulus unit : Word)
    (D I : ℕ) (support records acc out : Word) : Data :=
  ⟨r,fun i => match i.val with
    | 0 => X | 1 => bank | 2 => width | 3 => target | 4 => modulus | 5 => unit
    | 6 => List.replicate D true | 7 => List.replicate I true | 8 => support
    | 9 => out | 10 => records | 11 => acc | _ => []⟩

def setup : Code := .seq
  (.base (.seq (.atom (.set 0 false)) (.atom (.push 10 0))))
  (.call (StackRoutines.copyProgram 5 11 12 (0 : Fin 8) 1))
def gather : Code :=
  .call (ProgramLinking.liftProgram SubexpWeightGather.program id gatherPorts)
def literal : Code :=
  .call (ProgramLinking.liftProgram SubexpWeightLiteralProgram.program id literalPorts)
def command : Code := .seq setup (.seq gather literal)
def program := StructuredCalls.compiled command 8 9

theorem embed_gather (r r' : Fin 8 → Bool) (X bank width target modulus unit : Word)
    (D I : ℕ) (support records acc out support' records' : Word) :
    embedState id gatherPorts (state r X bank width target modulus unit D I support records acc out)
      (SubexpWeightGather.state r' X bank width target support' records' []) =
      state r' X bank width target modulus unit D I support' records' acc out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id gatherPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨19,by simpa [gatherPorts] using h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨16,by simpa [gatherPorts] using h.symm⟩
    fin_cases i <;> first | contradiction | rfl

theorem embed_literal (r r' : Fin 8 → Bool) (X bank width target modulus unit : Word)
    (D I : ℕ) (support records acc out records' acc' out' : Word) :
    embedState id literalPorts (state r X bank width target modulus unit D I support records acc out)
      (SubexpWeightLiteralProgram.state r' acc' modulus records' target D I out') =
      state r' X bank width target modulus unit D I support records' acc' out' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id literalPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨15,by simpa [literalPorts] using h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨11,by simpa [literalPorts] using h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨0,by simpa [literalPorts] using h.symm⟩
    fin_cases i <;> first | contradiction | rfl

theorem setup_eval (r : Fin 8 → Bool) (X bank width target modulus unit : Word)
    (D I : ℕ) (support : Word) :
    Eval setup (7*unit.length+7)
      (state r X bank width target modulus unit D I support [] [] [])
      (state (readRegs (Function.update r 0 false) 0 1 none)
        X bank width target modulus unit D I support [false] unit []) := by
  let d := state r X bank width target modulus unit D I support [] [] []
  let r0 := Function.update r 0 false
  let a := state r0 X bank width target modulus unit D I support [false] [] []
  have h0 : Eval (.base (.seq (.atom (.set 0 false)) (.atom (.push 10 0)))) 2 d a := by
    have h := (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d).seq
      (StructuredProgram.Eval.atom (.push (10 : Fin 38) 0) _)
    apply Eval.base
    convert h using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  have hc := ListRegisterProgram.copy_run (5 : Fin 38) 11 12 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a.regs a.stacks (by rfl)
  have he : (⟨readRegs a.regs 0 1 none,StackRoutines.copyStacks (5 : Fin 38) 11 a.stacks⟩ : Data) =
      state (readRegs r0 0 1 none) X bank width target modulus unit D I support [false] unit [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state,a,StackRoutines.copyStacks]
  have h1 : Eval (.call (StackRoutines.copyProgram 5 11 12 (0 : Fin 8) 1))
      (7*unit.length+5) a
      ⟨readRegs a.regs 0 1 none,StackRoutines.copyStacks (5 : Fin 38) 11 a.stacks⟩ :=
    Eval.call _ hc
  rw [he] at h1
  have h := Eval.seq h0 h1
  have hcost : 2 + (7 * unit.length + 5) = 7 * unit.length + 7 := by omega
  rw [hcost] at h
  exact h

theorem gather_eval {D : ℕ} (r : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (width target modulus unit suffix acc : Word) (I : ℕ)
    (hwidth : ∀ i, (coordinates i).length = width.length)
    (hpad : width.length ≤ target.length) (support : List (Fin D)) :
    ∃ n rf records, n ≤ 4+SubexpWeightGather.supportBudget a width target support ∧
      List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support.reverse records ∧
      Eval gather n
        (state r (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
          width target modulus unit D I
          (Encoding.encodeList id (SubexpWeightGather.supportBits support)++suffix) [false] acc [])
        (state rf (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
          width target modulus unit D I suffix (SubexpWeightControl.encodeRecords records) acc []) := by
  obtain ⟨rf,records,hgood,⟨n,hn,ht⟩⟩ :=
    SubexpWeightGather.program_runs r a coordinates width target suffix [] hwidth hpad support
  let d := state r (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
    width target modulus unit D I
    (Encoding.encodeList id (SubexpWeightGather.supportBits support)++suffix) [false] acc []
  have h := eval_call_lifted SubexpWeightGather.program id gatherPorts d
    Function.injective_id gatherPorts_injective ht
  simp only [d,List.append_nil,SubexpWeightControl.encodeRecords,embed_gather] at h
  exact ⟨n,_,records,hn,hgood,h⟩

theorem literal_eval (r : Fin 8 → Bool) (X bank width target modulus unit suffix : Word)
    (D : ℕ) (records : List SubexpWeightControl.WeightRecord)
    (hunit : unit.length = target.length)
    (hb : ∀ r ∈ records, r.base.length = target.length)
    (hmLength : modulus.length ≤ target.length+1)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2^target.length) :
    ∃ n rf output,
      n ≤ SubexpWeightControl.scanSteps target.length records+2+
        SubexpWeightLiteralProgram.overhead D target.length ∧
      Eval literal n
        (state r X bank width target modulus unit D (SubexpSymbolicCost.indexBits D) suffix
          (SubexpWeightControl.encodeRecords records) unit [])
        (state rf X bank width target modulus unit D (SubexpSymbolicCost.indexBits D) suffix [] []
          (SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticMarshal.marshalBits output target))) ∧
      output.length = target.length ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat unit : ZMod (BinaryArithmetic.toNat modulus)) *
          SubexpWeightControl.recordsValue (BinaryArithmetic.toNat modulus) records := by
  obtain ⟨rf,output,⟨n,hn,ht⟩,hlen,hvalue⟩ := SubexpWeightLiteralProgram.program_execute
    records r unit modulus [] target target.length D hunit rfl hb hmLength hm hcapacity
  simp only [List.append_nil] at ht
  let d := state r X bank width target modulus unit D (SubexpSymbolicCost.indexBits D) suffix
    (SubexpWeightControl.encodeRecords records) unit []
  have h := eval_call_lifted SubexpWeightLiteralProgram.program id literalPorts d
    Function.injective_id literalPorts_injective ht
  simp only [d,embed_literal] at h
  exact ⟨n,rf,output,hn,h,hlen,hvalue⟩

theorem goodRecords_value {D : ℕ} (m : ℕ) (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (target : Word) (support : List (Fin D))
    (records : List SubexpWeightControl.WeightRecord)
    (hgood : List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support records)
    (hwidth : ∀ i, (coordinates i).length ≤ target.length) :
    SubexpWeightControl.recordsValue m records =
      (support.map (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod m)^a i)).prod := by
  induction hgood with
  | nil => rfl
  | @cons i r support records h hr ih =>
      simp only [SubexpWeightControl.recordsValue,List.map_cons,List.prod_cons] at *
      rw [ih]
      congr 1
      simp only [SubexpWeightControl.recordValue,h.2.2.1,
        SubexpWeightGather.GoodRecord.base_value h (hwidth i)]

theorem goodRecords_lengths {D : ℕ} (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (target : Word) (support : List (Fin D))
    (records : List SubexpWeightControl.WeightRecord)
    (hgood : List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support records) :
    ∀ r ∈ records, r.base.length = target.length := by
  induction hgood with
  | nil => simp
  | @cons i r support records h hr ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h.base_length
      · exact ih q hq

theorem goodRecords_members {D : ℕ} (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (target : Word) (support : List (Fin D))
    (records : List SubexpWeightControl.WeightRecord)
    (hgood : List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support records) :
    ∀ r ∈ records, ∃ i ∈ support, SubexpWeightGather.GoodRecord a coordinates target i r := by
  induction hgood with
  | nil => simp
  | @cons i r support records h hr ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨i,by simp,h⟩
      · obtain ⟨j,hj,hgood⟩ := ih q hq
        exact ⟨j,by simp [hj],hgood⟩

theorem goodRecords_exponentTotal {D : ℕ} (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (target : Word) (support : List (Fin D))
    (records : List SubexpWeightControl.WeightRecord)
    (hgood : List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support records) :
    SubexpWeightControl.exponentTotal records = (support.map a).sum := by
  induction hgood with
  | nil => rfl
  | @cons i r support records h hr ih =>
      simp only [SubexpWeightControl.exponentTotal,List.map_cons,List.sum_cons] at *
      rw [h.2.2.1,ih]

def retainedWeightBudget (D B : ℕ) : ℕ :=
  (2*D+1)*(6010*(B+1)^2+16*(2*D+1)+16) +
    D*(5*D+8*B+24*(2*D+1)+37)+3

theorem goodRecords_scan_bound {D : ℕ} (B : ℕ) (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (target : Word) (support : List (Fin D))
    (records : List SubexpWeightControl.WeightRecord)
    (hgood : List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support records)
    (hn : support.Nodup) (hdegree : (∑ i, a i) ≤ 2*D+1) :
    SubexpWeightControl.scanSteps B records+2 ≤ retainedWeightBudget D B := by
  apply SubexpWeightControl.retained_scanSteps_le
  · rw [←hgood.length_eq]
    simpa using hn.length_le_card
  · rw [goodRecords_exponentTotal a coordinates target support records hgood]
    have hsum : (support.map a).sum ≤ ∑ i, a i := by
      rw [←List.sum_toFinset a hn]
      exact Finset.sum_le_sum_of_subset support.toFinset.subset_univ
    exact hsum.trans hdegree
  · intro r hr
    obtain ⟨i,hi,h⟩ := goodRecords_members a coordinates target support records hgood r hr
    rw [h.1,List.length_replicate]
    exact i.isLt.le
  · intro r hr
    obtain ⟨i,hi,h⟩ := goodRecords_members a coordinates target support records hgood r hr
    exact h.2.2.2.trans (SubexpWeightCode.retained_exponent_le a hdegree i)

/-- The first actual producer from X and a support/point descriptor, with no
caller-supplied weight or exponent-field bytes. The record witness is exposed
to retain the precise measured arithmetic bound. -/
theorem program_execute {D : ℕ} (r : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → Word) (width target modulus unit suffix : Word)
    (support : List (Fin D)) (hn : support.Nodup)
    (hwidth : ∀ i, (coordinates i).length = width.length)
    (hpad : width.length ≤ target.length) (hunit : unit.length = target.length)
    (hunitValue : (BinaryArithmetic.toNat unit : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hmLength : modulus.length ≤ target.length+1)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2^target.length) :
    ∃ rf output records,
      List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates target) support.reverse records ∧
      RunsIn program
        (7*target.length+12+SubexpWeightGather.supportBudget a width target support+
          SubexpWeightControl.scanSteps target.length records+2+
          SubexpWeightLiteralProgram.overhead D target.length)
        ((state r (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
          width target modulus unit D (SubexpSymbolicCost.indexBits D)
          (Encoding.encodeList id (SubexpWeightGather.supportBits support)++suffix) [] [] []).withPC
          (some program.entry))
        ((state rf (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
          width target modulus unit D (SubexpSymbolicCost.indexBits D) suffix [] []
          (SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticMarshal.marshalBits output target))).withPC none) ∧
      output.length = target.length ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  let X := SymbolicCost.unaryWords (List.ofFn a)
  let bank := (List.ofFn coordinates).flatten
  let supp := Encoding.encodeList id (SubexpWeightGather.supportBits support)++suffix
  let r1 := readRegs (Function.update r 0 false) 0 1 none
  have hi := setup_eval r X bank width target modulus unit D (SubexpSymbolicCost.indexBits D) supp
  obtain ⟨ng,rg,records,hng,hgood,hg⟩ := gather_eval r1 a coordinates width target modulus unit
    suffix unit (SubexpSymbolicCost.indexBits D) hwidth hpad support
  obtain ⟨nl,rf,output,hnl,hl,hlen,hvalue⟩ := literal_eval rg X bank width target modulus unit suffix
    D records hunit (goodRecords_lengths a coordinates target _ records hgood) hmLength hm hcapacity
  have ht := StructuredCalls.compiled_halt_trace (Eval.seq hi (Eval.seq hg hl)) 8 9
  refine ⟨rf,output,records,hgood,⟨_,?_,ht⟩,hlen,?_⟩
  · rw [hunit] at hi
    omega
  · rw [hvalue,hunitValue,one_mul,goodRecords_value _ _ _ _ _ _ hgood
      (fun i => (hwidth i).trans_le hpad)]
    rw [List.map_reverse,List.prod_reverse]
    exact (List.prod_toFinset _ hn).symm

end SubexponentialSAT.SubexpWeightDescriptorProgram

end OAI.Algorithms
