import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBankPred
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCrudeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationUnary

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def quotientPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    LeafParameterArithmetic.QuotientPorts 77 where
  left := port a
  right := port b
  out := port o
  work := work 6 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_left := fun i => work_ne_port 6 (by decide) i a
  work_ne_right := fun i => work_ne_port 6 (by decide) i b
  work_ne_out := fun i => work_ne_port 6 (by decide) i o

abbrev quotientCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  LeafParameterArithmetic.quotientAt (quotientPorts a b o hoa hob)

theorem quotient_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) (hp : 0 < BinaryArithmetic.toNat (w b)) :
    ∃ t rf word, Eval (quotientCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) / BinaryArithmetic.toNat (w b) ∧
      word.length = (w a).length ∧
      t  ≤  150*((w a).length+(w b).length+1)^2 := by
  have hv : LeafParameterArithmetic.QuotientReady (quotientPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [quotientPorts,state_port] using ho
    · intro i
      exact state_work r w _ (by change 64 ≤ 64 + i.val; omega)
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := LeafParameterArithmetic.quotientAt_eval
    (quotientPorts a b o hoa hob) (state r w) hv (by simpa [quotientPorts] using hp)
  exact ⟨t,rf,word,by simpa only [quotientCmd,quotientPorts,state_update] using he,
    by simpa only [quotientPorts,state_port] using hv,
    by simpa only [quotientPorts,state_port] using hl,
    by simpa only [quotientPorts,state_port] using ht⟩

def sqrtPorts (a o : Fin 64) (hoa : o ≠ a) : LeafParameterArithmetic.SqrtPorts 77 where
  input := port a
  out := port o
  work := work 13 (by decide)
  out_ne_input := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  work_ne_input := fun i => work_ne_port 13 (by decide) i a
  work_ne_out := fun i => work_ne_port 13 (by decide) i o

abbrev sqrtCmd (a o : Fin 64) (hoa : o ≠ a) : Cmd 8 77 :=
  LeafParameterArithmetic.sqrtAt (sqrtPorts a o hoa)

theorem sqrt_eval (r : Regs) (w : Words) (a o : Fin 64) (hoa : o ≠ a) (ho : w o = []) :
    ∃ t rf word, Eval (sqrtCmd a o hoa) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (w a)) ∧ word.length  ≤  BinaryArithmetic.toNat (w a) ∧
      t  ≤  200001*(BinaryArithmetic.toNat (w a)+(w a).length+2)^3 := by
  have hv : LeafParameterArithmetic.SqrtReady (sqrtPorts a o hoa) (state r w) := by
    constructor
    · simpa only [sqrtPorts,state_port] using ho
    · intro i
      exact state_work r w _ (by change 64 ≤ 64 + i.val; omega)
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ :=
    LeafParameterArithmetic.sqrtAt_eval (sqrtPorts a o hoa) (state r w) hv
  exact ⟨t,rf,word,by simpa only [sqrtCmd,sqrtPorts,state_update] using he,
    by simpa only [sqrtPorts,state_port] using hv,
    by simpa only [sqrtPorts,state_port] using hl,
    by simpa only [sqrtPorts,state_port] using ht⟩

abbrev copyCmd (a o : Fin 64) : Cmd 8 77 :=
  ArithmeticCalls.copyAt (port a) (port o) (work 1 (by decide) 0)

theorem copy_eval (r : Regs) (w : Words) (a o : Fin 64) (hoa : o ≠ a) (ho : w o = []) :
    ∃ rf, Eval (copyCmd a o) (7*(w a).length+5) (state r w)
        (state rf (Function.update w o (w a))) := by
  have hh := ArithmeticCalls.copyAt_eval (port a) (port o) (work 1 (by decide) 0) (state r w)
    (by intro h; exact hoa ((Fin.castAdd_injective 64 13) h.symm))
    (work_ne_port 1 (by decide) 0 a).symm
    (work_ne_port 1 (by decide) 0 o)
    (by simpa using ho) (state_work r w _ (by simp [work]))
  refine ⟨(ArithmeticCalls.afterCopy (port a) (port o) (state r w)).regs,?_⟩
  simp only [ArithmeticCalls.afterCopy] at hh
  rw [state_update] at hh
  simpa only [copyCmd, ArithmeticCalls.afterCopy, state_port] using hh

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatch -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic
abbrev Data := StructuredProgram.State 9 20

def regs : Fin 8 → Fin 9 := Fin.castAdd 1

def pair (j : Fin 10) (h : Fin 2) : Fin 20 := ⟨2*j.val+h.val,by omega⟩

theorem regs_injective : Function.Injective regs := Fin.castAdd_injective _ _
theorem pair_injective (j : Fin 10) : Function.Injective (pair j) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp [pair] at this; omega

theorem pair_separate {j k : Fin 10} (hjk : j ≠ k) (i : Fin 2) :
    ¬ ∃ h, pair j h = pair k i := by
  rintro ⟨h,he⟩
  have hv := congrArg Fin.val he
  apply hjk
  apply Fin.ext
  dsimp [pair] at hv
  have := h.isLt
  have := i.isLt
  omega

abbrev check (j : Fin 10) : StructuredCalls.Cmd 9 20 :=
  .seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program regs (pair j)))
    (.base (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))))

def cost (j : Fin 10) (d : Data) : ℕ :=
  10 * max (d.stacks (pair j 0)).length (d.stacks (pair j 1)).length + 8

def pass (j : Fin 10) (d : Data) : Bool :=
  decide (BinaryArithmetic.toNat (d.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (d.stacks (pair j 0)))

theorem check_eval (j : Fin 10) (a : Data) :
    ∃ b, StructuredCalls.Eval (check j) (cost j a) a b ∧
      b.regs 8 = (a.regs 8 && pass j a) ∧
      (∀ i, (¬ ∃ h, pair j h = i) → b.stacks i = a.stacks i) ∧
      (∀ h, b.stacks (pair j h) = []) := by
  obtain ⟨mid,hr,hcmp,hregs,hframe,hclear⟩ :=
    SubexpGuardProgram.compare_call regs (pair j) regs_injective (pair_injective j) a
  let inv := (Atom.bnot (0 : Fin 9) 0).eval mid
  let b := (Atom.band (8 : Fin 9) 8 0).eval inv
  have hb : StructuredProgram.Eval (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))) 2 mid b :=
    .seq (.atom _ _) (.atom _ _)
  have hnot : ¬ ∃ i, regs i = (8 : Fin 9) := by
    rintro ⟨i,hi⟩; have := congrArg Fin.val hi; have := i.isLt; dsimp [regs] at *; omega
  have hacc := hregs 8 hnot
  have hbool : (!mid.regs 0) = pass j a := by
    change mid.regs 0 = true ↔ _ at hcmp
    cases hm : mid.regs 0 with
    | false =>
      have hle : BinaryArithmetic.toNat (a.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (a.stacks (pair j 0)) := by
        have hn : ¬ BinaryArithmetic.toNat (a.stacks (pair j 0)) < BinaryArithmetic.toNat (a.stacks (pair j 1)) := by
          simpa [hm] using hcmp.symm
        omega
      simp [pass,hle]
    | true =>
      have hle : ¬ BinaryArithmetic.toNat (a.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (a.stacks (pair j 0)) := by
        have := hcmp.mp hm; omega
      simp [pass,hle]
  refine ⟨b,?_,?_,hframe,hclear⟩
  · simpa only [check,cost,Nat.add_assoc] using hr.seq (StructuredCalls.Eval.base hb)
  · simp [b,inv,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,execInstr,hacc,hbool]

/-- The list is fixed syntax; in the final guard it has exactly ten entries. -/
def checks : List (Fin 10) → StructuredCalls.Cmd 9 20
  | [] => .base .skip
  | j::js => .seq (check j) (checks js)

def checksCost (js : List (Fin 10)) (d : Data) : ℕ := (js.map (fun j => cost j d)).sum
def checksPass (js : List (Fin 10)) (d : Data) : Bool := js.all (fun j => pass j d)

theorem checks_eval (js : List (Fin 10)) (hn : js.Nodup) (a : Data) :
    ∃ b, StructuredCalls.Eval (checks js) (checksCost js a) a b ∧
      b.regs 8 = (a.regs 8 && checksPass js a) ∧
      (∀ j, j ∉ js → ∀ h, b.stacks (pair j h) = a.stacks (pair j h)) ∧
      (∀ j, j ∈ js → ∀ h, b.stacks (pair j h) = []) := by
  induction js generalizing a with
  | nil => exact ⟨a,.base (.skip _),by simp [checksPass],by simp,by simp⟩
  | cons j js ih =>
    obtain ⟨mid,he,hacc,hframe,hclear⟩ := check_eval j a
    obtain ⟨b,her,hracc,hrframe,hrclear⟩ := ih (List.nodup_cons.mp hn).2 mid
    have hv (k : Fin 10) (hk : k ∈ js) :
        cost k mid = cost k a ∧ pass k mid = pass k a := by
      have hjk : j ≠ k := by intro h; subst k; exact (List.nodup_cons.mp hn).1 hk
      have h0 := hframe (pair k 0) (pair_separate hjk 0)
      have h1 := hframe (pair k 1) (pair_separate hjk 1)
      simp only [cost,pass,h0,h1,and_self]
    have hc : checksCost js mid = checksCost js a := by
      unfold checksCost
      congr 1
      apply List.map_congr_left
      intro k hk
      exact (hv k hk).1
    have hp : checksPass js mid = checksPass js a := by
      unfold checksPass
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro hh k hk
        rw [← (hv k hk).2]
        exact hh k hk
      · intro hh k hk
        rw [(hv k hk).2]
        exact hh k hk
    refine ⟨b,?_,?_,?_,?_⟩
    · rw [hc] at her
      simpa only [checks,checksCost,List.map_cons,List.sum_cons] using he.seq her
    · rw [hracc,hacc,hp]
      simp [checksPass,Bool.and_assoc]
    · intro k hk h
      have hkj : k ≠ j := by intro he; subst k; exact hk (by simp)
      have hkjs : k ∉ js := by intro h; exact hk (List.mem_cons_of_mem j h)
      exact (hrframe k hkjs h).trans (hframe _ (pair_separate hkj.symm h))
    · intro k hk h
      rcases List.mem_cons.mp hk with rfl|hk
      · exact (hrframe k (List.nodup_cons.mp hn).1 h).trans (hclear h)
      · exact hrclear k hk h

def allChecks : List (Fin 10) := List.finRange 10

abbrev command : StructuredCalls.Cmd 9 20 :=
  .seq (.base (.atom (.set 8 true))) (checks allChecks)

def upperFor (x : Input) (p : Parameters) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 => x.freeCount
  | 1 => x.ambient
  | 2 => x.clauses
  | 3 => x.occurrence
  | 4 => x.arity
  | 5 => x.incidences
  | 6 | 7 => p.Q
  | 8 => x.incidences
  | _ => x.freeCount

def lowerFor (x : Input) (p : Parameters) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 | 2 | 3 | 4 => 1
  | 1 | 5 => x.freeCount
  | 6 => 2
  | 7 => 4*p.R
  | 8 => 4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2
  | _ => 16*p.Q*p.r^2

def upper (x : Input) := upperFor x (produce x)
def lower (x : Input) := lowerFor x (produce x)

def Encodes (x : Input) (a : Data) : Prop :=
  ∀ j, BinaryArithmetic.toNat (a.stacks (pair j 0)) = upper x j ∧
    BinaryArithmetic.toNat (a.stacks (pair j 1)) = lower x j

theorem command_eval (a : Data) :
    ∃ b, StructuredCalls.Eval command (1+checksCost allChecks a) a b ∧
      b.regs 8 = checksPass allChecks a := by
  let a0 := (Atom.set (8 : Fin 9) true).eval a
  obtain ⟨b,he,hacc,hframe,hclear⟩ := checks_eval allChecks (List.nodup_finRange 10) a0
  refine ⟨b,?_,?_⟩
  · exact (StructuredCalls.Eval.base (.atom _ _)).seq he
  · simpa [a0,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,
      checksPass,pass] using hacc

private theorem forall_ten (P : Fin 10 → Prop) :
    (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3,h 4,h 5,h 6,h 7,h 8,h 9⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9

private theorem numeric_guard_for (x : Input) (p : Parameters) :
    (∀ j : Fin 10, lowerFor x p j  ≤  upperFor x p j) ↔
      (0 < x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 0 < x.clauses ∧
       0 < x.occurrence ∧ 0 < x.arity ∧ x.freeCount ≤ x.incidences ∧
       2 ≤ p.Q ∧ 4*p.R ≤ p.Q ∧
       4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2 ≤ x.incidences ∧
       16*p.Q*p.r^2 ≤ x.freeCount) := by
  rw [forall_ten]
  change (1 ≤ x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 1 ≤ x.clauses ∧
    1 ≤ x.occurrence ∧ 1 ≤ x.arity ∧ x.freeCount ≤ x.incidences ∧
    2 ≤ p.Q ∧ 4*p.R ≤ p.Q ∧
    4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2 ≤ x.incidences ∧
    16*p.Q*p.r^2 ≤ x.freeCount) ↔ _
  exact and_congr Nat.succ_le_iff (and_congr Iff.rfl
    (and_congr Nat.succ_le_iff (and_congr Nat.succ_le_iff
      (and_congr Nat.succ_le_iff Iff.rfl))))

theorem numeric_guard_iff (x : Input) :
    (∀ j : Fin 10, lower x j  ≤  upper x j) ↔ Guard x :=
  numeric_guard_for x (produce x)

theorem checksPass_numeric (x : Input) (a : Data) (h : Encodes x a) :
    checksPass allChecks a = true ↔ ∀ j : Fin 10, lower x j  ≤  upper x j := by
  simp only [checksPass,List.all_eq_true,allChecks,List.mem_finRange,forall_true_left,pass,
    decide_eq_true_eq]
  exact forall_congr' (fun j => by rw [(h j).1,(h j).2])

theorem checksPass_iff (x : Input) (a : Data) (h : Encodes x a) :
    checksPass allChecks a = true ↔ Guard x :=
  (checksPass_numeric x a h).trans (numeric_guard_iff x)

/-- Both continuations are real structured commands. The selected branch is
charged after all ten comparisons, including failed fast-path guards. -/
abbrev dispatchCommand (yes no : StructuredCalls.Cmd 9 20) : StructuredCalls.Cmd 9 20 :=
  .seq command (.ite 8 yes no)

theorem dispatch_eval (x : Input) (a : Data) (h : Encodes x a)
    (yes no : StructuredCalls.Cmd 9 20) :
    ∃ mid, (mid.regs 8 = true ↔ Guard x) ∧
      ∀ m b, StructuredCalls.Eval (if passes x then yes else no) m mid b →
        StructuredCalls.Eval (dispatchCommand yes no)
          (1+checksCost allChecks a+(m+1)) a b := by
  obtain ⟨mid,he,hbit⟩ := command_eval a
  have hb : mid.regs 8 = passes x := by
    apply Bool.eq_iff_iff.mpr
    rw [hbit,checksPass_iff x a h,passes_eq_true]
  refine ⟨mid,by rw [hb,passes_eq_true],?_⟩
  intro m b hrun
  apply he.seq
  cases hx : passes x with
  | false => exact StructuredCalls.Eval.ite_false (hb.trans hx) (by simpa [hx] using hrun)
  | true => exact StructuredCalls.Eval.ite_true (hb.trans hx) (by simpa [hx] using hrun)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

/-- A finite arithmetic instruction table. All natural-number fields in this
type are code constants or physical port indices. Operand values reside in
Boolean stacks and are read by the concrete routines in `command`. -/
inductive Instr where
  | clear (a : Fin 64)
  | load (o : Fin 64) (bits : List Bool)
  | copy (a o : Fin 64) (h : o ≠ a)
  | add (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | mul (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | pow (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | quot (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | sqrt (a o : Fin 64) (h : o ≠ a)
  | logSucc (a : Fin 64)
  | addConst (a : Fin 64) (k : ℕ)
  | pred (a : Fin 64)
  | maxTwo (a : Fin 64)

def output : Instr → Fin 64
  | .clear a => a
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .quot _ _ o _ _ | .sqrt _ o _ => o
  | .logSucc a | .addConst a _ | .pred a | .maxTwo a => a

def command : Instr → Cmd 8 77
  | .clear a => ArithmeticExpressionSupport.clearCmd (port a)
  | .load o bits => loadCmd o bits
  | .copy a o _ => copyCmd a o
  | .add a b o ha hb => addCmd a b o ha hb
  | .mul a b o ha hb => multiplyCmd a b o ha hb
  | .pow a b o ha hb => powerCmd a b o ha hb
  | .quot a b o ha hb => quotientCmd a b o ha hb
  | .sqrt a o h => sqrtCmd a o h
  | .logSucc a => logSuccCmd a
  | .addConst a k => addConstCmd a k
  | .pred a => predCmd a
  | .maxTwo a => maxTwoCmd a

def value (v : Fin 64 → ℕ) : Instr → ℕ
  | .clear _ => 0
  | .load _ bits => BinaryArithmetic.toNat bits
  | .copy a _ _ => v a
  | .add a b _ _ _ => v a + v b
  | .mul a b _ _ _ => v a * v b
  | .pow a b _ _ _ => v a ^ v b
  | .quot a b _ _ _ => v a / v b
  | .sqrt a _ _ => Nat.sqrt (v a)
  | .logSucc a => Nat.log2 (v a)+1
  | .addConst a k => v a+k
  | .pred a => v a-1
  | .maxTwo a => max 2 (v a)

def lengthBound (v l : Fin 64 → ℕ) : Instr → ℕ
  | .clear _ => 0
  | .load _ bits => bits.length
  | .copy a _ _ => l a
  | .add a b _ _ _ | .mul a b _ _ _ => l a+l b+1
  | .pow a b _ _ _ => 1+v b*l a
  | .quot a _ _ _ _ => l a
  | .sqrt a _ _ => v a
  | .logSucc a => l a+1
  | .addConst a k => l a+k
  | .pred a => l a
  | .maxTwo a => l a+2

def cost (v l : Fin 64 → ℕ) : Instr → ℕ
  | .clear a => 2*l a+3
  | .load _ bits => 2*bits.length
  | .copy a _ _ => 7*l a+5
  | .add a b _ _ _ | .mul a b _ _ _ => 100*(l a+l b+1)^2
  | .pow a b _ _ _ => v b*(50*(l a+1)*(2+(v b+1)*l a))+
      (v b+1)*(16*l b+16)+3+9*l b+8
  | .quot a b _ _ _ => 150*(l a+l b+1)^2
  | .sqrt a _ _ => 200001*(v a+l a+2)^3
  | .logSucc a => 32*(l a+1)^2+4
  | .addConst a k => 8*k*(l a+k+1)+4
  | .pred a => 20*(l a+1)
  | .maxTwo a => 100*(l a+3)

def Ready (w : Words) : Instr → Prop
  | .clear _ => True
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .sqrt _ o _ => w o=[]
  | .quot _ b o _ _ => w o=[] ∧ 0 < BinaryArithmetic.toNat (w b)
  | .logSucc _ | .addConst _ _ | .pred _ | .maxTwo _ => True

def values (w : Words) (a : Fin 64) := BinaryArithmetic.toNat (w a)
def lengths (w : Words) (a : Fin 64) := (w a).length

/-- Uniform exact semantic and physical-cost contract, discharged by the
concrete Boolean-stack routines for every instruction constructor. -/
theorem instruction_eval (i : Instr) (r : Regs) (w : Words) (h : Ready w i) :
    ∃ t rf word, Eval (command i) t (state r w)
        (state rf (Function.update w (output i) word)) ∧
      BinaryArithmetic.toNat word = value (values w) i ∧ word.length  ≤  lengthBound (values w) (lengths w) i ∧
      t  ≤  cost (values w) (lengths w) i := by
  cases i with
  | clear a =>
    have he := ArithmeticExpressionSupport.clear_eval (port a) (state r w)
    refine ⟨2*(w a).length+3,readRegs r 0 1 none,[],?_,rfl,le_rfl,le_rfl⟩
    rw [state_update] at he
    have hr : (state r w).regs = r := rfl
    rw [hr] at he
    simpa only [command, output, state_port] using he
  | load o bits =>
    obtain ⟨rf,he⟩ := load_eval r w o bits h
    exact ⟨2*bits.length,rf,bits,he,rfl,le_rfl,le_rfl⟩
  | copy a o ha =>
    obtain ⟨rf,he⟩ := copy_eval r w a o ha h
    exact ⟨7*(w a).length+5,rf,w a,he,rfl,le_rfl,le_rfl⟩
  | add a b o ha hb => exact add_eval r w a b o ha hb h
  | mul a b o ha hb => exact multiply_eval r w a b o ha hb h
  | pow a b o ha hb =>
    obtain ⟨t,rf,word,he,hv,hl,ht⟩ := power_eval r w a b o ha hb h
    refine ⟨t,rf,word,he,hv,hl,?_⟩
    simpa only [cost,values,lengths,PowerPrograms.runtimeBound,PowerPrograms.workBound,PowerPrograms.callbackBound,
      CounterPrograms.value_eq_toNat] using ht
  | quot a b o ha hb =>
    obtain ⟨t,rf,word,he,hv,hl,ht⟩ := quotient_eval r w a b o ha hb h.1 h.2
    exact ⟨t,rf,word,he,hv,hl.le,ht⟩
  | sqrt a o ha => exact sqrt_eval r w a o ha h
  | logSucc a => exact logSucc_eval r w a
  | addConst a k => exact addConst_eval r w a k
  | pred a => exact pred_eval r w a
  | maxTwo a => exact maxTwo_eval r w a

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

structure Model where
  val : Fin 64 → ℕ
  len : Fin 64 → ℕ

def Shape (m : Model) (w : Words) : Prop :=
  (∀ a, BinaryArithmetic.toNat (w a)=m.val a) ∧ (∀ a, (w a).length ≤ m.len a)

def next (m : Model) (i : Instr) : Model :=
  ⟨Function.update m.val (output i) (value m.val i),
   Function.update m.len (output i) (lengthBound m.val m.len i)⟩

def Admissible (m : Model) : Instr → Prop
  | .clear _ => True
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .sqrt _ o _ => m.len o=0
  | .quot _ b o _ _ => m.len o = 0 ∧ 0 < m.val b
  | .logSucc _ | .addConst _ _ | .pred _ | .maxTwo _ => True

theorem lengthBound_mono (v l l' : Fin 64 → ℕ) (h : ∀ a, l a ≤ l' a) (i : Instr) :
    lengthBound v l i ≤ lengthBound v l' i := by
  cases i <;> simp only [lengthBound]
  all_goals first | exact le_rfl | apply h | (gcongr <;> apply h)

theorem cost_mono (v l l' : Fin 64 → ℕ) (h : ∀ a, l a ≤ l' a) (i : Instr) :
    cost v l i ≤ cost v l' i := by
  cases i <;> simp only [cost]
  all_goals first | exact le_rfl | apply h | (gcongr <;> apply h)

theorem shape_ready (m : Model) (w : Words) (hs : Shape m w) (i : Instr)
    (hi : Admissible m i) : Ready w i := by
  have hz (a : Fin 64) (ha : m.len a = 0) : w a = [] := by
    have hh := hs.2 a
    rw [ha] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  cases i with
  | clear => trivial
  | load o _ => exact hz o hi
  | copy _ o _ => exact hz o hi
  | add _ _ o _ _ => exact hz o hi
  | mul _ _ o _ _ => exact hz o hi
  | pow _ _ o _ _ => exact hz o hi
  | quot _ b o _ _ =>
      exact ⟨hz o hi.1, by rw [hs.1]; exact hi.2⟩
  | sqrt _ o _ => exact hz o hi
  | logSucc => trivial
  | addConst => trivial
  | pred => trivial
  | maxTwo => trivial

theorem instruction_shape (m : Model) (w : Words) (r : Regs) (hs : Shape m w)
    (i : Instr) (hi : Admissible m i) :
    ∃ t rf w', Eval (command i) t (state r w) (state rf w') ∧
      Shape (next m i) w' ∧ t ≤ cost m.val m.len i := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := instruction_eval i r w (shape_ready m w hs i hi)
  have hval : values w=m.val := funext hs.1
  rw [hval] at hv hl ht
  have hl' := hl.trans (lengthBound_mono m.val (lengths w) m.len hs.2 i)
  have ht' := ht.trans (cost_mono m.val (lengths w) m.len hs.2 i)
  refine ⟨t,rf,Function.update w (output i) word,he,⟨?_,?_⟩,ht'⟩
  · intro a
    by_cases ha : a=output i
    · subst a; simpa [next] using hv
    · simpa [next,ha] using hs.1 a
  · intro a
    by_cases ha : a=output i
    · subst a; simpa [next] using hl'
    · simpa [next,ha] using hs.2 a

def program : List Instr → Cmd 8 77
  | [] => .base .skip
  | i::is => .seq (command i) (program is)

def result : List Instr → Model → Model
  | [],m => m
  | i::is,m => result is (next m i)

def budget : List Instr → Model → ℕ
  | [],_ => 0
  | i::is,m => cost m.val m.len i+budget is (next m i)

def AdmissibleCode : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => Admissible m i ∧ AdmissibleCode is (next m i)

/-- Execute a fixed finite arithmetic circuit. Its returned bound includes
all arithmetic, copying, and every nested loop in the concrete primitives. -/
theorem program_eval (is : List Instr) (m : Model) (w : Words) (r : Regs)
    (hs : Shape m w) (hi : AdmissibleCode is m) :
    ∃ t rf w', Eval (program is) t (state r w) (state rf w') ∧
      Shape (result is m) w' ∧ t ≤ budget is m := by
  induction is generalizing m w r with
  | nil => exact ⟨0,r,w,.base (.skip _),hs,le_rfl⟩
  | cons i is ih =>
    obtain ⟨t,rf,w',he,hs',ht⟩ := instruction_shape m w r hs i hi.1
    obtain ⟨u,rg,w'',hf,hs'',hu⟩ := ih (next m i) w' rf hs' hi.2
    exact ⟨t+u,rg,w'',he.seq hf,hs'',Nat.add_le_add ht hu⟩

/-- Values in ports untouched by the table are preserved exactly. -/
theorem result_value_frame (is : List Instr) (m : Model) (a : Fin 64)
    (ha : ∀ i ∈ is, output i≠a) : (result is m).val a=m.val a := by
  induction is generalizing m with
  | nil => rfl
  | cons i is ih =>
    rw [result,ih (next m i) (fun j hj => ha j (List.mem_cons_of_mem i hj))]
    simp [next,Ne.symm (ha i (List.mem_cons_self))]

@[simp] theorem result_append (xs ys : List Instr) (m : Model) :
    result (xs++ys) m=result ys (result xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih (next m x)

@[simp] theorem budget_append (xs ys : List Instr) (m : Model) :
    budget (xs++ys) m=budget xs m+budget ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [budget,result]
  | cons x xs ih => simp [budget,result,ih,Nat.add_assoc]

@[simp] theorem admissibleCode_append (xs ys : List Instr) (m : Model) :
    AdmissibleCode (xs++ys) m ↔ AdmissibleCode xs m ∧ AdmissibleCode ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [AdmissibleCode,result]
  | cons x xs ih => simp [AdmissibleCode,result,ih,and_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Low eight slots hold ambient n, residual n, original clause count, actual
occurrence bound, maximum arity, full factor count (hash+marked+neutral),
formula width, and total incidences.
The remaining finite table is straight-line syntax, not an input oracle. -/
abbrev earlyCode : List Instr := [
  .load 8 [false,true],
  .load 9 [true,true],
  .load 10 [false,false,false,false,false,true],
  .load 11 [false,false,false,false,false,false,true],
  .load 12 [false,false,false,false,false,false,false,true],
  .copy 1 13 (by decide), .addConst 13 16, .logSucc 13,
  .copy 13 14 (by decide), .logSucc 14,
  .mul 14 14 15 (by decide) (by decide),
  .sqrt 13 16 (by decide),
  .quot 16 15 17 (by decide) (by decide),
  .copy 17 18 (by decide), .maxTwo 18]

abbrev quotientCode : List Instr := [
  .copy 18 19 (by decide), .logSucc 19,
  .mul 11 19 20 (by decide) (by decide),
  .quot 13 20 21 (by decide) (by decide)]

abbrev prefixCode : List Instr := earlyCode ++ quotientCode

abbrev heavyCode : List Instr := [
  .mul 13 13 22 (by decide) (by decide),
  .mul 3 18 23 (by decide) (by decide),
  .mul 23 22 24 (by decide) (by decide),
  .mul 10 24 25 (by decide) (by decide),
  .mul 11 24 26 (by decide) (by decide), .logSucc 26,
  .mul 12 21 27 (by decide) (by decide),
  .mul 27 26 28 (by decide) (by decide),
  .sqrt 28 29 (by decide), .addConst 29 4]

abbrev powerCode : List Instr := [
  .mul 8 21 30 (by decide) (by decide),
  .pow 18 30 31 (by decide) (by decide)]

abbrev finishCode : List Instr := heavyCode ++ powerCode

def coreCode : List Instr := prefixCode ++ finishCode

def tailCode : List Instr := [
  .copy 2 32 (by decide), .logSucc 32, .addConst 32 1,
  .add 0 32 33 (by decide) (by decide),
  .copy 21 34 (by decide), .logSucc 34, .addConst 34 1,
  .pow 9 34 35 (by decide) (by decide),
  .copy 33 36 (by decide), .pred 36,
  .mul 9 36 37 (by decide) (by decide),
  .mul 8 5 38 (by decide) (by decide),
  .add 38 37 39 (by decide) (by decide), .addConst 39 1,
  .mul 6 29 40 (by decide) (by decide),
  .mul 40 39 41 (by decide) (by decide),
  .copy 21 43 (by decide), .pred 43, .addConst 43 1,
  .quot 41 43 42 (by decide) (by decide), .addConst 42 1]

def code : List Instr := coreCode ++ tailCode

abbrev command : Cmd 8 77 := Circuit.program code

def initialValues (x : Input) (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => x.ambient
  | 1 => x.freeCount
  | 2 => x.clauses
  | 3 => x.occurrence
  | 4 => x.arity
  | 5 => x.factors
  | 6 => x.width
  | 7 => x.incidences
  | _ => 0

def initialModel (x : Input) (inputLengths : Fin 8 → ℕ) : Model where
  val := initialValues x
  len i := if h : i.val < 8 then inputLengths ⟨i.val,h⟩ else 0

def model (x : Input) (inputLengths : Fin 8 → ℕ) : Model :=
  Circuit.result code (initialModel x inputLengths)

def runtimeBound (x : Input) (inputLengths : Fin 8 → ℕ) : ℕ :=
  Circuit.budget code (initialModel x inputLengths)

/-- Program-level integration contract. The next theorem discharges its
structural arithmetic readiness from the explicit table. -/
theorem command_eval (x : Input) (inputLengths : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (initialModel x inputLengths) w)
    (ha : AdmissibleCode code (initialModel x inputLengths)) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (model x inputLengths) w' ∧ t ≤ runtimeBound x inputLengths :=
  Circuit.program_eval code (initialModel x inputLengths) w r hs ha

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutReady -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Every output is fresh and every division denominator is positive for all
inputs. The final safe divisor is max(1,Q); the fast-path guard later implies
Q>=2 and hence identifies it with Q. -/
theorem admissible (x : Input) (inputLengths : Fin 8 → ℕ) :
    AdmissibleCode code (initialModel x inputLengths) := by
  simp [code,coreCode,tailCode,AdmissibleCode,Admissible,next,output,value,lengthBound,initialModel,
    initialValues,BinaryArithmetic.toNat,bitVal,Fin.coe_ofNat_eq_mod]

theorem execution (x : Input) (inputLengths : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (initialModel x inputLengths) w) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (model x inputLengths) w' ∧ t ≤ runtimeBound x inputLengths :=
  command_eval x inputLengths w r hs (admissible x inputLengths)

def program := compiled command (port 0) (port 42)

theorem program_runs (x : Input) (inputLengths : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (initialModel x inputLengths) w) :
    ∃ rf w', RunsIn program (runtimeBound x inputLengths+1)
      ((state r w).withPC (some program.entry)) ((state rf w').withPC none) ∧
      Shape (model x inputLengths) w' := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := execution x inputLengths w r hs
  exact ⟨rf,w',⟨t+1,Nat.add_le_add_right ht 1,compiled_halt_trace he (port 0) (port 42)⟩,hs'⟩

theorem primitive_execution (x : Input) (inputLengths : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (initialModel x inputLengths) w) :
    ∃ rf w', Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(runtimeBound x inputLengths+1))
      (primitiveCfg program ((state r w).withPC (some program.entry)))
      (primitiveCfg program ((state rf w').withPC none)) ∧ Shape (model x inputLengths) w' := by
  obtain ⟨rf,w',hr,hs'⟩ := program_runs x inputLengths w r hs
  exact ⟨rf,w',BitProgram.primitive_execution program hr,hs'⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutValues -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic

private theorem prefix_values (x : Input) (l : Fin 8 → ℕ) :
    (result prefixCode (initialModel x l)).val 13 = Asymptotic.L x.freeCount ∧
    (result prefixCode (initialModel x l)).val 18 = Asymptotic.layoutR x.freeCount ∧
    (result prefixCode (initialModel x l)).val 21 = Asymptotic.layoutQ x.freeCount := by
  let m := result earlyCode (initialModel x l)
  have h13 : m.val 13 = Asymptotic.L x.freeCount := by
    simp [m,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,BinaryArithmetic.toNat,bitVal]
  have h18 : m.val 18 = Asymptotic.layoutR x.freeCount := by
    simp [m,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two]
  rw [prefixCode,result_append]
  constructor
  · rw [result_value_frame quotientCode _ 13]
    · exact h13
    · decide
  constructor
  · rw [result_value_frame quotientCode _ 18]
    · exact h18
    · decide
  · simp [result,next,value,output,
      initialModel,initialValues,
      Asymptotic.layoutQ,Asymptotic.layoutDen,Asymptotic.layoutR,
      Asymptotic.s,Asymptotic.w,Asymptotic.L,pow_two]

private theorem prefix_eight (x : Input) (l : Fin 8 → ℕ) :
    (result prefixCode (initialModel x l)).val 8 = 2 := by
  rw [prefixCode,result_append]
  rw [result_value_frame quotientCode _ 8]
  · simp [result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  · decide

private theorem val_eq (x : Input) (l : Fin 8 → ℕ) :
    (model x l).val 13 = Asymptotic.L x.freeCount ∧
    (model x l).val 14 = Asymptotic.w x.freeCount ∧
    (model x l).val 17 = Asymptotic.s x.freeCount ∧
    (model x l).val 18 = Asymptotic.layoutR x.freeCount ∧
    (model x l).val 21 = Asymptotic.layoutQ x.freeCount ∧
    (model x l).val 25 = 32*x.occurrence*Asymptotic.layoutR x.freeCount*
      Asymptotic.L x.freeCount^2 ∧
    (model x l).val 29 = Asymptotic.layoutCutoff x.freeCount x.occurrence ∧
    (model x l).val 31 = Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) := by
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L, BinaryArithmetic.toNat,bitVal]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w, BinaryArithmetic.toNat,bitVal]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s, BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,Asymptotic.layoutQ,
      Asymptotic.layoutDen, BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,Asymptotic.layoutQ,
      Asymptotic.layoutDen,Asymptotic.layoutCutoff,Asymptotic.layoutEnergy,
      BinaryArithmetic.toNat,bitVal,pow_two]
    congr 1
    ring_nf
  · rw [model,code,result_append]
    rw [result_value_frame tailCode _ 31]
    · rw [coreCode,result_append]
      obtain ⟨_,hr,hq⟩ := prefix_values x l
      have h8 := prefix_eight x l
      rw [finishCode,result_append]
      have hr' : (result heavyCode (result prefixCode (initialModel x l))).val 18 =
          Asymptotic.layoutR x.freeCount := by
        rw [result_value_frame heavyCode _ 18]
        · exact hr
        · decide
      have hq' : (result heavyCode (result prefixCode (initialModel x l))).val 21 =
          Asymptotic.layoutQ x.freeCount := by
        rw [result_value_frame heavyCode _ 21]
        · exact hq
        · decide
      have h8' : (result heavyCode (result prefixCode (initialModel x l))).val 8 = 2 := by
        rw [result_value_frame heavyCode _ 8]
        · exact h8
        · decide
      let mh := result heavyCode (result prefixCode (initialModel x l))
      change mh.val 18 = Asymptotic.layoutR x.freeCount at hr'
      change mh.val 21 = Asymptotic.layoutQ x.freeCount at hq'
      change mh.val 8 = 2 at h8'
      change (result powerCode mh).val 31 =
        Asymptotic.layoutR x.freeCount ^ (2 * Asymptotic.layoutQ x.freeCount)
      simp [result,next,value,output,hr',hq',h8']
    · decide

theorem model_core_values (x : Input) (l : Fin 8 → ℕ) :
    (model x l).val 13 = (produce x).L ∧
    (model x l).val 14 = (produce x).w ∧
    (model x l).val 17 = (produce x).s ∧
    (model x l).val 18 = (produce x).r ∧
    (model x l).val 21 = (produce x).Q ∧
    (model x l).val 25 = (produce x).epsilonDen ∧
    (model x l).val 29 = (produce x).R ∧
    (model x l).val 31 = (produce x).N := val_eq x l

theorem model_inputs (x : Input) (l : Fin 8 → ℕ) (i : Fin 8) :
    (model x l).val (i.castAdd 56)=initialValues x (i.castAdd 56) := by
  fin_cases i <;> simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues]

theorem model_precision (x : Input) (l : Fin 8 → ℕ) (hm : x.clauses≠0) :
    (model x l).val 33 = (produce x).t := by
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    produce,precision,size_eq_log2_add_one hm,BinaryArithmetic.toNat,bitVal,Nat.add_assoc]

theorem model_degree (x : Input) (l : Fin 8 → ℕ) (hQ : (produce x).Q≠0) :
    (model x l).val 34 = (produce x).d := by
  have h := size_eq_log2_add_one hQ
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    produce,extensionDegree,Asymptotic.layoutQ,Asymptotic.layoutDen,
    Asymptotic.layoutR,Asymptotic.s,Asymptotic.w,Asymptotic.L,BinaryArithmetic.toNat,bitVal,
    pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at h ⊢
  omega

theorem model_fieldCard (x : Input) (l : Fin 8 → ℕ) (hQ : (produce x).Q≠0) :
    (model x l).val 35 = fieldCard x := by
  rw [fieldCard,← model_degree x l hQ]
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    BinaryArithmetic.toNat,bitVal]

theorem model_jet (x : Input) (l : Fin 8 → ℕ)
    (hm : x.clauses≠0) (hQ : (produce x).Q≠0) :
    (model x l).val 42 = (produce x).J := by
  have hpos : 1 ≤ (produce x).Q := Nat.one_le_iff_ne_zero.mpr hQ
  have hsafe := Nat.sub_add_cancel hpos
  rcases model_core_values x l with ⟨_,_,_,_,hQ',_,hR,_⟩
  have hf := model_inputs x l 5
  have hw := model_inputs x l 6
  let m₀ := result coreCode (initialModel x l)
  have h0 : m₀.val 0 = x.ambient := by
    dsimp [m₀]
    rw [result_value_frame coreCode _ 0]
    · rfl
    · decide
  have h2 : m₀.val 2 = x.clauses := by
    dsimp [m₀]
    rw [result_value_frame coreCode _ 2]
    · rfl
    · decide
  have h8 : m₀.val 8 = 2 := by
    simp [m₀,coreCode,result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  have h9 : m₀.val 9 = 3 := by
    simp [m₀,coreCode,result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  rw [model,code,result_append] at hQ' hR hf hw ⊢
  simp [tailCode,result,next,value,output] at hQ' hR hf hw ⊢
  change m₀.val 21 = _ at hQ'
  change m₀.val 29 = _ at hR
  change m₀.val 5 = _ at hf
  change m₀.val 6 = _ at hw
  change m₀.val 6 * m₀.val 29 *
      (m₀.val 8 * m₀.val 5 +
        m₀.val 9 * (m₀.val 0 + (Nat.log2 (m₀.val 2) + 1)) + 1) /
      (m₀.val 21 - 1 + 1) + 1 = (produce x).J
  rw [hQ',hR,hf,hw,h0,h2,h8,h9]
  simp [initialValues]
  rw [hsafe]
  simp [produce,precision,size_eq_log2_add_one hm]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramGuardSetup -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Materialize the twenty comparison operands. Public parameter slots and
all eight original metadata words are preserved. Reused private slots are
cleared by real stack programs before each new arithmetic result. -/
def preparation : List Instr := [
  .clear 8,
  .load 8 [true],
  .clear 9,
  .load 9 [false,true],
  .clear 10,
  .load 10 [false,false,true],
  .clear 11,
  .load 11 [false,false,false,false,true],
  .clear 12,
  .mul 31 31 12 (by decide) (by decide),
  .clear 15,
  .mul 25 25 15 (by decide) (by decide),
  .clear 16,
  .add 3 4 16 (by decide) (by decide),
  .clear 19,
  .mul 10 16 19 (by decide) (by decide),
  .clear 20,
  .mul 19 12 20 (by decide) (by decide),
  .clear 22,
  .mul 20 15 22 (by decide) (by decide),
  .clear 23,
  .mul 18 18 23 (by decide) (by decide),
  .clear 24,
  .mul 21 23 24 (by decide) (by decide),
  .clear 26,
  .mul 11 24 26 (by decide) (by decide),
  .clear 27,
  .mul 10 29 27 (by decide) (by decide)]

def emissions : List Instr := [
  .clear 44,
  .copy 1 44 (by decide),
  .clear 45,
  .copy 8 45 (by decide),
  .clear 46,
  .copy 0 46 (by decide),
  .clear 47,
  .copy 1 47 (by decide),
  .clear 48,
  .copy 2 48 (by decide),
  .clear 49,
  .copy 8 49 (by decide),
  .clear 50,
  .copy 3 50 (by decide),
  .clear 51,
  .copy 8 51 (by decide),
  .clear 52,
  .copy 4 52 (by decide),
  .clear 53,
  .copy 8 53 (by decide),
  .clear 54,
  .copy 7 54 (by decide),
  .clear 55,
  .copy 1 55 (by decide),
  .clear 56,
  .copy 21 56 (by decide),
  .clear 57,
  .copy 9 57 (by decide),
  .clear 58,
  .copy 21 58 (by decide),
  .clear 59,
  .copy 27 59 (by decide),
  .clear 60,
  .copy 7 60 (by decide),
  .clear 61,
  .copy 22 61 (by decide),
  .clear 62,
  .copy 1 62 (by decide),
  .clear 63,
  .copy 26 63 (by decide)]

def code : List Instr := preparation ++ emissions

def command := Circuit.program code

theorem admissible (m : Model) : AdmissibleCode code m := by
  rw [code, admissibleCode_append]
  constructor
  · simp [preparation, AdmissibleCode, Admissible, next, output, value, lengthBound]
  · simp [emissions, AdmissibleCode, Admissible, next, output, value, lengthBound]

def pair (j : Fin 10) (h : Fin 2) : Fin 64 := ⟨44+2*j.val+h.val,by omega⟩

def upper (m : Model) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 => m.val 1
  | 1 => m.val 0
  | 2 => m.val 2
  | 3 => m.val 3
  | 4 => m.val 4
  | 5 | 8 => m.val 7
  | 6 | 7 => m.val 21
  | _ => m.val 1

def lower (m : Model) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 | 2 | 3 | 4 => 1
  | 1 | 5 => m.val 1
  | 6 => 2
  | 7 => 4*m.val 29
  | 8 => 4*(m.val 3+m.val 4)*(m.val 31)^2*(m.val 25)^2
  | _ => 16*m.val 21*(m.val 18)^2

theorem values (m : Model) (j : Fin 10) :
    (Circuit.result code m).val (pair j 0)=upper m j ∧
    (Circuit.result code m).val (pair j 1)=lower m j := by
  rw [code, result_append]
  fin_cases j <;>
    simp [emissions, Circuit.result, next, value, output, upper, lower, pair, pow_two] <;>
    simp [preparation, Circuit.result, next, value, output,
      BinaryArithmetic.toNat, bitVal, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem execution (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (Circuit.result code m) w' ∧ t ≤ Circuit.budget code m :=
  Circuit.program_eval code m w r hs (admissible m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPrepared -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def code := Layout.code++GuardSetup.code

abbrev command : Cmd 8 77 := Circuit.program code

def finalModel (x : Input) (l : Fin 8 → ℕ) :=
  Circuit.result GuardSetup.code (Layout.model x l)

def runtimeBound (x : Input) (l : Fin 8 → ℕ) :=
  Layout.runtimeBound x l+Circuit.budget GuardSetup.code (Layout.model x l)

theorem command_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (finalModel x l) w' ∧ t ≤ runtimeBound x l := by
  have ha : AdmissibleCode code (Layout.initialModel x l) := by
    rw [code,admissibleCode_append]
    exact ⟨Layout.admissible x l,GuardSetup.admissible _⟩
  simpa only [command,code,result_append,budget_append,finalModel,runtimeBound,
    Layout.model,Layout.runtimeBound] using
    Circuit.program_eval code (Layout.initialModel x l) w r hs ha

private theorem operand_bridge (m : Model) (x : Input) (p : Parameters)
    (h0 : m.val 0=x.ambient) (h1 : m.val 1=x.freeCount) (h2 : m.val 2=x.clauses)
    (h3 : m.val 3=x.occurrence) (h4 : m.val 4=x.arity) (h7 : m.val 7=x.incidences)
    (hr : m.val 18=p.r) (hQ : m.val 21=p.Q) (he : m.val 25=p.epsilonDen)
    (hR : m.val 29=p.R) (hN : m.val 31=p.N) (j : Fin 10) :
    GuardSetup.upper m j=BitGuard.upperFor x p j ∧ GuardSetup.lower m j=BitGuard.lowerFor x p j := by
  fin_cases j <;> simp [GuardSetup.upper,GuardSetup.lower,BitGuard.upperFor,BitGuard.lowerFor,
    h0,h1,h2,h3,h4,h7,hr,hQ,he,hR,hN]

theorem operand_values (x : Input) (l : Fin 8 → ℕ) (j : Fin 10) :
    (finalModel x l).val (GuardSetup.pair j 0)=BitGuard.upper x j ∧
    (finalModel x l).val (GuardSetup.pair j 1)=BitGuard.lower x j := by
  have hg := GuardSetup.values (Layout.model x l) j
  rcases Layout.model_core_values x l with ⟨hL,hw,hs,hr,hQ,he,hR,hN⟩
  have hb := operand_bridge (Layout.model x l) x (produce x)
    (Layout.model_inputs x l 0) (Layout.model_inputs x l 1) (Layout.model_inputs x l 2)
    (Layout.model_inputs x l 3) (Layout.model_inputs x l 4) (Layout.model_inputs x l 7)
    hr hQ he hR hN j
  exact ⟨hg.1.trans hb.1,hg.2.trans hb.2⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecute -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev Data := StructuredProgram.State 9 77

def state (r : Fin 9 → Bool) (w : Words) : Data :=
  ⟨r,(Bank.state (fun _ => false) w).stacks⟩

@[simp] theorem state_port (r : Fin 9 → Bool) (w : Words) (a : Fin 64) :
    (state r w).stacks (Bank.port a)=w a :=
  Bank.state_port (fun _ => false) w a

def registers : Fin 8 → Fin 9 := Fin.castAdd 1

def guardStacks (i : Fin 20) : Fin 77 := ⟨44+i.val,by omega⟩

theorem guardStacks_injective : Function.Injective guardStacks := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [guardStacks] at this
  omega

theorem guardStacks_pair (j : Fin 10) (h : Fin 2) :
    guardStacks (BitGuard.pair j h)=Bank.port (GuardSetup.pair j h) := by
  apply Fin.ext
  simp [guardStacks,BitGuard.pair,Bank.port,GuardSetup.pair,Nat.add_assoc]

abbrev numeric : Cmd 9 77 := liftCommand Prepared.command (Bank.port 0) (Bank.port 42) registers id

abbrev check : Cmd 9 77 := liftCommand BitGuard.command 0 0 id guardStacks

def setup : Cmd 9 77 := .seq numeric check

theorem numeric_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf w', Eval numeric t (state r w) (state rf w') ∧
      Shape (Prepared.finalModel x l) w' ∧ t ≤ Prepared.runtimeBound x l+1 := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := Prepared.command_eval x l w (r ∘ registers) hs
  let e := embedState registers id (state r w) (Bank.state rf w')
  have hrun : Eval numeric (t+1) (state r w) e :=
    eval_liftCommand_from_state Prepared.command (Bank.port 0) (Bank.port 42)
      registers id (state r w) (Fin.castAdd_injective 8 1) Function.injective_id he
  have heq : e=state e.regs w' := by
    apply CounterForPrograms.data_ext (a := e) (b := state e.regs w') rfl
    funext i
    exact embedState_stack registers id (state r w) (Bank.state rf w') Function.injective_id i
  refine ⟨t+1,e.regs,w',?_,hs',Nat.add_le_add_right ht 1⟩
  rw [← heq]
  exact hrun

theorem guard_encodes (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Prepared.finalModel x l) w) :
    BitGuard.Encodes x (projectState id guardStacks (state r w)) := by
  intro j
  have hv := Prepared.operand_values x l j
  constructor
  · change BinaryArithmetic.toNat ((state r w).stacks (guardStacks (BitGuard.pair j 0)))=_
    rw [guardStacks_pair]
    rw [state_port]
    exact (hs.1 _).trans hv.1
  · change BinaryArithmetic.toNat ((state r w).stacks (guardStacks (BitGuard.pair j 1)))=_
    rw [guardStacks_pair]
    rw [state_port]
    exact (hs.1 _).trans hv.2

/-- A native setup-and-test trace. The operand words are produced by the
numeric program itself before the ten bit comparisons are executed. -/
theorem setup_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t mid final,
      Eval setup t (state r w) final ∧
      (final.regs 8=true ↔ Guard x) ∧
      (∃ rm wm, mid=state rm wm ∧ Shape (Prepared.finalModel x l) wm) ∧
      (∀ a : Fin 64, a.val < 44 → final.stacks (Bank.port a)=mid.stacks (Bank.port a)) ∧
      t ≤ Prepared.runtimeBound x l+BitGuard.checksCost BitGuard.allChecks
        (projectState id guardStacks mid)+3 := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := numeric_eval x l w r hs
  let mid := state rf w'
  let a0 :=  projectState id guardStacks mid
  have hc : BitGuard.Encodes x a0 := guard_encodes x l w' rf hs'
  obtain ⟨b,hb,hflag⟩ := BitGuard.command_eval a0
  let final := embedState id guardStacks mid b
  have hcheck : Eval check ((1+BitGuard.checksCost BitGuard.allChecks a0)+1) mid final :=
    eval_liftCommand_from_state BitGuard.command 0 0 id guardStacks mid
      Function.injective_id guardStacks_injective hb
  refine ⟨t+((1+BitGuard.checksCost BitGuard.allChecks a0)+1),mid,final,
    he.seq hcheck,?_,⟨rf,w',rfl,hs'⟩,?_,by dsimp only [a0]; omega⟩
  · have hreg : final.regs 8=b.regs 8 :=
      embedState_register id guardStacks mid b Function.injective_id 8
    rw [hreg,hflag]
    exact BitGuard.checksPass_iff x a0 hc
  · intro a ha
    apply embedState_stack_frame id guardStacks mid b (Bank.port a)
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    dsimp [guardStacks,Bank.port] at hv
    omega

/-- Both branches are finite bit programs. Every input first pays the full
numeric setup and comparison cost, including inputs routed to fallback. -/
abbrev dispatch (yes no : Cmd 9 77) : Cmd 9 77 := .seq setup (.ite 8 yes no)

theorem dispatch_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) (yes no : Cmd 9 77) :
    ∃ t mid, Eval setup t (state r w) mid ∧ (mid.regs 8=true ↔ Guard x) ∧
      ∀ u final, Eval (if passes x then yes else no) u mid final →
        Eval (dispatch yes no) (t+(u+1)) (state r w) final := by
  obtain ⟨t,work,mid,he,hg,hshape,hframe,ht⟩ := setup_eval x l w r hs
  have hflag : mid.regs 8=passes x := by
    apply Bool.eq_iff_iff.mpr
    rw [hg,passes_eq_true]
  refine ⟨t,mid,he,hg,?_⟩
  intro u final hu
  apply he.seq
  cases hp : passes x with
  | false => exact Eval.ite_false (hflag.trans hp) (by simpa [hp] using hu)
  | true => exact Eval.ite_true (hflag.trans hp) (by simpa [hp] using hu)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

/-- Only these numeric values control loops or increase representation length.
The numeric result of a power is deliberately absent. -/
def scale (m : Model) : Instr → ℕ
  | .load _ bits => bits.length
  | .pow _ b _ _ _ => m.val b
  | .sqrt a _ _ => m.val a
  | .addConst _ k => k
  | _ => 2

def majorant (B : ℕ) : ℕ := 10000000*(B+2)^6

theorem le_majorant (B : ℕ) : B ≤ majorant B := by
  have hp : B+2 ≤ (B+2)^6 := Nat.le_self_pow (by decide) _
  dsimp [majorant]
  omega

private theorem power_bounds (B : ℕ) :
    1 ≤ (B+2)^6 ∧ B ≤ (B+2)^6 ∧ B^2 ≤ (B+2)^6 ∧
      B^3 ≤ (B+2)^6 ∧ B^4 ≤ (B+2)^6 := by
  have h1 : 1 ≤ B+2 := by omega
  have hp (k : ℕ) (hk : k ≤ 6) : B^k ≤ (B+2)^6 :=
    (Nat.pow_le_pow_left (show B ≤ B+2 by omega) k).trans (Nat.pow_le_pow_right h1 hk)
  exact ⟨one_le_pow₀ h1,(by simpa using hp 1 (by decide)),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide)⟩

theorem length_cost_majorant (m : Model) (i : Instr) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : scale m i ≤ B) :
    lengthBound m.val m.len i ≤ majorant B ∧ cost m.val m.len i ≤ majorant B := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := power_bounds B
  have hM := le_majorant B
  cases i with
  | clear a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  0 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B+3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | load o bits =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | copy a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  7*B+5 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | add a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | mul a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pow a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  1+B*B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  B*(50*(B+1)*(2+(B+1)*B))+(B+1)*(16*B+16)+3+9*B+8 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | quot a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  150*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | sqrt a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  200001*(B+B+2)^3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | logSucc a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  32*(B+1)^2+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | addConst a k =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  8*B*(B+B+1)+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pred a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  20*(B+1) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | maxTwo a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+2 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+3) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]

def iterMajorant : ℕ → ℕ → ℕ
  | 0,B => B
  | n+1,B => iterMajorant n (majorant B)

theorem le_iterMajorant (n B : ℕ) : B ≤ iterMajorant n B := by
  induction n generalizing B with
  | zero => exact le_rfl
  | succ n ih => exact (le_majorant B).trans (ih (majorant B))

def ScaleBound (B : ℕ) : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => scale m i ≤ B ∧ ScaleBound B is (next m i)

theorem scaleBound_mono (B C : ℕ) (hBC : B ≤ C) (is : List Instr) (m : Model)
    (h : ScaleBound B is m) : ScaleBound C is m := by
  induction is generalizing m with
  | nil => trivial
  | cons i is ih => exact ⟨h.1.trans hBC,ih (next m i) h.2⟩

/-- A single global bound on numeric loop parameters yields a polynomial
bound for every fixed instruction table, regardless of large output values. -/
theorem budget_majorant (is : List Instr) (m : Model) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : ScaleBound B is m) :
    (∀ a, (result is m).len a ≤ iterMajorant is.length B) ∧
      budget is m ≤ is.length*iterMajorant is.length B := by
  induction is generalizing m B with
  | nil => exact ⟨hl,by simp [budget]⟩
  | cons i is ih =>
    have hi := length_cost_majorant m i B hl hs.1
    have hn : ∀ a, (next m i).len a ≤ majorant B := by
      intro a
      by_cases ha : a=output i
      · simpa [next,ha] using hi.1
      · simpa [next,ha] using (hl a).trans (le_majorant B)
    have ht := ih (next m i) (majorant B) hn
      (scaleBound_mono B (majorant B) (le_majorant B) is (next m i) hs.2)
    refine ⟨ht.1,?_⟩
    have hm := le_iterMajorant is.length (majorant B)
    simp only [budget,List.length_cons,iterMajorant]
    nlinarith [hi.2,ht.2]

def coefficient : ℕ → ℕ
  | 0 => 1
  | n+1 => coefficient n * 10000000^(6^n)

def polynomialCoefficient : ℕ → ℕ
  | 0 => 1
  | n+1 => polynomialCoefficient n * (10000000*3^6)^(6^n)

/-- The deliberately loose degree is a fixed constant once the finite table
is fixed. It establishes a genuine ordinary-polynomial setup bound. -/
theorem iterMajorant_polynomial (n B : ℕ) (hB : 1 ≤ B) :
    iterMajorant n B ≤ polynomialCoefficient n * B^(6^n) := by
  induction n generalizing B with
  | zero => simp [iterMajorant,polynomialCoefficient]
  | succ n ih =>
    have hF : 1 ≤ majorant B := hB.trans (le_majorant B)
    have hb : B+2 ≤ 3*B := by omega
    have hm : majorant B ≤ (10000000*3^6)*B^6 := by
      dsimp [majorant]
      calc
        _  ≤  10000000*(3*B)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
        _ = _ := by rw [mul_pow]; ring_nf
    calc
      iterMajorant (n+1) B = iterMajorant n (majorant B) := rfl
      _  ≤  polynomialCoefficient n * (majorant B)^(6^n) := ih (majorant B) hF
      _  ≤  polynomialCoefficient n * ((10000000*3^6)*B^6)^(6^n) := by gcongr
      _ = polynomialCoefficient (n+1)*B^(6^(n+1)) := by
        rw [polynomialCoefficient,mul_pow,← pow_mul,pow_succ 6 n]
        simp only [Nat.mul_comm,Nat.mul_assoc]

@[simp] theorem scaleBound_append (B : ℕ) (xs ys : List Instr) (m : Model) :
    ScaleBound B (xs++ys) m ↔ ScaleBound B xs m ∧ ScaleBound B ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [ScaleBound,result]
  | cons i xs ih => simp [ScaleBound,result,ih,and_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

/-- The only input values entering loop costs are precisely the four small
operands bounded in CrudeBounds. All power outputs affect later work through
binary word lengths alone. -/
theorem scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (loopCap x) code (initialModel x l) := by
  obtain ⟨h16,hL,hQ,hR,hd⟩ := loop_operands_le_cap x
  have hL' : (x.freeCount + 16).log2 + 1 ≤ loopCap x := by
    simpa [L] using hL
  have hR' : 128 * (layoutQ x.freeCount *
      layoutEnergy x.freeCount x.occurrence) ≤ loopCap x := by
    simpa only [Nat.mul_assoc] using hR
  have henergy :
      Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1 =
        layoutEnergy x.freeCount x.occurrence := by
    simp [layoutEnergy,pow_two,Nat.mul_assoc]
  have hRcomputed : 128 * (layoutQ x.freeCount *
      (Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1)) ≤ loopCap x := by
    rw [henergy]
    exact hR'
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hRcomputed
  have hQcomputed := hQ
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hQcomputed
  rw [code,scaleBound_append]
  constructor
  · simp [coreCode,ScaleBound,scale,next,output,value,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal,Nat.mul_assoc]
    omega
  · have hQ' : (result coreCode (initialModel x l)).val 21 = layoutQ x.freeCount := by
      rw [coreCode,result_append]
      rw [result_value_frame finishCode _ 21]
      · exact (prefix_values x l).2.2
      · decide
    simp [tailCode,ScaleBound,scale,next,output,value,hQ']
    omega

theorem guard_scaleBound (m : Model) (B : ℕ) (hB : 16 ≤ B) :
    ScaleBound B GuardSetup.code m := by
  rw [GuardSetup.code, scaleBound_append]
  constructor
  · simp [GuardSetup.preparation, ScaleBound, scale]
    omega
  · simp [GuardSetup.emissions, ScaleBound, scale]
    omega

def inputMeasure (x : Input) (l : Fin 8 → ℕ) : ℕ := magnitude x+∑ i, l i

def setupScale (x : Input) (l : Fin 8 → ℕ) : ℕ := loopCap x+∑ i, l i

def guardedCode := code++GuardSetup.code

def guardedBudget (x : Input) (l : Fin 8 → ℕ) :=
  Circuit.budget guardedCode (initialModel x l)

theorem setupScale_pos (x : Input) (l : Fin 8 → ℕ) : 1 ≤ setupScale x l := by
  have := (loop_operands_le_cap x).1
  dsimp [setupScale]
  omega

theorem initial_lengths_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ a, (initialModel x l).len a ≤ setupScale x l := by
  intro a
  dsimp [initialModel]
  split_ifs with h
  · have hs : l ⟨a.val,h⟩ ≤ ∑ i, l i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    dsimp [setupScale]
    omega
  · exact Nat.zero_le _

theorem guarded_scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (setupScale x l) guardedCode (initialModel x l) := by
  rw [guardedCode,scaleBound_append]
  constructor
  · exact scaleBound_mono _ _ (by dsimp [setupScale]; omega) _ _ (scaleBound x l)
  · exact guard_scaleBound _ _ (by have := (loop_operands_le_cap x).1; dsimp [setupScale]; omega)

theorem guarded_budget_bound (x : Input) (l : Fin 8 → ℕ) :
    guardedBudget x l ≤ guardedCode.length*polynomialCoefficient guardedCode.length*
      (setupScale x l)^(6^guardedCode.length) := by
  have hb := (budget_majorant guardedCode (initialModel x l) (setupScale x l)
    (initial_lengths_le x l) (guarded_scaleBound x l)).2
  have hp := iterMajorant_polynomial guardedCode.length (setupScale x l) (setupScale_pos x l)
  calc
    _  ≤  guardedCode.length*iterMajorant guardedCode.length (setupScale x l) := hb
    _  ≤  guardedCode.length*(polynomialCoefficient guardedCode.length*(setupScale x l)^(6^guardedCode.length)) :=
      Nat.mul_le_mul_left _ hp
    _ = _ := (Nat.mul_assoc _ _ _).symm

theorem setupScale_le (x : Input) (l : Fin 8 → ℕ) :
    setupScale x l ≤ 1000001*(inputMeasure x l)^6 := by
  have hm : magnitude x ≤ inputMeasure x l := by dsimp [inputMeasure]; omega
  have hl : (∑ i, l i) ≤ inputMeasure x l := by dsimp [inputMeasure]; omega
  have hp : inputMeasure x l ≤ (inputMeasure x l)^6 := Nat.le_self_pow (by decide) _
  calc
    setupScale x l = 1000000*(magnitude x)^6+∑ i, l i := rfl
    _  ≤  1000000*(inputMeasure x l)^6+(inputMeasure x l)^6 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 6)) (hl.trans hp)
    _ = _ := by ring_nf

private theorem scaled_power (U V X d : ℕ) :
    U*(V*X^6)^d=(U*V^d)*X^(6*d) := by
  rw [mul_pow,← pow_mul]
  exact (Nat.mul_assoc U (V^d) (X^(6*d))).symm

/-- Ordinary-polynomial bit work, uniformly over all padded input words.
The constants depend only on the fixed table, never on an input parameter. -/
theorem guarded_budget_ordinary :
    ∃ C d : ℕ, ∀ x l, guardedBudget x l ≤ C*(inputMeasure x l)^d := by
  let D := 6^guardedCode.length
  let C := guardedCode.length*polynomialCoefficient guardedCode.length*1000001^D
  refine ⟨C,6*D,?_⟩
  intro x l
  calc
    guardedBudget x l  ≤  guardedCode.length*polynomialCoefficient guardedCode.length*
        (setupScale x l)^D := guarded_budget_bound x l
    _  ≤  guardedCode.length*polynomialCoefficient guardedCode.length*
        (1000001*(inputMeasure x l)^6)^D :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (setupScale_le x l) D)
    _ = C*(inputMeasure x l)^(6*D) := by
      exact scaled_power _ _ _ _

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

theorem checksCost_le (js : List (Fin 10)) (d : Data) (B : ℕ)
    (h : ∀ j b, (d.stacks (pair j b)).length ≤ B) :
    checksCost js d ≤ js.length*(10*B+8) := by
  induction js with
  | nil => simp [checksCost]
  | cons j js ih =>
    have hc : cost j d ≤ 10*B+8 := by
      dsimp [cost]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 (max_le (h j 0) (h j 1))) 8
    simp only [checksCost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem allChecksCost_le (d : Data) (B : ℕ)
    (h : ∀ j b, (d.stacks (pair j b)).length ≤ B) :
    checksCost allChecks d ≤ 100*B+80 := by
  have hh := checksCost_le allChecks d B h
  simp [allChecks] at hh ⊢
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecuteCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def bitBound (x : Input) (l : Fin 8 → ℕ) : ℕ :=
  iterMajorant Layout.guardedCode.length (Layout.setupScale x l)

def runtimeBound (x : Input) (l : Fin 8 → ℕ) : ℕ :=
  Prepared.runtimeBound x l+100*bitBound x l+83

theorem final_lengths_le (x : Input) (l : Fin 8 → ℕ) (a : Fin 64) :
    (Prepared.finalModel x l).len a ≤ bitBound x l := by
  have h := (budget_majorant Layout.guardedCode (Layout.initialModel x l)
    (Layout.setupScale x l) (Layout.initial_lengths_le x l) (Layout.guarded_scaleBound x l)).1 a
  simpa only [Layout.guardedCode,result_append,Layout.model,Prepared.finalModel,bitBound] using h

theorem setup_eval_bounded (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t final, Eval setup t (state r w) final ∧ (final.regs 8=true ↔ Guard x) ∧
      t ≤ runtimeBound x l := by
  obtain ⟨t,mid,final,he,hg,⟨rm,wm,hm,hshape⟩,hframe,ht⟩ := setup_eval x l w r hs
  have hlen (j : Fin 10) (b : Fin 2) :
      ((projectState id guardStacks mid).stacks (BitGuard.pair j b)).length ≤ bitBound x l := by
    rw [hm]
    change ((state rm wm).stacks (guardStacks (BitGuard.pair j b))).length ≤ _
    rw [guardStacks_pair]
    rw [state_port]
    exact (hshape.2 _).trans (final_lengths_le x l _)
  have hc := BitGuard.allChecksCost_le (projectState id guardStacks mid) (bitBound x l) hlen
  exact ⟨t,final,he,hg,by dsimp [runtimeBound]; omega⟩

def program := compiled setup (Bank.port 0) (Bank.port 42)

theorem program_runs (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ final : Data, RunsIn program (runtimeBound x l+1)
      ((state r w).withPC (some program.entry)) (final.withPC none) ∧
      (final.regs 8=true ↔ Guard x) := by
  obtain ⟨t,final,he,hg,ht⟩ := setup_eval_bounded x l w r hs
  exact ⟨final,⟨t+1,Nat.add_le_add_right ht 1,compiled_halt_trace he (Bank.port 0) (Bank.port 42)⟩,hg⟩

theorem prepared_runtime_eq (x : Input) (l : Fin 8 → ℕ) :
    Prepared.runtimeBound x l=Layout.guardedBudget x l := by
  simp only [Prepared.runtimeBound,Layout.guardedBudget,Layout.guardedCode,budget_append,
    Layout.runtimeBound,Layout.model]

private theorem scaled_power (U V X d : ℕ) :
    U*(V*X^6)^d=(U*V^d)*X^(6*d) := by
  rw [mul_pow,← pow_mul]
  exact (Nat.mul_assoc U (V^d) (X^(6*d))).symm

private theorem assemble_cost (X Y N A P : ℕ)
    (hX : X ≤ N*A*P) (hY : Y ≤ A*P) (hP : 1 ≤ P) :
    X+100*Y+83+1 ≤ ((N+100)*A+84)*P := by
  nlinarith

/-- The complete physical parameter setup, including all guards and halt,
has a fixed ordinary-polynomial bound in input counts and padded bit lengths. -/
theorem runtime_ordinary :
    ∃ C d : ℕ, ∀ x l, runtimeBound x l+1 ≤ C*(Layout.inputMeasure x l)^d := by
  let N := Layout.guardedCode.length
  let D := 6^N
  let A := polynomialCoefficient N*1000001^D
  refine ⟨(N+100)*A+84,6*D,?_⟩
  intro x l
  let M := Layout.inputMeasure x l
  have hM : 1 ≤ M := by
    have hm := (magnitude_ge x).1
    dsimp [M,Layout.inputMeasure]
    omega
  have hpow : 1 ≤ M^(6*D) := one_le_pow₀ hM
  have hs := Layout.setupScale_le x l
  have hb : bitBound x l ≤ A*M^(6*D) := by
    calc
      bitBound x l  ≤  polynomialCoefficient N*(Layout.setupScale x l)^D :=
        iterMajorant_polynomial N (Layout.setupScale x l) (Layout.setupScale_pos x l)
      _  ≤  polynomialCoefficient N*(1000001*M^6)^D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs D)
      _ = A*M^(6*D) := scaled_power _ _ _ _
  have hn : Prepared.runtimeBound x l ≤ N*A*M^(6*D) := by
    rw [prepared_runtime_eq]
    calc
      Layout.guardedBudget x l  ≤  N*polynomialCoefficient N*(Layout.setupScale x l)^D :=
        Layout.guarded_budget_bound x l
      _  ≤  N*polynomialCoefficient N*(1000001*M^6)^D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs D)
      _ = N*A*M^(6*D) := by
        rw [scaled_power]
        exact congrArg (fun z => z*M^(6*D)) (Nat.mul_assoc N (polynomialCoefficient N) (1000001^D))
  dsimp [runtimeBound]
  change Prepared.runtimeBound x l+100*bitBound x l+83+1 ≤ ((N+100)*A+84)*M^(6*D)
  exact assemble_cost _ _ _ _ _ hn hb hpow

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Public output ABI for a successful fast-path parameter setup. Other
entries are paid working values and need not be interpreted by callers. -/
def EncodesParameters (p : Parameters) (w : Words) : Prop :=
  BinaryArithmetic.toNat (w 13)=p.L ∧ BinaryArithmetic.toNat (w 14)=p.w ∧ BinaryArithmetic.toNat (w 17)=p.s ∧
  BinaryArithmetic.toNat (w 18)=p.r ∧ BinaryArithmetic.toNat (w 21)=p.Q ∧ BinaryArithmetic.toNat (w 25)=p.epsilonDen ∧
  BinaryArithmetic.toNat (w 29)=p.R ∧ BinaryArithmetic.toNat (w 31)=p.N ∧ BinaryArithmetic.toNat (w 33)=p.t ∧
  BinaryArithmetic.toNat (w 34)=p.d ∧ BinaryArithmetic.toNat (w 35)=3^p.d ∧ BinaryArithmetic.toNat (w 42)=p.J

theorem shape_encodes (x : Input) (l : Fin 8 → ℕ) (w : Words)
    (hs : Shape (model x l) w) (hm : x.clauses≠0) (hq : (produce x).Q≠0) :
    EncodesParameters (produce x) w := by
  rcases model_core_values x l with ⟨hL,hw,hs',hr,hQ,he,hR,hN⟩
  exact ⟨(hs.1 13).trans hL,(hs.1 14).trans hw,(hs.1 17).trans hs',
    (hs.1 18).trans hr,(hs.1 21).trans hQ,(hs.1 25).trans he,
    (hs.1 29).trans hR,(hs.1 31).trans hN,
    (hs.1 33).trans (model_precision x l hm),
    (hs.1 34).trans (model_degree x l hq),
    (hs.1 35).trans (model_fieldCard x l hq),
    (hs.1 42).trans (model_jet x l hm hq)⟩

theorem execution_public (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (initialModel x l) w) (hm : x.clauses≠0) (hq : (produce x).Q≠0) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      EncodesParameters (produce x) w' ∧ t ≤ runtimeBound x l := by
  obtain ⟨t,rf,w',he,hshape,ht⟩ := execution x l w r hs
  exact ⟨t,rf,w',he,shape_encodes x l w' hshape hm hq,ht⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecutePublic -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def publicSlot : Fin 12 → Fin 64 := ![13,14,17,18,21,25,29,31,33,34,35,42]

theorem publicSlot_lt (i : Fin 12) : (publicSlot i).val < 44 := by
  fin_cases i <;> decide

theorem guard_preserves_public (m : Model) (i : Fin 12) :
    (result GuardSetup.code m).val (publicSlot i)=m.val (publicSlot i) := by
  rw [GuardSetup.code, result_append]
  have he : ∀ j ∈ GuardSetup.emissions, output j ≠ publicSlot i := by
    fin_cases i <;> decide
  have hp : ∀ j ∈ GuardSetup.preparation, output j ≠ publicSlot i := by
    fin_cases i <;> decide
  calc
    (result GuardSetup.emissions (result GuardSetup.preparation m)).val (publicSlot i) =
        (result GuardSetup.preparation m).val (publicSlot i) := by
      exact result_value_frame _ _ _ he
    _ = m.val (publicSlot i) := by
      exact result_value_frame _ _ _ hp

theorem prepared_encodes (x : Input) (l : Fin 8 → ℕ) (w : Words)
    (hs : Shape (Prepared.finalModel x l) w) (hm : x.clauses≠0) (hq : (produce x).Q≠0) :
    Layout.EncodesParameters (produce x) w := by
  have hv (i : Fin 12) : BinaryArithmetic.toNat (w (publicSlot i))=(Layout.model x l).val (publicSlot i) :=
    (hs.1 _).trans (guard_preserves_public (Layout.model x l) i)
  rcases Layout.model_core_values x l with ⟨hL,hw,hs',hr,hQ,he,hR,hN⟩
  exact ⟨(hv 0).trans hL,(hv 1).trans hw,(hv 2).trans hs',
    (hv 3).trans hr,(hv 4).trans hQ,(hv 5).trans he,
    (hv 6).trans hR,(hv 7).trans hN,
    (hv 8).trans (Layout.model_precision x l hm),
    (hv 9).trans (Layout.model_degree x l hq),
    (hv 10).trans (Layout.model_fieldCard x l hq),
    (hv 11).trans (Layout.model_jet x l hm hq)⟩

theorem encodes_congr (p : Parameters) (w w' : Words)
    (h : ∀ i, w (publicSlot i)=w' (publicSlot i)) :
    Layout.EncodesParameters p w ↔ Layout.EncodesParameters p w' := by
  unfold Layout.EncodesParameters
  have h0 : w 13=w' 13 := h 0
  have h1 : w 14=w' 14 := h 1
  have h2 : w 17=w' 17 := h 2
  have h3 : w 18=w' 18 := h 3
  have h4 : w 21=w' 21 := h 4
  have h5 : w 25=w' 25 := h 5
  have h6 : w 29=w' 29 := h 6
  have h7 : w 31=w' 31 := h 7
  have h8 : w 33=w' 33 := h 8
  have h9 : w 34=w' 34 := h 9
  have h10 : w 35=w' 35 := h 10
  have h11 : w 42=w' 42 := h 11
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

/-- Native end-to-end parameter production and guard testing. On a successful
fast path every public output word encodes its exact specified parameter. -/
theorem setup_output (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t final, Eval setup t (state r w) final ∧ (final.regs 8=true ↔ Guard x) ∧
      (Guard x → Layout.EncodesParameters (produce x) (fun a => final.stacks (Bank.port a))) ∧
      t ≤ runtimeBound x l := by
  obtain ⟨t,mid,final,he,hg,⟨rm,wm,hm,hshape⟩,hframe,ht⟩ := setup_eval x l w r hs
  have hlen (j : Fin 10) (b : Fin 2) :
      ((projectState id guardStacks mid).stacks (BitGuard.pair j b)).length ≤ bitBound x l := by
    rw [hm]
    change ((state rm wm).stacks (guardStacks (BitGuard.pair j b))).length ≤ _
    rw [guardStacks_pair]
    rw [state_port]
    exact (hshape.2 _).trans (final_lengths_le x l _)
  have hc := BitGuard.allChecksCost_le (projectState id guardStacks mid) (bitBound x l) hlen
  refine ⟨t,final,he,hg,?_,by dsimp [runtimeBound]; omega⟩
  intro hg'
  have hm' : x.clauses≠0 := Nat.ne_of_gt hg'.2.2.1
  have hq' : (produce x).Q≠0 := by have hh := hg'.2.2.2.2.2.2.1; omega
  have hp := prepared_encodes x l wm hshape hm' hq'
  apply (encodes_congr (produce x) (fun a => final.stacks (Bank.port a)) wm ?_).mpr hp
  intro i
  rw [hframe (publicSlot i) (publicSlot_lt i),hm,state_port]


theorem program_output_runs (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ final : Data, RunsIn program (runtimeBound x l+1)
      ((state r w).withPC (some program.entry)) (final.withPC none) ∧
      (final.regs 8=true ↔ Guard x) ∧
      (Guard x → Layout.EncodesParameters (produce x) (fun a => final.stacks (Bank.port a))) := by
  obtain ⟨t,final,he,hg,hp,ht⟩ := setup_output x l w r hs
  exact ⟨final,⟨t+1,Nat.add_le_add_right ht 1,
    compiled_halt_trace he (Bank.port 0) (Bank.port 42)⟩,hg,hp⟩

theorem program_output_primitive (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ final : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(runtimeBound x l+1))
      (primitiveCfg program ((state r w).withPC (some program.entry)))
      (primitiveCfg program (final.withPC none)) ∧
      (final.regs 8=true ↔ Guard x) ∧
      (Guard x → Layout.EncodesParameters (produce x) (fun a => final.stacks (Bank.port a))) := by
  obtain ⟨final,he,hg,hp⟩ := program_output_runs x l w r hs
  exact ⟨final,BitProgram.primitive_execution program he,hg,hp⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramSerialization -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Input t is at33 and qE at35. The two derived metadata words are
qE−2 at44 and B=2t at45. No other numeric table entry changes. -/
def code : List Instr := [
  .clear 44, .copy 35 44 (by decide), .pred 44, .pred 44,
  .clear 45, .add 33 33 45 (by decide) (by decide)]

abbrev command : Cmd 8 77 := Circuit.program code

theorem admissible (m : Model) : AdmissibleCode code m := by
  simp [code,AdmissibleCode,Admissible,next,output,lengthBound]

theorem values (m : Model) :
    (result code m).val 44=m.val 35-2 ∧ (result code m).val 45=2*m.val 33 := by
  simp [code,result,next,value,output]
  omega

theorem frame (m : Model) (a : Fin 64) (h44 : a≠44) (h45 : a≠45) :
    (result code m).val a=m.val a := by
  simp [code,result,next,value,output,h44,h45]

theorem command_eval (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (result code m) w' ∧ t ≤ budget code m :=
  Circuit.program_eval code m w r hs (admissible m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization


end OAI.Algorithms
