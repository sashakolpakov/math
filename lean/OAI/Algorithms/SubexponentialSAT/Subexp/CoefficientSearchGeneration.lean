import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchInvariant

namespace OAI.Algorithms

/-!
# Actual tuple-generation prefix of coefficient search

The dimension is copied from its preserved unary input. The fixed tuple
machine emits the candidate records, and its sentinel is then cleared.
The low checker data and saved selected candidate remain framed.
-/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

private def generationCleared (d : Data) (src : Fin 32) : Data :=
  ⟨readRegs d.regs 11 12 none, Function.update d.stacks src []⟩

private theorem generationClear_eval (d : Data) (src : Fin 32) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (generationCleared d src) := by
  simpa only [clear, generationCleared, StackRoutines.clearStacks] using
    TupleProgram.clear_eval src (11 : Fin 14) 12 d

def tupleView (d : Data) : State 10 9 :=
  ⟨d.regs ∘ tupleRegisters, d.stacks ∘ tupleStacks⟩

theorem embed_tupleView (d : Data) :
    embedState tupleRegisters tupleStacks d (tupleView d) = d := by
  apply embedState_eq tupleRegisters tupleStacks tupleRegisters_injective tupleStacks_injective
  · intro i; rfl
  · intro i; rfl
  · intro i hi; rfl
  · intro i hi; rfl

def tupleLowRegisters (next : State 10 9) : Fin 8 → Bool :=
  fun i => next.regs (Fin.castAdd 2 i)

variable (p : ℕ) [Fact p.Prime]

def generationInput (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) (selected : List Bool) : Data :=
  wide (blank p R regs g neg ok) tag present found selected [] []
    (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p))
    (List.replicate A true)

/-- This input contains the scalar alphabet, field constants, and unary
interval counters; it contains no candidate list or successful coefficients. -/
def inputState (A R : ℕ) (regs : Fin 8 → Bool) (g neg ok tag present found : Bool) : Data :=
  generationInput p A R regs g neg ok tag present found []

def generationOutput (A R : ℕ) (next : State 10 9)
    (ok found : Bool) (selected : List Bool) : Data :=
  wide (blank p R (tupleLowRegisters next) (next.regs 8) false ok)
    false false found selected (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.rows p R)) []
    (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p))
    (List.replicate A true)

private theorem generation_stack_frame (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) (selected : List Bool) (next : State 10 9)
    (j : Fin 32) (hj : ¬ ∃ i, tupleStacks i = j) :
    Function.update (generationOutput p A R next ok found selected).stacks 28 [false] j =
      (afterCopy (generationInput p A R regs g neg ok tag present found selected)
        16 30 11 12).stacks j := by
  revert hj
  refine Fin.addCases (m := 20) (n := 12) (fun i => ?_) (fun i => ?_) j
  · intro _
    have h28 : (Fin.castAdd 12 i : Fin 32) ≠ 28 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have h30 : (Fin.castAdd 12 i : Fin 32) ≠ 30 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [generationOutput,generationInput,afterCopy,StackRoutines.copyStacks,
      wide,blank,CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
      MatrixScalarProgram.state,h28,h30]
  · intro hj
    fin_cases i <;>
      simp_all [tupleStacks,Fin.exists_fin_succ,generationOutput,generationInput,
        afterCopy,StackRoutines.copyStacks,wide,blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks,CoefficientPascalProgram.valueWords]

/-- Exact frame around the nine tuple-machine ports. -/
theorem generated_frame (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) (selected : List Bool) (next : State 10 9)
    (hn : TupleProgram.Ready (CoefficientSearchSemantics.scalarTokens p)
      (CoefficientSearchSemantics.rows p R) [] false next) :
    embedState tupleRegisters tupleStacks
      (afterCopy (generationInput p A R regs g neg ok tag present found selected) 16 30 11 12) next =
      ⟨(generationOutput p A R next ok found selected).regs,
        Function.update (generationOutput p A R next ok found selected).stacks 28 [false]⟩ := by
  rcases hn with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
  apply embedState_eq tupleRegisters tupleStacks tupleRegisters_injective tupleStacks_injective
  · intro i
    fin_cases i <;>
      simp [generationOutput,tupleLowRegisters,tupleRegisters,wide,blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,h9]
  · intro i
    fin_cases i <;>
      simp [generationOutput,tupleStacks,wide,blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks,CoefficientPascalProgram.valueWords,
        h0,h1,h2,h3,h4,h5,h6,h7,h8]
  · intro j hj
    have hjv : 10 ≤ j.val := by
      by_contra h
      exact hj ⟨⟨j.val,by omega⟩,Fin.ext rfl⟩
    fin_cases j <;>
      simp_all [generationOutput,generationInput,tupleLowRegisters,tupleRegisters,
        afterCopy,readRegs,wide,blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state]
  · intro j hj
    exact generation_stack_frame p A R regs g neg ok tag present found selected next j hj

theorem generation_clear_sentinel (A R : ℕ) (next : State 10 9)
    (ok found : Bool) (selected : List Bool) :
    generationCleared
      (⟨(generationOutput p A R next ok found selected).regs,
        Function.update (generationOutput p A R next ok found selected).stacks 28 [false]⟩ : Data)
      28 = generationOutput p A R next ok found selected := by
  apply state_ext
  · funext j
    fin_cases j <;>
      simp [generationCleared,readRegs,generationOutput,wide,blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state]
  · funext j
    fin_cases j <;>
      simp [generationCleared,generationOutput,wide,blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks,CoefficientPascalProgram.valueWords]

/-- One fixed generator actually constructs every candidate from scalar
tokens. No candidate list is supplied as an input. -/
theorem generate_eval_shape (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) (selected : List Bool) :
    ∃ n ≤ 7 * R + TupleProgram.powerCost (CoefficientSearchSemantics.scalarTokens p) R [[]] + 19,
      ∃ next : State 10 9,
        Eval generate n (generationInput p A R regs g neg ok tag present found selected)
          (generationOutput p A R next ok found selected) := by
  let d0 := generationInput p A R regs g neg ok tag present found selected
  let d1 := afterCopy d0 16 30 11 12
  let a := tupleView d1
  have htmp : d0.stacks 24 = [] := rfl
  have hlen : (d0.stacks 16).length = R := by
    simp [d0,generationInput,wide,blank,CoefficientCheckerProgram.wide]
  have e1 : Eval (copy 16 30) (7 * R + 5) d0 d1 := by
    simpa only [copy,hlen] using SubexpScanPrimitives.copy_eval d0 16 30 24 11 12
      (by decide) (by decide) (by decide) (by decide) htmp
  have ha : TupleProgram.outerInvariant (CoefficientSearchSemantics.scalarTokens p)
      (List.replicate R true) (a.regs 9) a := by
    simp [TupleProgram.outerInvariant,a,tupleView,Function.comp_def,tupleStacks,
      d1,d0,afterCopy,StackRoutines.copyStacks,generationInput,wide,blank,
      CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
      MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,CoefficientPascalProgram.valueWords]
  have h0 : a.stacks 0 = [] := rfl
  have h2 : a.stacks 2 = [] := rfl
  have h5 : a.stacks 5 = [] := rfl
  obtain ⟨next,hn,n,hcost,ht⟩ := TupleProgram.generateProgram_runsIn
    (CoefficientSearchSemantics.scalarTokens p) (List.replicate R true) (a.regs 9) a ha h0 h2 h5
  simp only [List.length_replicate] at hn hcost
  change TupleProgram.Ready (CoefficientSearchSemantics.scalarTokens p)
    (CoefficientSearchSemantics.rows p R) [] false next at hn
  let d2 := embedState tupleRegisters tupleStacks d1 next
  have e2 : Eval (.call (ProgramLinking.liftProgram TupleProgram.generateProgram tupleRegisters tupleStacks))
      n d1 d2 := by
    have he := eval_call_lifted TupleProgram.generateProgram tupleRegisters tupleStacks d1
      tupleRegisters_injective tupleStacks_injective (a := a) (b := next) ht
    simpa only [a,embed_tupleView] using he
  have hd2 : d2 =
      ⟨(generationOutput p A R next ok found selected).regs,
        Function.update (generationOutput p A R next ok found selected).stacks 28 [false]⟩ :=
    generated_frame p A R regs g neg ok tag present found selected next hn
  have hsentinel : d2.stacks 28 = [false] := by rw [hd2]; simp
  have e3 : Eval (clear 28) 5 d2 (generationOutput p A R next ok found selected) := by
    have he := generationClear_eval d2 28
    rw [hsentinel] at he
    have hout : generationCleared d2 28 = generationOutput p A R next ok found selected := by
      rw [hd2]
      exact generation_clear_sentinel p A R next ok found selected
    rw [hout] at he
    exact he
  refine ⟨(7 * R + 5) + (n + 5),by omega,next,?_⟩
  exact e1.seq (e2.seq e3)

/-- Ready-to-scan output, with all generator work ports cleared and the
saved selected candidate unchanged. -/
theorem generate_eval (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) (selected : List Bool)
    (hselected : selected.length ≤ R * (2 * width p + 1)) :
    ∃ n ≤ 7 * R + TupleProgram.powerCost (CoefficientSearchSemantics.scalarTokens p) R [[]] + 19,
      ∃ next : Data,
        Eval generate n (generationInput p A R regs g neg ok tag present found selected) next ∧
        Invariant p A R (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p)) next ∧
        next.stacks 22 = ProgramEncoding.encodeRecords (CoefficientSearchSemantics.rows p R) ∧
        next.stacks 23 = [] ∧ next.stacks 21 = selected := by
  obtain ⟨n,hn,t,he⟩ := generate_eval_shape p A R regs g neg ok tag present found selected
  refine ⟨n,hn,generationOutput p A R t ok found selected,he,?_,rfl,rfl,rfl⟩
  exact ⟨tupleLowRegisters t,t.regs 8,false,ok,false,false,found,selected,
    ProgramEncoding.encodeRecords (CoefficientSearchSemantics.rows p R),[],rfl,hselected⟩

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
