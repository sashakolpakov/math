import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramMove

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def Ready (base : Data) : Prop :=
  (∀ i : Fin 256, i.val < 200 → base.stacks i=[]) ∧
  (∀ i : Fin 256, 212 ≤ i.val → i.val < 252 → base.stacks i=[])

def parked (base : Data) (query : ℕ) : Data :=
  ⟨base.regs,Function.update base.stacks 216 (unary query)⟩

theorem parked_ready (base : Data) (hb : Ready base) (query : ℕ) :
    ArithmeticReady (parked base query) := by
  intro i hi
  have hn : i≠216 := by
    intro h
    have he : i.val=216 := congrArg Fin.val h
    omega
  simp only [parked,Function.update_of_ne hn]
  exact hb.1 i (by omega)

def parkColumn : Code := move 253 216 224
def clearCount : Code := .call (StackRoutines.clearProgram 215 0 1)
def finish : Code := .seq (move 212 254 224)
  (.seq (move 213 255 224) (move 216 253 224))

theorem parkColumn_eval (base : Data) (hb : Ready base) (query : ℕ)
    (regs : Fin 16 → Bool) :
    Eval parkColumn (9*query+8)
      (data base regs [] (unary query) ([],[]) ([],[]))
      (data (parked base query) (readRegs regs 0 1 none) [] [] ([],[]) ([],[])) := by
  have h216 := hb.2 216 (by decide) (by decide)
  have h224 := hb.2 224 (by decide) (by decide)
  have h := move_eval 253 216 224 (data base regs [] (unary query) ([],[]) ([],[]))
    (by decide) (by decide) (by decide) (by simp [data,bank,h216]) (by simp [data,bank,h224])
  have he : moved 253 216 (data base regs [] (unary query) ([],[]) ([],[]))=
      data (parked base query) (readRegs regs 0 1 none) [] [] ([],[]) ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h216' : i=216
      · subst i; simp [data,bank,parked]
      by_cases h253 : i=253
      · subst i; simp [data,bank]
      simp [data,bank,parked,h216',h253]
  rw [he] at h
  simpa [parkColumn,data,bank,unary] using h

theorem query_eval (base : Data) (hb : Ready base) (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps) (regs : Fin 16 → Bool) :
    ∃ n ≤ LayoutOwnerFiberProgram.budget query ps+2*(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length+3,
      ∃ rf, Eval (.seq findOwner clearCount) n
        (data (parked base query) regs [] [] ([],[]) ([],[]))
        (data (parked base query) rf
          (encodeIndices (LayoutOwnerFiberProgram.fiberIndices query 0 ps)) [] ([],[]) ([],[])) := by
  let a := data (parked base query) regs [] [] ([],[]) ([],[])
  let is := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  obtain ⟨n,hn,rr,hr⟩ := findOwner_eval a query ps
    (by simp [a,data,bank,parked]) (by simpa [a,data,bank,parked] using hs)
    (by
      intro i hi
      fin_cases i <;> simp_all [ownerStacks,a,data,bank,parked]
      all_goals exact hb.2 _ (by decide) (by decide))
  have hc := SubexponentialSAT.Subexp.TupleProgram.clear_eval (215 : Fin 256) (0 : Fin 16) 1
    (ownerResult a rr is)
  have he : (⟨readRegs rr 0 1 none,
      StackRoutines.clearStacks 215 (ownerResult a rr is).stacks⟩ : Data)=
      data (parked base query) (readRegs rr 0 1 none) (encodeIndices is) [] ([],[]) ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h215 : i=215
      · subst i
        simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked,
          hb.2 215 (by decide) (by decide)]
      by_cases h214 : i=214
      · subst i; simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked]
      simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked,h215,h214]
  change Eval clearCount _ _ (⟨readRegs rr 0 1 none,
      StackRoutines.clearStacks 215 (ownerResult a rr is).stacks⟩ : Data) at hc
  rw [he] at hc
  have hh := hr.seq hc
  refine ⟨_,?_,readRegs rr 0 1 none,hh⟩
  simp only [ownerResult,Function.update_of_ne (show (215 : Fin 256)≠214 by decide),
    Function.update_same,unary,List.length_replicate]
  dsimp only [is]
  omega

theorem finish_eval (base : Data) (hb : Ready base) (query : ℕ)
    (regs : Fin 16 → Bool) (result : WordPair) :
    Eval finish (9*(pairLength result+query)+24)
      (data (parked base query) regs [] [] result ([],[]))
      (data base (readRegs regs 0 1 none) [] (unary query) ([],[]) result) := by
  let a := data (parked base query) regs [] [] result ([],[])
  let b := moved 212 254 a
  let c := moved 213 255 b
  have h224 := hb.2 224 (by decide) (by decide)
  have h1 := move_eval 212 254 224 a (by decide) (by decide) (by decide)
    (by simp [a,data,bank]) (by simp [a,data,bank,parked,h224])
  have h2 := move_eval 213 255 224 b (by decide) (by decide) (by decide)
    (by simp [b,moved,a,data,bank]) (by simp [b,moved,a,data,bank,parked,h224])
  have h3 := move_eval 216 253 224 c (by decide) (by decide) (by decide)
    (by simp [c,b,moved,a,data,bank]) (by simp [c,b,moved,a,data,bank,parked,h224])
  have he : moved 216 253 c=
      data base (readRegs regs 0 1 none) [] (unary query) ([],[]) result := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [c,b,moved,a,data,StackRoutines.readRegs_reset]
    · funext i
      by_cases h212 : i=212
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h213 : i=213
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h216 : i=216
      · subst i; simp [c,b,moved,a,data,bank,parked,hb.2 216 (by decide) (by decide)]
      by_cases h253 : i=253
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h254 : i=254
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h255 : i=255
      · subst i; simp [c,b,moved,a,data,bank,parked]
      simp [c,b,moved,a,data,bank,parked,h212,h213,h216,h253,h254,h255]
  rw [he] at h3
  convert h1.seq (h2.seq h3) using 1 <;>
    simp_all [a,b,c,moved,data,bank,parked,pairLength,unary] <;>
      first | rfl | omega

def command (entry : Code) : Code := .seq parkColumn
  (.seq (.seq findOwner clearCount) (.seq (loop entry) finish))
def actualProgram (entry : Code) := compiled (command entry) 253 254

def budget (T B J query : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  let count := (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length
  LayoutOwnerFiberProgram.budget query ps+18*query+2*count+39+
    count*(T+5*J+12+25000*((count+1)*(B+2)+3)^2+9*(B+2))

/-- The whole original-column wrapper: construct the fiber from original
owner plans, compute its entries one at a time, sum them, and restore column253.
Only the concrete per-incidence command remains a stated dependency. -/
theorem command_eval (entry : Code) (base : Data) (hb : Ready base)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (value : ℕ → ℤ) (T B M J : ℕ)
    (hentry : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps,
      EntryAt entry (parked base query) value T B M i)
    (hJ : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ J)
    (regs : Fin 16 → Bool) :
    ∃ n < budget T B J query ps, ∃ rf result,
      Eval (command entry) n (data base regs [] (unary query) ([],[]) ([],[]))
        (data base rf [] (unary query) ([],[]) result) ∧
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices query 0 ps).map value).sum ∧
      pairLength result ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(B+2) ∧
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*M := by
  let is := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  have hp := parkColumn_eval base hb query regs
  obtain ⟨nq,hnq,rq,hq⟩ := query_eval base hb query ps hs (readRegs regs 0 1 none)
  obtain ⟨nf,hnf,rf,result,hf,hv,hl,hm⟩ :=
    loop_eval entry (parked base query) (parked_ready base hb query) value T B M is
      hentry rq ([],[]) 0 (by simp [pairLength])
  have hh := finish_eval base hb query rf result
  have hc := cost_le T B J 0 is hJ
  simp only [Nat.zero_add] at hc hl
  have hv' : pairValue result=(is.map value).sum := by simpa [pairValue,signedValue] using hv
  have hm' : pairTotal result.1 result.2 ≤ is.length*M := by simpa [pairTotal] using hm
  refine ⟨_,?_,readRegs rf 0 1 none,result,hp.seq (hq.seq (hf.seq hh)),hv',hl,hm'⟩
  unfold budget
  dsimp only [is] at *
  nlinarith

theorem actualProgram_runs (entry : Code) (base : Data) (hb : Ready base)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (value : ℕ → ℤ) (T B M J : ℕ)
    (hentry : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps,
      EntryAt entry (parked base query) value T B M i)
    (hJ : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ J)
    (regs : Fin 16 → Bool) :
    ∃ rf result, RunsIn (actualProgram entry) (budget T B J query ps)
      ((data base regs [] (unary query) ([],[]) ([],[])).withPC (some (actualProgram entry).entry))
      ((data base rf [] (unary query) ([],[]) result).withPC none) ∧
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices query 0 ps).map value).sum ∧
      pairLength result ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(B+2) ∧
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*M := by
  obtain ⟨n,hn,rf,result,he,hv,hl,hm⟩ := command_eval entry base hb query ps hs value T B M J hentry hJ regs
  exact ⟨rf,result,⟨n+1,by omega,compiled_halt_trace he 253 254⟩,hv,hl,hm⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
