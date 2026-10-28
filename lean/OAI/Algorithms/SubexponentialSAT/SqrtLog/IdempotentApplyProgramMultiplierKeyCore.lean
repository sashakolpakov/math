import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramConstant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeKeyMapProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


def keyPorts : Fin 6 → Fin 96 := ![89,90,91,81,92,93]
theorem keyPorts_injective : Function.Injective keyPorts := by decide

abbrev makeUKeyCommand : Cmd 8 96 := List.foldr Cmd.seq (.base .skip)
  [copy 88 89 70,
   liftCommand HashCircuitProgram.Constant.pad 0 2 id keyPorts,
   liftCommand HashCircuitProgram.Constant.tag 2 2 id keyPorts,
   .base (.atom (.set 0 true)), .base (.atom (.push 91 0)),
   copy 91 94 70, clear 91]

def mapPorts : Fin 15 → Fin 96 := ![67,94,45,46,86,80,81,82,83,84,85,89,90,91,92]
theorem mapPorts_injective : Function.Injective mapPorts := by decide
abbrev shiftUCommand : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id mapPorts)

/-- The monomial U, with empty Boolean support. -/
def uKey (n : ℕ) : Squarefree.Index (Fin n) := ⟨1,0,∅⟩

theorem uKey_encode (n : ℕ) :
    Squarefree.encodeIndex (uKey n)=true :: List.replicate (n+2) false := by
  simp [uKey,Squarefree.encodeIndex,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const,List.replicate_succ]

private def keyState (regs : Fin 8 → Bool) (bank : Fin 96 → List Bool)
    (shape key output : List Bool) : State 8 96 :=
  ⟨regs,Function.update (Function.update (Function.update bank 89 shape) 91 key) 94 output⟩

private theorem embed_key (regs rr : Fin 8 → Bool) (bank : Fin 96 → List Bool)
    (shape key output shape' key' : List Bool)
    (h90:bank 90=[]) (h81:bank 81=[]) (h92:bank 92=[]) (h93:bank 93=[]) :
    embedState id keyPorts (keyState regs bank shape key output)
      (HashCircuitProgram.Constant.data rr shape' [] key' [] [] [])=keyState rr bank shape' key' output := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [keyPorts,keyState,HashCircuitProgram.Constant.data,h90,h81,h92,h93]
  · intro i hi
    have h89:i≠89:=by intro he; apply hi; exact ⟨0,he.symm⟩
    have h91:i≠91:=by intro he; apply hi; exact ⟨2,he.symm⟩
    simp [keyState,Function.update_apply,h89,h91]

private theorem project_key (regs : Fin 8 → Bool) (bank : Fin 96 → List Bool)
    (shape key output : List Bool)
    (h90:bank 90=[]) (h81:bank 81=[]) (h92:bank 92=[]) (h93:bank 93=[]) :
    projectState id keyPorts (keyState regs bank shape key output)=
      HashCircuitProgram.Constant.data regs shape [] key [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [keyPorts,keyState,h90,h81,h92,h93]

/-- The shape tape is preserved; the only resulting stack change is the new U key. -/
theorem makeUKey_command_eval (x : State 8 96)
    (h70:x.stacks 70=[]) (h89:x.stacks 89=[]) (h90:x.stacks 90=[])
    (h91:x.stacks 91=[]) (h81:x.stacks 81=[]) (h92:x.stacks 92=[])
    (h93:x.stacks 93=[]) (h94:x.stacks 94=[]) :
    ∃ rr, Eval makeUKeyCommand (20*(x.stacks 88).length+50) x
      ⟨rr,Function.update x.stacks 94 (Squarefree.encodeIndex (uKey (x.stacks 88).length))⟩ := by
  let shape:=x.stacks 88
  let n:=shape.length
  let r1:=readRegs x.regs 0 1 none
  have h1:=copy_eval x 88 89 70 (by decide) (by decide) (by decide) h70
  have h1' : Eval (copy 88 89 70) (7*n+5) x (keyState r1 x.stacks shape [] []) := by
    convert h1 using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi:i=89 <;> by_cases hj:i=91 <;> by_cases hk:i=94 <;>
        simp_all [copied,StackRoutines.copyStacks,shape]
  obtain ⟨r2,h2⟩:=HashCircuitProgram.Constant.pad_eval r1 shape []
  have h2':=eval_liftCommand h2 0 2 id keyPorts
    (keyState r1 x.stacks shape [] []) Function.injective_id keyPorts_injective
  rw [embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93,
      embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93] at h2'
  have h3:=eval_liftCommand (HashCircuitProgram.Constant.tag_eval r2 n []) 2 2 id keyPorts
    (keyState r2 x.stacks [] (List.replicate n false) []) Function.injective_id keyPorts_injective
  rw [embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93,
      embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93] at h3
  let r3:=Function.update r2 (0:Fin 8) false
  let r4:=Function.update r3 (0:Fin 8) true
  let z:=Squarefree.encodeIndex (uKey n)
  have h4 : Eval (.base (.atom (.set 0 true))) 1
      (keyState r3 x.stacks [] (HashCircuitProgram.Constant.key n) []) (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []) := by
    exact Eval.base (StructuredProgram.Eval.atom _ _)
  have h5 : Eval (.base (.atom (.push 91 0))) 1
      (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []) (keyState r4 x.stacks [] z []) := by
    have hp:=Eval.base (StructuredProgram.Eval.atom (.push (91:Fin 96) (0:Fin 8))
      (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []))
    convert hp using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi:i=91 <;> by_cases hj:i=94 <;>
        simp [keyState,z,uKey_encode,HashCircuitProgram.Constant.key,r4,Function.update_apply,hi,hj,StructuredProgram.Atom.instr,execInstr]
  let r6:=readRegs r4 0 1 none
  have h6:=copy_eval (keyState r4 x.stacks [] z []) 91 94 70
    (by decide) (by decide) (by decide) (by simpa [keyState] using h70)
  have h6' : Eval (copy 91 94 70) (7*(n+3)+5)
      (keyState r4 x.stacks [] z []) (keyState r6 x.stacks [] z z) := by
    convert h6 using 1
    · simp [keyState,z,Squarefree.encodeIndex_length,uKey]; omega
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; by_cases hi:i=94 <;>
          simp_all [copied,StackRoutines.copyStacks,keyState,Function.update_apply]
  have h7:=clear_eval (keyState r6 x.stacks [] z z) 91
  have h7' : Eval (clear 91) (2*(n+3)+3)
      (keyState r6 x.stacks [] z z) (keyState (readRegs r6 0 1 none) x.stacks [] [] z) := by
    convert h7 using 1
    · simp [keyState,z,Squarefree.encodeIndex_length,uKey]; omega
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; by_cases hi:i=91 <;> by_cases hj:i=94 <;>
          simp [StackRoutines.clearStacks,keyState,Function.update_apply,hi,hj]
  have hrun:=h1'.seq (h2'.seq (h3.seq (h4.seq (h5.seq (h6'.seq
    (h7'.seq (Eval.base (.skip _))))))))
  refine ⟨readRegs r6 0 1 none,?_⟩
  convert hrun using 1
  · rfl
  · dsimp [n, shape]
    omega
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 89 <;> by_cases hj : i = 91 <;> by_cases hk : i = 94 <;>
        simp_all [keyState, z, n, shape]

/-- The key-map call preserves its key and capacity tapes and all surrounding memory. -/
theorem shiftU_command_eval {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
    (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (hk:x.stacks 94=Squarefree.encodeIndex a)
    (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
    (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
      Eval shiftUCommand k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
        (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩ := by
  have h80:=hclean 80 (by simp)
  have h81:=hclean 81 (by simp)
  have h82:=hclean 82 (by simp)
  have h83:=hclean 83 (by simp)
  have h84:=hclean 84 (by simp)
  have h85:=hclean 85 (by simp)
  have h89:=hclean 89 (by simp)
  have h90:=hclean 90 (by simp)
  have h91:=hclean 91 (by simp)
  have h92:=hclean 92 (by simp)
  let initial:=Squarefree.KeyMapProgram.state x.regs (Squarefree.KeyMapProgram.idle (Squarefree.KeyMapProgram.environment a u J)
    (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries)) (x.stacks 86))
  have hi : projectState id mapPorts x=initial := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [mapPorts,Squarefree.KeyMapProgram.tapes,Squarefree.KeyMapProgram.idle,Squarefree.KeyMapProgram.environment,hs,hk,hu,hJ,
          h80,h81,h82,h83,h84,h85,h89,h90,h91,h92]
  obtain ⟨k,hbound,rr,ht⟩:=Squarefree.KeyMapProgram.scan_trace a u J entries (x.stacks 86) x.regs
  dsimp only [initial] at hi
  rw [←hi] at ht
  have he:=eval_call_from_state Squarefree.KeyMapProgram.scanProgram id mapPorts x
    Function.injective_id mapPorts_injective ht
  refine ⟨k,hbound,rr,?_⟩
  convert he using 1
  symm
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id mapPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;>
      simp [mapPorts,Squarefree.KeyMapProgram.state,Squarefree.KeyMapProgram.tapes,Squarefree.KeyMapProgram.idle,Squarefree.KeyMapProgram.environment,hk,hu,hJ,
        h80,h81,h82,h83,h84,h85,h89,h90,h91,h92]
  · intro i hi
    have h67:i≠67:=by intro he; apply hi; exact ⟨0,he.symm⟩
    have h86:i≠86:=by intro he; apply hi; exact ⟨4,he.symm⟩
    simp [h67,h86]

/-- The U key need not itself survive the truncation (in particular u may be 0 or 1). -/
theorem uKey_stepBudget_le {n u J C : ℕ} (b : Squarefree.Index (Fin n))
    (L : ℕ) (hb : b.Kept u J) (hL : L ≤ C) :
    Squarefree.KeyMapProgram.stepBudget (uKey n) b u J L ≤ 120*(n+u+J+C+3) := by
  rcases hb with ⟨hbu,hbz⟩
  simp only [Squarefree.KeyMapProgram.stepBudget,Squarefree.encodeIndex_length,
    uKey,Squarefree.Index.join]
  omega

/-- A linear scan bound with no lower bound on the U truncation capacity. -/
theorem uKey_budget_le {n u J C : ℕ} (entries : List (Squarefree.KeyMapProgram.Entry n))
    (hk : ∀ e∈entries,e.1.Kept u J) (hc : ∀ e∈entries,e.2.length ≤ C) :
    Squarefree.KeyMapProgram.budget (uKey n) u J entries ≤
      entries.length*(120*(n+u+J+C+3)+2)+1 := by
  induction entries with
  | nil => simp [Squarefree.KeyMapProgram.budget]
  | cons e entries ih =>
    rcases e with ⟨b,bits⟩
    have hs:=uKey_stepBudget_le b bits.length (hk (b,bits) (by simp)) (hc (b,bits) (by simp))
    have hr:=ih (fun e he=>hk e (by simp [he])) (fun e he=>hc e (by simp [he]))
    simp only [Squarefree.KeyMapProgram.budget,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
