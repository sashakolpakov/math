import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceProgram

namespace OAI.Algorithms

/-! Concrete storage framing for the current-exponent source constructor. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

structure Context where
  exponent : Word
  width : Word
  target : Word
  modulus : Word
  unit : Word
  dimension : ℕ
  indexWidth : ℕ
  zero : Word
  one : Word
  template : Word

def flags (r : Fin 8 → Bool) (v p c : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update r 0 v) 1 p) 2 c

def state (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (payload bank support : Word)
    (captured : Word := []) : Data :=
  ⟨r,fun i => match i.val with
    | 0 => ctx.exponent | 1 => captured
    | 13 => a 0 | 14 => a 1 | 15 => a 2 | 16 => a 3
    | 17 => a 4 | 18 => a 5 | 19 => payload | 21 => a 6
    | 22 => bank | 23 => ctx.width | 24 => ctx.target
    | 25 => ctx.modulus | 26 => ctx.unit
    | 27 => List.replicate ctx.dimension true
    | 28 => List.replicate ctx.indexWidth true
    | 29 => support | 58 => input | 59 => ctx.zero | 60 => ctx.one
    | 62 => ctx.template | _ => []⟩

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 3 5

private def assemblyInverse (i : Fin 63) : Fin 22 :=
  if i = 58 then 0 else if i = 59 then 1 else if i = 60 then 2
  else ⟨i.val % 22,Nat.mod_lt _ (by decide)⟩

theorem assemblyPorts_injective : Function.Injective assemblyPorts :=
  (show Function.LeftInverse assemblyInverse assemblyPorts from by
    intro i; fin_cases i <;> rfl).injective

private def descriptorInverse (i : Fin 63) : Fin 38 := match i.val with
  | 0 => 0 | 22 => 1 | 23 => 2 | 24 => 3 | 25 => 4 | 26 => 5
  | 27 => 6 | 28 => 7 | 29 => 8 | 19 => 9 | 30 => 10 | 31 => 11
  | 32 => 12 | 33 => 13 | 34 => 14 | 35 => 15 | 36 => 16 | 37 => 17
  | 38 => 18 | 39 => 19 | 40 => 20 | 41 => 21 | 42 => 22 | 43 => 23
  | 44 => 24 | 45 => 25 | 46 => 26 | 47 => 27 | 48 => 28 | 49 => 29
  | 50 => 30 | 51 => 31 | 52 => 32 | 53 => 33 | 54 => 34 | 55 => 35
  | 56 => 36 | 57 => 37 | _ => 0

theorem descriptorPorts_injective : Function.Injective descriptorPorts :=
  (show Function.LeftInverse descriptorInverse descriptorPorts from by
    intro i; fin_cases i <;> rfl).injective

@[simp] theorem flags_self (r : Fin 8 → Bool) : flags r (r 0) (r 1) (r 2) = r := by
  simp [flags]

@[simp] theorem flags_flags (r : Fin 8 → Bool) (v p c v' p' c' : Bool) :
    flags (flags r v p c) v' p' c' = flags r v' p' c' := by
  funext i
  fin_cases i <;> simp [flags]

theorem assembly_project (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (payload bank support captured : Word) :
    projectState registers assemblyPorts (state ctx r input a payload bank support captured) =
      SubexpBlockAssembly.work (r 0) (r 1) (r 2) input ctx.zero ctx.one a payload [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem assembly_embed (ctx : Context) (r : Fin 8 → Bool) (input input' : Word)
    (a a' : SubexpBlockAssembly.Buffers) (payload payload' bank support captured : Word)
    (v p c : Bool) :
    embedState registers assemblyPorts (state ctx r input a payload bank support captured)
      (SubexpBlockAssembly.work v p c input' ctx.zero ctx.one a' payload' []) =
      state ctx (flags r v p c) input' a' payload' bank support captured := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective assemblyPorts_injective
  · intro i; fin_cases i <;> simp [state,flags,registers,SubexpBlockAssembly.work,
      SubexpHornerProgram.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
    simp [state,flags,h0,h1,h2]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h13 : i ≠ 13 := fun h => hi ⟨13,by simpa [assemblyPorts] using h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨14,by simpa [assemblyPorts] using h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨15,by simpa [assemblyPorts] using h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨16,by simpa [assemblyPorts] using h.symm⟩
    have h17 : i ≠ 17 := fun h => hi ⟨17,by simpa [assemblyPorts] using h.symm⟩
    have h18 : i ≠ 18 := fun h => hi ⟨18,by simpa [assemblyPorts] using h.symm⟩
    have h19 : i ≠ 19 := fun h => hi ⟨19,by simpa [assemblyPorts] using h.symm⟩
    have h21 : i ≠ 21 := fun h => hi ⟨21,by simpa [assemblyPorts] using h.symm⟩
    have h58 : i ≠ 58 := fun h => hi ⟨0,by simpa [assemblyPorts] using h.symm⟩
    fin_cases i <;> first | contradiction | rfl

theorem base_eval (ctx : Context) (r : Fin 8 → Bool) (input input' : Word)
    (a a' : SubexpBlockAssembly.Buffers) (payload payload' bank support captured : Word)
    (v p c : Bool) {cmd : SubexpBlockAssembly.Code} {n : ℕ}
    (h : Eval cmd n
      (SubexpBlockAssembly.work (r 0) (r 1) (r 2) input ctx.zero ctx.one a payload [])
      (SubexpBlockAssembly.work v p c input' ctx.zero ctx.one a' payload' [])) :
    Eval (base cmd) (n+1) (state ctx r input a payload bank support captured)
      (state ctx (flags r v p c) input' a' payload' bank support captured) := by
  have hh := eval_liftCommand_from_state cmd 0 19 registers assemblyPorts
    (state ctx r input a payload bank support captured) registers_injective assemblyPorts_injective
    (by rw [assembly_project]; exact h)
  simpa only [base,assembly_embed] using hh

theorem descriptor_project (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (payload bank support captured : Word) :
    projectState id descriptorPorts (state ctx r input a payload bank support captured) =
      SubexpWeightDescriptorProgram.state r ctx.exponent bank ctx.width ctx.target
        ctx.modulus ctx.unit ctx.dimension ctx.indexWidth support [] [] payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem descriptor_embed (ctx : Context) (r r' : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (payload payload' bank support support' captured : Word) :
    embedState id descriptorPorts (state ctx r input a payload bank support captured)
      (SubexpWeightDescriptorProgram.state r' ctx.exponent bank ctx.width ctx.target
        ctx.modulus ctx.unit ctx.dimension ctx.indexWidth support' [] [] payload') =
      state ctx r' input a payload' bank support' captured := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id descriptorPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h19 : i ≠ 19 := fun h => hi ⟨9,by simpa [descriptorPorts] using h.symm⟩
    have h29 : i ≠ 29 := fun h => hi ⟨8,by simpa [descriptorPorts] using h.symm⟩
    fin_cases i <;> first | contradiction | rfl

def afterMove (src dst : Fin 63) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src ++ d.stacks dst)⟩

/-- Two transfers preserve the payload order. The reversal buffer is empty
again at return, and all other data is unchanged. -/
theorem moveForward_eval (src dst : Fin 63) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 61) (hd : dst ≠ 61) (htmp : d.stacks 61 = []) :
    Eval (moveForward src dst) (6*(d.stacks src).length+6) d (afterMove src dst d) := by
  let middle : Data := ⟨readRegs d.regs 0 1 none,
    StackRoutines.transferStacks src 61 d.stacks⟩
  have h1 : Eval (transfer src 61) (3*(d.stacks src).length+3) d middle :=
    .call _ (ListRegisterProgram.transfer_run src 61 0 1 hs (by decide) d.regs d.stacks)
  have h2 : Eval (transfer 61 dst) (3*(middle.stacks 61).length+3) middle
      ⟨readRegs middle.regs 0 1 none,StackRoutines.transferStacks 61 dst middle.stacks⟩ :=
    .call _ (ListRegisterProgram.transfer_run 61 dst 0 1 hd.symm (by decide)
      middle.regs middle.stacks)
  have he : (⟨readRegs middle.regs 0 1 none,
      StackRoutines.transferStacks 61 dst middle.stacks⟩ : Data) = afterMove src dst d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [middle,readRegs]
    · funext i
      by_cases hi : i = src <;> by_cases hj : i = dst <;> by_cases hk : i = 61 <;>
        simp_all [middle,StackRoutines.transferStacks,Function.update_apply]
  rw [he] at h2
  have hm : (middle.stacks 61).length = (d.stacks src).length := by
    simp [middle,StackRoutines.transferStacks,htmp]
  rw [hm] at h2
  have h := Eval.seq h1 h2
  have hcost : 3 * (d.stacks src).length + 3 +
      (3 * (d.stacks src).length + 3) = 6 * (d.stacks src).length + 6 := by omega
  rw [hcost] at h
  exact h

theorem move_bank_eval (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (bits captured : Word) :
    Eval (moveForward 19 22) (6*bits.length+6)
      (state ctx r input a bits [] [] captured)
      (state ctx (readRegs r 0 1 none) input a [] bits [] captured) := by
  have h := moveForward_eval 19 22 (state ctx r input a bits [] [] captured)
    (by decide) (by decide) (by decide) rfl
  have he : afterMove 19 22 (state ctx r input a bits [] [] captured) =
      state ctx (readRegs r 0 1 none) input a [] bits [] captured := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> first | rfl | exact List.append_nil bits
  have hlen : ((state ctx r input a bits [] [] captured).stacks (19 : Fin 63)).length =
      bits.length := rfl
  rw [hlen] at h
  simpa only [he] using h

theorem move_support_eval (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (bits bank captured : Word) :
    Eval (moveForward 19 29) (6*bits.length+6)
      (state ctx r input a bits bank [] captured)
      (state ctx (readRegs r 0 1 none) input a [] bank bits captured) := by
  have h := moveForward_eval 19 29 (state ctx r input a bits bank [] captured)
    (by decide) (by decide) (by decide) rfl
  have he : afterMove 19 29 (state ctx r input a bits bank [] captured) =
      state ctx (readRegs r 0 1 none) input a [] bank bits captured := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> first | rfl | exact List.append_nil bits
  have hlen : ((state ctx r input a bits bank [] captured).stacks (19 : Fin 63)).length =
      bits.length := rfl
  rw [hlen] at h
  simpa only [he] using h

theorem clear_bank_eval (ctx : Context) (r : Fin 8 → Bool) (input : Word)
    (a : SubexpBlockAssembly.Buffers) (payload bank captured : Word) :
    Eval (clear 22) (2*bank.length+3)
      (state ctx r input a payload bank [] captured)
      (state ctx (readRegs r 0 1 none) input a payload [] [] captured) := by
  let d := state ctx r input a payload bank [] captured
  have h : Eval (clear 22) (2*bank.length+3) d
      ⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks 22 d.stacks⟩ :=
    .call _ (ListRegisterProgram.clear_run 22 0 1 d.regs d.stacks)
  have he : (⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks 22 d.stacks⟩ : Data) =
      state ctx (readRegs r 0 1 none) input a payload [] [] captured := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> rfl
  simpa only [he] using h

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
