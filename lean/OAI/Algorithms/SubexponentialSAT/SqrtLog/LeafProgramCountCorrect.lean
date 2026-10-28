import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadbackStore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCorrect

namespace OAI.Algorithms

/-! Closed count recovery: the native Hermite program, the native first-word
reader, and physical reclamation of the CRT caches. The hypotheses describe
stored data and the polynomial, never an assumed arithmetic execution. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram


noncomputable def install (frame : Data) (a : SubexpCRTOuterProgram.Data) : Data :=
  embedState crtRegisters crtStacks frame a

theorem crtRegisters_injective : Function.Injective crtRegisters :=
  Fin.castAdd_injective 16 24

theorem crtStacks_injective : Function.Injective crtStacks :=
  Fin.castAdd_injective 320 448

theorem install_stack (frame : Data) (a : SubexpCRTOuterProgram.Data) (i : Fin 320) :
    (install frame a).stacks (crtStacks i) = a.stacks i :=
  embedState_stack crtRegisters crtStacks frame a crtStacks_injective i

theorem install_stack_outside (frame : Data) (a : SubexpCRTOuterProgram.Data)
    (i : Fin 768) (hi : 320 ≤ i.val) :
    (install frame a).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

def project (a : Data) : SubexpCRTOuterProgram.Data :=
  projectState crtRegisters crtStacks a

theorem install_project (a : Data) : install a (project a) = a :=
  embedState_project crtRegisters crtStacks a crtRegisters_injective crtStacks_injective

theorem install_register_outside (frame : Data) (a : SubexpCRTOuterProgram.Data)
    (i : Fin 40) (hi : 16 ≤ i.val) : (install frame a).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem install_prepared_stacks (frame : Data) (input : SubexpCRTOuterProgram.Data)
    (rr : Fin 16 → Bool) (word : List Bool) :
    (install frame ⟨rr,Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261 word⟩).stacks =
      Function.update (Function.update (Function.update (install frame input).stacks
        5 (input.stacks 194)) 10 (input.stacks 202)) 261 word := by
  simp only [install,embedState,ReconstructionProgram.Entry.prepared,
    ProgramLinking.extend_update crtStacks_injective] ; rfl

theorem cachesCleared_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (cachesCleared a).regs i = a.regs i := by
  apply StackRoutines.readRegs_frame
  · intro h; subst i; simp at hi
  · intro h; subst i; simp at hi

/-- The CRT coefficient is consumed, and the two copied entry caches are
reclaimed. All three were empty in the ready caller, so only the count changes. -/
theorem readback_cleanup_stacks (entry middle : Data) (rr : Fin 8 → Bool)
    (word modulus width coeff : List Bool)
    (hmid : middle.stacks = Function.update (Function.update (Function.update
      entry.stacks 5 modulus) 10 width) 261 coeff)
    (h5 : entry.stacks 5 = []) (h10 : entry.stacks 10 = [])
    (h261 : entry.stacks 261 = [])
    (hempty : ∀ i∈([323,324,325,326,327,328,329] : List (Fin 768)), middle.stacks i=[]) :
    (cachesCleared (QueryReadback.Wide.completed middle rr word)).stacks =
      Function.update entry.stacks 323 word := by
  change Function.update (Function.update (QueryReadback.Wide.completed middle rr word).stacks
    5 []) 10 [] = _
  rw [QueryReadback.Wide.completed_stacks middle rr word hempty,hmid]
  funext i
  by_cases h323 : i=323
  · subst i; simp
  by_cases hi5 : i=5
  · subst i; simp [h5]
  by_cases hi10 : i=10
  · subst i; simp [h10]
  by_cases hi261 : i=261
  · subst i; simp [h261]
  simp [h323,hi5,hi10,hi261]

def recoveryBudget (Q J t d : ℕ) (modulus width : List Bool) : ℕ :=
  ReconstructionProgram.Native.budget Q J t d modulus.length width.length + 1 +
    SubexpFlatCount.budget (baseWidth 3 t) modulus (List.replicate (d*baseWidth 3 t) false) +
    6*(modulus.length+baseWidth 3 t)+7+2*modulus.length+2*width.length+6

theorem command_correct (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d)
    (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (polyFrame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth polyFrame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t))
    (frame : Data)
    (hm : BinaryArithmetic.toNat (input.stacks 194) = 3^t)
    (hw : (input.stacks 202).length = baseWidth 3 t)
    (hreader : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), frame.stacks i = []) :
    ∃ k out, k ≤ recoveryBudget Q J t d (input.stacks 194) (input.stacks 202) ∧
      Eval command k (install frame input) out ∧
      BinaryArithmetic.toNat (out.stacks 323) = count ∧
      (out.stacks 323).length = (input.stacks 194).length+baseWidth 3 t ∧
      out.stacks 324 = [] ∧ out.stacks 5 = [] ∧ out.stacks 10 = [] ∧
      out.stacks = Function.update (install frame input).stacks 323 (out.stacks 323) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = (install frame input).regs i) := by
  obtain ⟨b,rf,⟨nr,hnr,hr⟩,hb,_⟩ := ReconstructionProgram.Native.program_correct t ht hd a M cache hcanon hzbits
    J hJpos hB nodes jets minusOne hminus input hscalar scalarWidth polyFrame hpoly hclean
    hzero hone hneg hJ hnodes hjets hexponent hprecision hdistinct target hdegree htargetJets
    count m n hcount hlarge htarget
  let localOut : SubexpCRTOuterProgram.Data :=
    ⟨rf,Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩
  let middle := install frame localOut
  have hre : Eval reconstruct nr (install frame input) middle :=
    eval_call_lifted ReconstructionProgram.Native.program crtRegisters crtStacks frame
      crtRegisters_injective crtStacks_injective hr
  have hs (i : Fin 320) : middle.stacks (crtStacks i) = localOut.stacks i :=
    install_stack frame localOut i
  have h194 : middle.stacks 194 = input.stacks 194 := by
    rw [show (194 : Fin 768) = crtStacks 194 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h202 : middle.stacks 202 = input.stacks 202 := by
    rw [show (202 : Fin 768) = crtStacks 202 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h5 : middle.stacks 5 = input.stacks 194 := by
    rw [show (5 : Fin 768) = crtStacks 5 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h10 : middle.stacks 10 = input.stacks 202 := by
    rw [show (10 : Fin 768) = crtStacks 10 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have hv : middle.stacks 261 = RingProgram.flat b := by
    rw [show (261 : Fin 768) = crtStacks 261 from rfl,hs]
    simp [localOut]
  have he : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), middle.stacks i = [] := by
    intro i hi
    rw [install_stack_outside frame localOut i]
    · exact hreader i hi
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with h|h|h|h|h|h|h <;> subst i <;> decide
  obtain ⟨nk,afterRead,hnk,her,hvalue,hlen,hclear,rr,word,hafter⟩ :=
    QueryReadback.Wide.run_at t ht hd a M cache b count (hcount.trans_lt hlarge) hb middle hv
      (by simpa only [h194] using hm) (by simpa only [h202] using hw) he
  have hf5 : afterRead.stacks 5 = input.stacks 194 := by
    rw [hafter,QueryReadback.Wide.finished_stack_frame middle rr word 5 (by decide),h5]
  have hf10 : afterRead.stacks 10 = input.stacks 202 := by
    rw [hafter,QueryReadback.Wide.finished_stack_frame middle rr word 10 (by decide),h10]
  let nc := 2*(afterRead.stacks 5).length+2*(afterRead.stacks 10).length+6
  refine ⟨nr+(nk+nc),cachesCleared afterRead,?_,hre.seq (her.seq (clearCaches_eval afterRead)),?_,?_,?_,
    cachesCleared_five _,cachesCleared_ten _,?_,?_⟩
  · simp only [h194,SubexpFlatCount.budget,RingProgram.flat_length] at hnk
    simp only [recoveryBudget,SubexpFlatCount.budget,List.length_replicate,nc,hf5,hf10]
    omega
  · simpa only [cachesCleared_frame afterRead 323 (by decide) (by decide)] using hvalue
  · simpa only [cachesCleared_frame afterRead 323 (by decide) (by decide),h194] using hlen
  · simpa only [cachesCleared_frame afterRead 324 (by decide) (by decide)] using hclear
  · have hstart (j : Fin 320) : (install frame input).stacks (crtStacks j) = input.stacks j :=
      install_stack frame input j
    have hstart5 : (install frame input).stacks 5 = [] :=
      (hstart 5).trans (hclean 5 (by decide))
    have hstart10 : (install frame input).stacks 10 = [] :=
      (hstart 10).trans (hclean 10 (by decide))
    have hstart261 : (install frame input).stacks 261 = [] :=
      (hstart 261).trans (hclean 261 (by decide))
    have hmiddle : middle.stacks = Function.update (Function.update (Function.update
        (install frame input).stacks 5 (input.stacks 194)) 10 (input.stacks 202)) 261 (RingProgram.flat b) :=
      install_prepared_stacks frame input rf (RingProgram.flat b)
    have hstore := readback_cleanup_stacks (install frame input) middle rr word
      (input.stacks 194) (input.stacks 202) (RingProgram.flat b) hmiddle hstart5 hstart10 hstart261 he
    have hafter' : afterRead = QueryReadback.Wide.completed middle rr word := hafter
    have hword : (cachesCleared afterRead).stacks 323 = word := by
      rw [cachesCleared_frame afterRead 323 (by decide) (by decide),hafter']
      exact QueryReadback.Wide.completed_output middle rr word (he 323 (by simp)) (he 324 (by simp))
    rw [hword,hafter']
    exact hstore
  · intro i hi
    rw [cachesCleared_register_frame afterRead i (by omega)]
    have hafter' : afterRead = QueryReadback.Wide.completed middle rr word := hafter
    rw [hafter',QueryReadback.Wide.completed_register_frame middle rr word i (by omega)]
    exact (install_register_outside frame localOut i hi).trans
      (install_register_outside frame input i hi).symm

theorem program_correct (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d)
    (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (polyFrame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth polyFrame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t))
    (frame : Data)
    (hm : BinaryArithmetic.toNat (input.stacks 194) = 3^t)
    (hw : (input.stacks 202).length = baseWidth 3 t)
    (hreader : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), frame.stacks i = []) :
    ∃ out : Data, RunsIn program (recoveryBudget Q J t d (input.stacks 194) (input.stacks 202)+1)
      ((install frame input).withPC (some program.entry)) (out.withPC none) ∧
      BinaryArithmetic.toNat (out.stacks 323) = count ∧
      (out.stacks 323).length = (input.stacks 194).length+baseWidth 3 t ∧
      out.stacks 324 = [] ∧ out.stacks 5 = [] ∧ out.stacks 10 = [] ∧
      out.stacks = Function.update (install frame input).stacks 323 (out.stacks 323) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = (install frame input).regs i) := by
  obtain ⟨k,out,hk,he,hvalue,hlen,h324,h5,h10,hstacks,hregs⟩ :=
    command_correct t ht hd a M cache hcanon hzbits J hJpos hB nodes jets minusOne hminus
      input hscalar scalarWidth polyFrame hpoly hclean hzero hone hneg hJ hnodes hjets
      hexponent hprecision hdistinct target hdegree htargetJets count m n hcount hlarge htarget
      frame hm hw hreader
  exact ⟨out,⟨k+1,by omega,compiled_halt_trace he 256 323⟩,
    hvalue,hlen,h324,h5,h10,hstacks,hregs⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
