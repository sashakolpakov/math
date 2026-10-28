import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountCorrect

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

abbrev Data := State 40 768

def canonicalWideRead : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram ReconstructionSpace.canonicalQueryProgram
    LeafProgram.QueryReadback.Wide.regMap LeafProgram.QueryReadback.Wide.stackMap)

def command : Cmd 40 768 :=
  .seq LeafProgram.Count.reconstruct
    (.seq canonicalWideRead LeafProgram.Count.clearCaches)

def program := compiled command 256 323

def budget (S : ℕ) : ℕ :=
  2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 +
    4400*(2*(S+1)^2+1)^2 + 4*S+7

/-- The recovery degree is fixed before every input. -/
theorem budget_polynomial (S : ℕ) :
    budget S ≤ (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608)*(S+1)^96 := by
  have hpositive : 0 < S+1 := Nat.succ_pos S
  have hone : 1 ≤ (S+1)^2 := Nat.one_le_pow _ _ hpositive
  have hfour : (S+1)^4 ≤ (S+1)^96 := Nat.pow_le_pow_right hpositive (by decide)
  have hlinear : S+1 ≤ (S+1)^96 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpositive (show 1 ≤ 96 by decide)
  have hsquare : (2*(S+1)^2+1)^2 ≤ 9*(S+1)^4 := by
    have h := Nat.pow_le_pow_left (show 2*(S+1)^2+1 ≤ 3*(S+1)^2 by omega) 2
    convert h using 1
    ring
  have hread : 4400*(2*(S+1)^2+1)^2 ≤ 39600*(S+1)^96 := by
    calc
      _ ≤ 4400*(9*(S+1)^4) := Nat.mul_le_mul_left 4400 hsquare
      _ = 39600*(S+1)^4 := by ring
      _ ≤ 39600*(S+1)^96 := Nat.mul_le_mul_left 39600 hfour
  have hrest : 4*S+8 ≤ 8*(S+1)^96 := by omega
  unfold budget
  calc
    _ ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96 +
        39600*(S+1)^96 + 8*(S+1)^96 := by omega
    _ = _ := by ring

/-- The physically staged scalar is decoded and normalized by the same actual
fixed reader, embedded identically into lower330 of the768-stack workspace. -/
theorem canonical_wide_read (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
    (a : Data) (hvalue : a.stacks 261 = RingProgram.flat x)
    (hm : BinaryArithmetic.toNat (a.stacks 194) = 3^t)
    (hw : (a.stacks 202).length = baseWidth 3 t)
    (hempty : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i = [])
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : (a.stacks 194).length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ (steps : ℕ) (regs : Fin 8 → Bool), steps ≤ 4400*(S+1)^2 ∧
      Eval canonicalWideRead steps a
        (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count)) := by
  let q := LeafProgram.QueryReadback.Wide.project a
  have hs : q.stacks 323 = [] := hempty 323 (by simp)
  have ha : q.stacks 324 = [] := hempty 324 (by simp)
  have hr : LeafProgram.QueryReadback.project q =
      SubexpFlatCount.start (q.regs ∘ LeafProgram.QueryReadback.regMap)
        (a.stacks 194) (a.stacks 202) (RingProgram.flat x) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [LeafProgram.QueryReadback.stackMap,q,
          LeafProgram.QueryReadback.Wide.project,LeafProgram.QueryReadback.Wide.stackMap,
          SubexpFlatCount.store,hvalue,hempty 325 (by simp),
          hempty 326 (by simp),hempty 327 (by simp),hempty 328 (by simp),hempty 329 (by simp)]
  obtain ⟨steps,b,hsteps,_,htrace,_,_,_,⟨regs,hb⟩,_⟩ :=
    ReconstructionSpace.canonical_query_run_space t ht hd model M cache x count hcount hx q
      (q.regs ∘ LeafProgram.QueryReadback.regMap) (a.stacks 194) (a.stacks 202)
      hm hw hr hs ha S hB hmodulus hinput
  change b = LeafProgram.QueryReadback.finish q regs (DisjointReuse.binaryNat count)
    (a.stacks 194) (a.stacks 202) at hb
  rw [hb] at htrace
  have he := eval_call_lifted ReconstructionSpace.canonicalQueryProgram
    LeafProgram.QueryReadback.Wide.regMap LeafProgram.QueryReadback.Wide.stackMap a
    LeafProgram.QueryReadback.Wide.regMap_injective
    LeafProgram.QueryReadback.Wide.stackMap_injective htrace
  change Eval canonicalWideRead (steps+1)
    (LeafProgram.QueryReadback.Wide.install a q)
    (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count)) at he
  rw [LeafProgram.QueryReadback.Wide.install_project] at he
  exact ⟨steps+1,regs,hsteps,he⟩

/-- Complete canonical recovery on one actual trace. This is an internal
composition theorem: its stored jets and target correctness are not final
algorithmic premises, and must be discharged by the streaming query producer. -/
theorem run_space (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
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
    (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
    (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
    (hmodsize : (input.stacks 194).length ≤ S)
    (hwidthsize : (input.stacks 202).length ≤ S)
    (frame : Data)
    (hm : BinaryArithmetic.toNat (input.stacks 194) = 3^t)
    (hw : (input.stacks 202).length = baseWidth 3 t)
    (hreader : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), frame.stacks i = []) :
    ∃ steps out, steps+1 ≤ budget S ∧
      Eval command steps (install frame input) out ∧
      Trace program (steps+1) ((install frame input).withPC (some program.entry))
        (out.withPC none) ∧
      out.stacks = Function.update (install frame input).stacks 323
        (DisjointReuse.binaryNat count) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = (install frame input).regs i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace program prefixSteps ((install frame input).withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits (install frame input).stacks + budget S := by
  obtain ⟨b,rf,nr,hnr,hr,hb,_,_⟩ :=
    ReconstructionSpace.reconstruct_run_space t ht hd a M cache hcanon hzbits J hJpos hB
      nodes jets minusOne hminus input hscalar scalarWidth polyFrame hpoly hclean
      hzero hone hneg hJ hnodes hjets hexponent hprecision hdistinct target hdegree htargetJets
      S hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize count m n hcount hlarge htarget
  let localOut : SubexpCRTOuterProgram.Data :=
    ⟨rf,Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩
  let middle := install frame localOut
  have hre : Eval LeafProgram.Count.reconstruct nr (install frame input) middle :=
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
  have hmod : (middle.stacks 194).length ≤ 2*(S+1)^2 := by
    rw [h194]
    nlinarith only [hmodsize]
  have hbase : baseWidth 3 t ≤ 2*(S+1)^2 := by
    rw [RingProgram.ternary_baseWidth]
    nlinarith only [htsize]
  have hflat : (RingProgram.flat b).length ≤ 2*(S+1)^2 := by
    rw [RingProgram.flat_length,RingProgram.ternary_baseWidth]
    have hprod := Nat.mul_le_mul hdsize htsize
    nlinarith only [hprod]
  obtain ⟨nk,rr,hnk,her⟩ := canonical_wide_read t ht hd a M cache b count
    (hcount.trans_lt hlarge) hb middle hv (by simpa only [h194] using hm)
      (by simpa only [h202] using hw) he (2*(S+1)^2) hbase hmod hflat
  let afterRead := LeafProgram.QueryReadback.Wide.completed middle rr (DisjointReuse.binaryNat count)
  have hf5 : afterRead.stacks 5 = input.stacks 194 := by
    rw [LeafProgram.QueryReadback.Wide.completed_frame middle rr _ 5 (by decide),h5]
  have hf10 : afterRead.stacks 10 = input.stacks 202 := by
    rw [LeafProgram.QueryReadback.Wide.completed_frame middle rr _ 10 (by decide),h10]
  let nc := 2*(afterRead.stacks 5).length+2*(afterRead.stacks 10).length+6
  have hcost : nr+(nk+nc)+1 ≤ budget S := by
    dsimp only [nc]
    rw [hf5,hf10]
    unfold budget
    omega
  have heval : Eval command (nr+(nk+nc)) (install frame input) (cachesCleared afterRead) :=
    hre.seq (her.seq (clearCaches_eval afterRead))
  have hstart (j : Fin 320) : (install frame input).stacks (crtStacks j) = input.stacks j :=
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
  have hstore := readback_cleanup_stacks (install frame input) middle rr (DisjointReuse.binaryNat count)
    (input.stacks 194) (input.stacks 202) (RingProgram.flat b) hmiddle hstart5 hstart10 hstart261 he
  refine ⟨nr+(nk+nc),cachesCleared afterRead,hcost,heval,compiled_halt_trace heval 256 323,hstore,?_,?_⟩
  · intro i hi
    rw [cachesCleared_register_frame afterRead i (by omega)]
    rw [LeafProgram.QueryReadback.Wide.completed_register_frame middle rr _ i (by omega)]
    exact (install_register_outside frame localOut i hi).trans
      (install_register_outside frame input i hi).symm
  · intro prefixSteps intermediate hprefix hp
    exact StructuredSpace.local_stack_bound program (steps := budget S) (by rfl)
      prefixSteps intermediate (hprefix.trans hcost) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
