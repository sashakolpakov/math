import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReadout
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRegisterBase

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.RegisterFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lowCore {l : ℕ} (p : Program 8 56 l) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (.call (ProgramLinking.liftProgram p coreRegisters corePorts)) i := by
  apply lifted
  intro j h
  have he := congrArg Fin.val h
  simp [coreRegisters] at he
  omega

theorem weightedAdd (i : Fin 40) (hi : 16 ≤ i.val) : Preserves MomentsAssembly.weightedAdd i :=
  lowCore _ i hi

theorem multiply (i : Fin 40) (hi : 16 ≤ i.val) : Preserves MomentsAssembly.multiply i :=
  lowCore _ i hi

theorem normalize (i : Fin 40) (hi : 16 ≤ i.val) : Preserves MomentsAssembly.normalize i :=
  lowCore _ i hi

theorem project (i : Fin 40) (hi : 16 ≤ i.val) : Preserves MomentsAssembly.project i := by
  apply lifted
  intro j h
  have he := congrArg Fin.val h
  simp [projectionRegisters] at he
  omega

theorem readout (i : Fin 40) (hi : 16 ≤ i.val) : Preserves MomentsAssembly.readout i := by
  apply lifted
  intro j h
  have he := congrArg Fin.val h
  simp [coreRegisters] at he
  omega

/-- The wide producer is the only component that can access registers16+.
The actual composition retains the caller's register frame whenever it does. -/
theorem command (produce : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (hp : Preserves produce i) : Preserves (MomentsAssembly.command produce) i := by
  unfold MomentsAssembly.command bucketStep startBucket finishBucket supportScan supportStep
    startSupport finishSupport headScan headStep startHead finishHead assignmentScan assignmentStep
    moveForward rawScan rawLoop
  repeat' first
    | apply seq
    | apply loop
    | exact hp
    | exact peek _ i hi
    | exact clear _ i hi
    | exact transfer _ _ i hi
    | exact copy _ _ i hi
    | exact takeFrame _ _ _ i hi
    | exact reader _ _ _ i hi
    | exact weightedAdd i hi
    | exact multiply i hi
    | exact normalize i hi
    | exact project i hi

theorem denseCommand (produce : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (hp : Preserves produce i) : Preserves (MomentsAssembly.denseCommand produce) i :=
  seq (command produce i hi hp) (readout i hi)

/-- Apply this to the same actual Eval witness used to compile the worker.
All caller registers16..23 (indeed16..39) are preserved. -/
theorem dense_eval {produce : Code} {n : ℕ} {a b : Data}
    (hp : ∀ i : Fin 40, 16 ≤ i.val → Preserves produce i)
    (h : Eval (MomentsAssembly.denseCommand produce) n a b) :
    ∀ i : Fin 40, 16 ≤ i.val → b.regs i=a.regs i := by
  intro i hi
  exact denseCommand produce i hi (hp i hi) h

end SubexponentialSAT.SqrtLog.MomentsAssembly.RegisterFrame

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- The concrete wide assembly and readout trace, with the register frame
required by the node worker. Compile this same Eval with compiled_halt_trace. -/
theorem denseCommand_eval_framed (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width shape : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hshape : shape.length=n) (u J W : ℕ)
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (hproducer : ∀ i : Fin 40, 16 ≤ i.val → RegisterFrame.Preserves produce i)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (n:=n) validFrame base bs)
    (h102 : base 102 = []) (h190 : base 190 = RingProgram.flat zero) (h191 : base 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, base i = [])
    (hk : ∀ a ∈ bucketsRun p t M cache table u J meaning base ss one bs seed,
      (Squarefree.encodeIndex a.1).length ≤ W) :
    let e := Product.environment p t M cache table degree width u J
    let entries := bucketsRun p t M cache table u J meaning base ss one bs seed
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ k ≤ bucketsWork p t M cache table u J meaning cost base ss one bs seed+
        MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J W entries.length,
      ∃ rr, Eval (denseCommand produce) k
        (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
        (machine rr (emptyCore e) (Function.update (bucketStream base (Product.bytes entries) []) 102 bits)) ∧
        ∀ i : Fin 40, 16 ≤ i.val → rr i=regs i := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let entries := bucketsRun p t M cache table u J meaning base ss one bs seed
  let high := bucketStream base (Product.bytes entries) []
  obtain ⟨na,ha,r1,h1⟩ := command_eval produce p t M cache hz table degree width hd hw u J
    meaning cost validFrame contract one seed ss bs base regs hsupports hone hclean h162 h170 h177 hv
  obtain ⟨nr,hr,r2,h2⟩ := readout_machine_eval p t M cache table entries zero degree width shape u J W r1 high
    hd hw hshape hk (by simp [high,bucketStream,h102]) (by simp [high,bucketStream])
    (by simp [high,bucketStream,h190]) (by simp [high,bucketStream,h191]) (by
      intro i hi
      have hn163 : i ≠ 163 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      simpa [high,bucketStream,hn163,hn166] using hwork i hi)
  have he := h1.seq h2
  dsimp [entries] at hr
  refine ⟨na+nr,by omega,r2,he,?_⟩
  exact RegisterFrame.dense_eval hproducer he

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
