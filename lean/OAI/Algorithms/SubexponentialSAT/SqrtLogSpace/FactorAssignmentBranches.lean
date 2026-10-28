import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorInput

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

/-- Exact state after the paid factor-ID copy and its guarded pop. -/
noncomputable def identified (a : FactorAssignmentProgram.Data) (factor : ℕ) : FactorAssignmentProgram.Data :=
  embedState id lowStack a (FactorID.output (projectState id lowStack a) factor)

theorem identify_eval (a : FactorAssignmentProgram.Data) (factor : ℕ)
    (hid : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hout : a.stacks 556 = []) (htmp : a.stacks 359 = []) :
    Eval (liftLow FactorID.command 149 556) (7 * (factor + 1) + 7)
      a (identified a factor) := by
  have he := FactorID.command_eval (projectState id lowStack a) factor hid hout htmp
  have hh := eval_liftCommand_from_state FactorID.command 149 556 id lowStack a
    Function.injective_id (Fin.castAdd_injective _ _) he
  unfold liftLow identified
  convert hh using 1

theorem identified_stacks (a : FactorAssignmentProgram.Data) (factor : ℕ) :
    (identified a factor).stacks = Function.update a.stacks 556 (List.replicate factor true) := by
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, identified, embedState_stack id lowStack a _ (Fin.castAdd_injective _ _) j]
    by_cases h556 : j = 556
    · rw [h556]
      rfl
    · have hne : lowStack j ≠ (556 : Fin 896) := by
        intro he
        apply h556
        apply Fin.ext
        have hv := congrArg (fun k : Fin 896 => k.val) he
        exact hv
      simp [FactorID.output, Function.update_of_ne h556,
        Function.update_of_ne hne, projectState]
  · have h556 : i ≠ 556 := by
      intro he
      have hv := congrArg (fun k : Fin 896 => k.val) he
      change i.val = 556 at hv
      omega
    rw [identified, embedState_stack_frame _ _ _ _ i, Function.update_of_ne h556]
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega


noncomputable def tableInput (a : FactorAssignmentProgram.Data) (factor : ℕ) :=
  projectState FactorTableProgram.callerRegisters id (identified a factor)

noncomputable def tableTime {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n B S : ℕ) (a : FactorAssignmentProgram.Data) (factor : ℕ) : ℕ :=
  FactorTableSpace.commandBudget B n
    (FactorTableNative.specializedLiteralWork p u J n S
      ((FactorTableProgram.staged (tableInput a factor)).stacks 574).length)
    (FactorTableNative.specializedPayloadBound n u J (baseWidth 3 p.t) d)

/-- The source table is generated on this very run after the unary factor ID
has been constructed. Its actual dictionary witnesses are returned unchanged. -/
theorem prepareIncidence_eval {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (hout : a.stacks 556 = []) (htmp : a.stacks 359 = [])
    (hready : FactorTableNative.Ready p ps P u J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    ∃ (incidence : Fin n → List (Product.Entry n (baseWidth 3 p.t) d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (Product.bytes (incidence v)).length ≤
        FactorTableNative.specializedPayloadBound n u J (baseWidth 3 p.t) d) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P u J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      steps ≤ 7 * (f + 1) + 7 + tableTime p u J n B S a f ∧
      Eval FactorAssignmentProgram.prepareIncidence steps a e ∧
      e.stacks = Function.update a.stacks 62
        (Squarefree.Program.lookupRecords (Cost.entries incidence)) := by
  have hclean : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 →
      (identified a f).stacks i = [] := by
    intro i hi h62 h556
    rw [identified_stacks, Function.update_of_ne h556]
    exact hblank i hi h62 h556
  obtain ⟨incidence,steps,e,hgood,hlen,hmeaning,hsteps,he,hstore,_,_,_⟩ :=
    FactorTableNative.caller_native_resources (identified a f) hready hclean
  refine ⟨incidence,7*(f+1)+7+steps,e,hgood,hlen,hmeaning,
    Nat.add_le_add_left hsteps _,(identify_eval a f hid hout htmp).seq he,?_⟩
  rw [hstore, identified_stacks]
  funext i
  by_cases h62 : i = 62
  · subst i; rfl
  · by_cases h556 : i = 556
    · subst i; simp [hout]
    · simp [Function.update_of_ne h62, Function.update_of_ne h556]


/-- The marked branch moves the actual parsed clause into the native reader,
evaluates it, and multiplies it into the retained group product. -/
theorem marked_arithmetic_eval {t n d : ℕ} (ctx : Context 3 t n d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
    (houtput : a.stacks 63 = [])
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i)
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch, a.stacks (Clause.callerStacks i) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    let result := Product.run 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (FactorServices.clauseResult ctx minus one incidence ls) []
    ∃ steps e,
      steps ≤ 9 * (a.stacks 154).length + 8 +
        FactorEvaluationSpace.serviceBudget (baseWidth 3 t) d n ctx.u ctx.J ls.length 0 0 ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic) steps a e ∧
      e.stacks = Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 154 []) 63 []) 67 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  let mid := Factor.moved a 154 63
  have hm : mid.stacks = Function.update (Function.update a.stacks 63 (a.stacks 154)) 154 [] := by
    simp [mid, Factor.moved, houtput]
  have hmlow : ∀ i, mid.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i := by
    intro i
    have hn (j : Fin 768) (hj : 56 ≤ j.val) :
        Clause.callerStacks (Memory.lowPort i) ≠ j := Factor.low_ne i j hj
    rw [hm, Function.update_of_ne (hn 154 (by decide)),
      Function.update_of_ne (hn 63 (by decide))]
    exact hlow i
  have hmwork : ∀ i ∈ FactorServices.clauseScratch,
      mid.stacks (Clause.callerStacks i) = [] := by
    intro i hi
    have hn : Clause.callerStacks i ≠ 154 ∧ Clause.callerStacks i ≠ 63 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch,
        Clause.callerStacks i ≠ 154 ∧ Clause.callerStacks i ≠ 63) i hi
    rw [hm, Function.update_of_ne hn.1, Function.update_of_ne hn.2]
    exact hwork i hi
  obtain ⟨steps,e,hsteps,hgood,he,hstore,_,_⟩ :=
    FactorEvaluationSpace.markedArithmetic_run_space ctx minus one seed incidence hone hseed hi ls mid
      hmlow (by simpa [hm] using hraw) (by simpa [hm] using htable)
      (by simpa [hm] using honeTape) (by simpa [hm] using hminus) hmwork
      (by simpa [hm] using hseedTape) (by simpa [hm] using htmp)
  refine ⟨9 * (a.stacks 154).length + 8 + steps,e,Nat.add_le_add_left hsteps _,hgood,
    (Factor.move_eval a 154 63 (by decide) (by decide) (by decide) htmp).seq he,?_⟩
  rw [hstore,hm]
  funext i
  by_cases h154 : i = 154 <;> by_cases h63 : i = 63 <;>
    by_cases h67 : i = 67 <;> by_cases h62 : i = 62 <;> by_cases h151 : i = 151 <;>
    simp [h154, h63, h67, h62, h151]


/-- Original row expansion and native indicator evaluation share the same
empty-support dictionary witnesses and fixed polynomial arithmetic budget. -/
theorem hash_arithmetic_eval {t n d : ℕ} (ctx : Context 3 t n d)
    (ht : 0 < t) (hd : 0 < d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t)))
    (b width : ℕ) (hb : 0 < b)
    (hbound : 3 * (HashInputProgram.Expansion.encodedClauses source).length ≤ 2 ^ b)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow t d source terms,
      w.literals.length ≤ width)
    (a : Factor.Data) (hin : Factor.HashInput ctx minus one seed source terms digits b a)
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence)) :
    let result := Product.run 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (Indicator.result ctx minus one incidence
        (HashInputProgram.Expansion.weightedRow t d source terms) digits) []
    ∃ steps e,
      steps ≤ 9 * (a.stacks 154).length + 10 +
        HashInputProgram.Loop.uniformBudget t (d-1) b (a.stacks 707)
          (HashInputProgram.Expansion.encodedClauses source) terms.length +
        FactorEvaluationSpace.serviceBudget (baseWidth 3 t) d n ctx.u ctx.J
          width terms.length digits.length ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic) steps a e ∧
      e.stacks = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151
          (Product.bytes result) := by
  dsimp only
  obtain ⟨steps,e,hsteps,he,hstore⟩ := Factor.expanded_hash_eval ctx ht hd minus one seed incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    source terms digits b hb hbound a hin.raw hin.formula hin.width hin.modulus
    hin.ringShape hin.output hin.expand hin.work358 hin.work359 hin.low
    htable hin.one hin.minus hin.tape hin.shape hin.work hin.seed hin.temporary
  have hwork := FactorEvaluationSpace.hashWork_polynomial ctx hu hJ
    minus one seed incidence hone hseed hi
    (HashInputProgram.Expansion.weightedRow t d source terms) digits width hwidth
  rw [HashInputProgram.Expansion.weightedRow_length] at hwork
  rw [htable] at hsteps
  have hgood := product_good 3 t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J seed _ hseed
    (FactorEvaluationSpace.result_good ctx hu hJ minus one incidence
      hone hi (HashInputProgram.Expansion.weightedRow t d source terms) digits)
  exact ⟨steps,e,by omega,hgood,he,hstore⟩


/-- A marked factor is computed entirely from retained physical words. The
returned specialized incidence dictionaries are the very witnesses used by
the clause arithmetic; the complete private table bank is restored. -/
theorem markedFactor_eval {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (ls : List (SAT.Literal (Fin n))) (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556 = []) (h359 : a.stacks 359 = []) (h62 : a.stacks 62 = [])
    (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
    (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
    (houtput : a.stacks 63 = [])
    (hlow : ∀ i, a.stacks (lowStack (Clause.callerStacks (Memory.lowPort i))) = low ctx i)
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,
      a.stacks (lowStack (Clause.callerStacks i)) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
        (FactorServices.clauseResult ctx minus one incidence ls) []
      steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
        (9 * (a.stacks 154).length + 9 +
          FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J ls.length 0 0) ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval FactorAssignmentProgram.markedFactor steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result) := by
  obtain ⟨incidence,ki,mid,hgood,_,hmeaning,hki,hei,hm⟩ :=
    prepareIncidence_eval p ps P ctx.u ctx.J f B S theta a hid h556 h359 hready hblank
  let small := projectState id lowStack mid
  have frame (i : Fin 768) (hi : i ≠ 62) : small.stacks i = a.stacks (lowStack i) := by
    change mid.stacks (lowStack i) = _
    rw [hm, Function.update_of_ne]
    intro he
    exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))
  have lowReady : ∀ i, small.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i := by
    intro i
    exact (frame (Clause.callerStacks (Memory.lowPort i))
      (show Clause.callerStacks (Memory.lowPort i) ≠ 62 from
        Factor.low_ne i 62 (by decide))).trans (hlow i)
  have workReady : ∀ i ∈ FactorServices.clauseScratch,
      small.stacks (Clause.callerStacks i) = [] := by
    intro i hi
    have hn : Clause.callerStacks i ≠ 62 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch, Clause.callerStacks i ≠ 62) i hi
    rw [frame _ hn]
    exact hwork i hi
  have ht : small.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence) := by
    change mid.stacks 62 = _
    simp [hm]
  obtain ⟨ka,z,hka,hresult,hea,hz⟩ := marked_arithmetic_eval ctx minus one seed incidence
    hone hseed (fun v => ⟨(hgood v).valid,(hgood v).nodup⟩) ls small
    ((frame 154 (by decide)).trans hraw) ((frame 63 (by decide)).trans houtput)
    lowReady ht ((frame 69 (by decide)).trans honeTape)
    ((frame 76 (by decide)).trans hminus) workReady
    ((frame 151 (by decide)).trans hseedTape) ((frame 159 (by decide)).trans htmp)
  let e := embedState id lowStack mid z
  have her : Eval (liftLow (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic)
      154 151) (ka+1) mid e :=
    eval_liftCommand_from_state _ 154 151 id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _) hea
  have hbase : Function.extend lowStack small.stacks mid.stacks = mid.stacks :=
    congrArg (fun state : State 40 896 => state.stacks) (embedState_project id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _))
  have hstore : e.stacks = Function.update (Function.update (Function.update (Function.update
      (Function.update mid.stacks 154 []) 63 []) 67 []) 62 []) 151
        (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls) [])) := by
    change Function.extend lowStack z.stacks mid.stacks = _
    rw [hz]
    rw [ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),hbase]
    rfl
  have h67 : a.stacks 67 = [] := hwork 67 (by decide)
  refine ⟨incidence,ki+(ka+1),e,hgood,hmeaning,?_,hresult,hei.seq her,?_⟩
  · rw [frame 154 (by decide)] at hka
    rw [show lowStack (154 : Fin 768) = (154 : Fin 896) from rfl] at hka
    omega
  · rw [hstore,hm]
    funext i
    by_cases h154 : i = 154 <;> by_cases h63 : i = 63 <;>
      by_cases hi67 : i = 67 <;> by_cases hi62 : i = 62 <;> by_cases h151 : i = 151 <;>
      simp [h154, h63, hi67, hi62, h151, houtput, h67, h62]


/-- Ordinary factors read the selected original raw row, expand its original
clauses, apply the actual idempotent program, and multiply only after immediate
correction specialization. No expanded row or incidence service is assumed. -/
theorem hashFactor_eval {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b width : ℕ) (hb : 0 < b)
    (hbound : 3 * (HashInputProgram.Expansion.encodedClauses source).length ≤ 2 ^ b)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow p.t d source terms,
      w.literals.length ≤ width)
    (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556 = []) (h62 : a.stacks 62 = [])
    (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
    (hin : Factor.HashInput ctx minus one seed source terms digits b
      (projectState id lowStack a)) :
    ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
        (Indicator.result ctx minus one incidence
          (HashInputProgram.Expansion.weightedRow p.t d source terms) digits) []
      steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
        (9 * (a.stacks 154).length + 11 +
          HashInputProgram.Loop.uniformBudget p.t (d-1) b (a.stacks 707)
            (HashInputProgram.Expansion.encodedClauses source) terms.length +
          FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J
            width terms.length digits.length) ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval FactorAssignmentProgram.hashFactor steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result) := by
  obtain ⟨incidence,ki,mid,hgood,_,hmeaning,hki,hei,hm⟩ :=
    prepareIncidence_eval p ps P ctx.u ctx.J f B S theta a hid h556 hin.work359 hready hblank
  let small := projectState id lowStack mid
  have frame (i : Fin 768) (hi : i ≠ 62) : small.stacks i = a.stacks (lowStack i) := by
    change mid.stacks (lowStack i) = _
    rw [hm, Function.update_of_ne]
    intro he
    exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))
  have hinput : Factor.HashInput ctx minus one seed source terms digits b small :=
    hin.frame frame
  have ht : small.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence) := by
    change mid.stacks 62 = _
    simp [hm]
  obtain ⟨ka,z,hka,hresult,hea,hz⟩ := hash_arithmetic_eval ctx p.ht p.hd
    hready.positiveU hready.positiveJ minus one seed incidence hone hseed
    (fun v => ⟨(hgood v).valid,(hgood v).nodup⟩) source terms digits b width hb hbound hwidth
    small hinput ht
  rw [frame 154 (by decide),frame 707 (by decide)] at hka
  rw [show lowStack (154 : Fin 768) = (154 : Fin 896) from rfl,
    show lowStack (707 : Fin 768) = (707 : Fin 896) from rfl] at hka
  let e := embedState id lowStack mid z
  have her : Eval (liftLow (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic)
      154 151) (ka+1) mid e :=
    eval_liftCommand_from_state _ 154 151 id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _) hea
  have hbase : Function.extend lowStack small.stacks mid.stacks = mid.stacks :=
    congrArg (fun state : State 40 896 => state.stacks) (embedState_project id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _))
  have hstore : e.stacks = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mid.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151
        (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence
            (HashInputProgram.Expansion.weightedRow p.t d source terms) digits) [])) := by
    change Function.extend lowStack z.stacks mid.stacks = _
    rw [hz]
    rw [ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),hbase]
    rfl
  have h64 : a.stacks 64 = [] := hin.output
  have h67 : a.stacks 67 = [] := hin.work 67 (by decide)
  have h68 : a.stacks 68 = [] := hin.work 68 (by decide)
  refine ⟨incidence,ki+(ka+1),e,hgood,hmeaning,?_,hresult,hei.seq her,?_⟩
  · omega
  · rw [hstore,hm]
    funext i
    by_cases h154 : i = 154 <;> by_cases hi64 : i = 64 <;>
      by_cases hi67 : i = 67 <;> by_cases hi68 : i = 68 <;>
      by_cases hi62 : i = 62 <;> by_cases h151 : i = 151 <;>
      simp [h154, hi64, hi67, hi68, hi62, h151, h64, h67, h68, h62]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
