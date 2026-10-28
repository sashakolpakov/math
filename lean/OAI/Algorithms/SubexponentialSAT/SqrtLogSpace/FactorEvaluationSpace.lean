import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBoundsPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorValue
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

/-! Immediate correction specialization keeps every factor dictionary over the
empty formal-variable support. The retained key capacity is polynomial u*J.
The bounds below apply to the actual native indicator, clause and product
programs, including their input parsers and paid tape cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics FactorBounds

variable {p t n d : ℕ} [Fact p.Prime]

@[simp] theorem empty_capacity (u J : ℕ) (hJ : 0 < J) :
    IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) u J = u * J := by
  simp [IdempotentApplyProgram.Bounds.capacity, Squarefree.Sparse.supportUniverse,
    Finset.filter_singleton, hJ]

theorem rawHash_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d)) :
    Good (∅ : Finset (Fin n)) ctx.u ctx.J (Indicator.rawHash ctx minus one incidence ws) :=
  row_fold_good p t ctx.modulus ctx.cache ctx.table (∅ : Finset (Fin n)) ctx.u ctx.J
    minus one incidence hone hi ws [] Good.nil

theorem result_good (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) :
    Good (∅ : Finset (Fin n)) ctx.u ctx.J (Indicator.result ctx minus one incidence ws digits) := by
  have hh := rawHash_good ctx minus one incidence hone hi ws
  have hp := IdempotentApplyProgram.Bounds.prepared_bounded ctx (∅ : Finset (Fin n)) minus
    (Indicator.rawHash ctx minus one incidence ws) one hh.valid (indicator_good_iff.mpr hone)
  exact indicator_good_iff.mp (IdempotentApplyProgram.Bounds.loopResult_good ctx (∅ : Finset (Fin n))
    hu hJ _ _ hh.valid hp.1 digits.reverse []
      (IdempotentApplyProgram.Bounds.good_nil (∅ : Finset (Fin n)) ctx.u ctx.J))

omit [Fact p.Prime] in
theorem table_length (ctx : Context p t n d)
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v)) :
    (Squarefree.Program.lookupRecords (Cost.entries incidence)).length ≤
      tableBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) := by
  have hp := fun v => Cost.good_bytes (hi v) (le_refl
    (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
  simpa only [Cost.entries,LookupBounds.incidence_entries_length,tableBound] using
    LookupBounds.records_length (Cost.entries incidence) n _
      (LookupBounds.incidence_key_length _ ())
      (LookupBounds.incidence_payload_length _ () _ hp)

theorem productBudget_le (ctx : Context p t n d)
    (seed factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hs : Good (∅ : Finset (Fin n)) ctx.u ctx.J seed)
    (hf : Good (∅ : Finset (Fin n)) ctx.u ctx.J factor) :
    Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor ≤
      56*Cost.bytesBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)+
      Cost.productBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)+54 := by
  have hcap := le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)
  have bs := Cost.good_bytes hs hcap
  have bf := Cost.good_bytes hf hcap
  have br := Cost.good_bytes (product_good p t ctx.modulus ctx.cache ctx.table
    (∅ : Finset (Fin n)) ctx.u ctx.J seed factor hs hf) hcap
  have hw := Cost.product_le p t ctx.modulus ctx.cache ctx.table hcap seed factor hs hf
  dsimp only [Factor.productBudget]
  omega

theorem indicatorBudget_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits ≤
      Cost.programBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) k ws.length+
      IdempotentApplyProgram.Bounds.totalEnvelope (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) digits.length+4 := by
  have hh := rawHash_good ctx minus one incidence hone hi ws
  have hc := Cost.program_le p t ctx.modulus ctx.cache ctx.table
    (le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
    minus one incidence hone hi (List.replicate d true) (by simp) ws k hk
  have ha := IdempotentApplyProgram.Bounds.totalCost_le ctx (∅ : Finset (Fin n)) hu hJ minus
    (Indicator.rawHash ctx minus one incidence ws) one
    (IdempotentApplyProgram.Bounds.good_bounded ctx (∅ : Finset (Fin n)) _ (indicator_good_iff.mpr hh))
    (indicator_good_iff.mpr hone) digits
  change IdempotentApplyProgram.applicationBudget _ _ _ _ _ ≤ _ at ha
  unfold FactorServices.indicatorBudget
  omega

theorem hashService_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one) (hs : Good (∅ : Finset (Fin n)) ctx.u ctx.J seed)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits+
      (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
        2*(Squarefree.Program.lookupRecords (Cost.entries incidence)).length+6+
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)) ≤
      hashServiceBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) k ws.length digits.length := by
  have h1 := indicatorBudget_le ctx hu hJ minus one incidence hone hi ws digits k hk
  have h2 := table_length ctx incidence hi
  have h3 := Cost.good_bytes (rawHash_good ctx minus one incidence hone hi ws)
    (le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
  have h4 := productBudget_le ctx seed _ hs (result_good ctx hu hJ minus one incidence hone hi ws digits)
  unfold hashServiceBound
  omega

theorem clauseResult_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    Good (∅ : Finset (Fin n)) ctx.u ctx.J (FactorServices.clauseResult ctx minus one incidence ls) :=
  clause_fold_good p t ctx.modulus ctx.cache ctx.table (∅ : Finset (Fin n)) ctx.u ctx.J
    minus one incidence hone hi ls one hone

theorem markedService_le (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one) (hs : Good (∅ : Finset (Fin n)) ctx.u ctx.J seed)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls+
      (2*(Squarefree.Program.lookupRecords (Cost.entries incidence)).length+3+
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls)) ≤
      markedServiceBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) ls.length := by
  have h1 := Cost.clause_le p t ctx.modulus ctx.cache ctx.table
    (le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
    minus one incidence hone hi (List.replicate d true) (by simp) ls one hone
  have h2 := table_length ctx incidence hi
  have h3 := Cost.good_bytes hone
    (le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
  have h4 := productBudget_le ctx seed _ hs (clauseResult_good ctx minus one incidence hone hi ls)
  unfold FactorServices.clauseBudget markedServiceBound
  omega


/-- All numerical arguments are encoded dimensions or polynomial retained
capacity. The exponent is fixed independently of every input. -/
def inputScale (B d n u J k m L : ℕ) : ℕ :=
  B + d + n + u + J + u * J + k + m + L + 1

def serviceBudget (B d n u J k m L : ℕ) : ℕ :=
  14000000 * (inputScale B d n u J k m L) ^ 9

theorem empty_capacity_le (u J : ℕ) :
    IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) u J ≤ u * J := by
  have h : (Squarefree.Sparse.supportUniverse (∅ : Finset (Fin n)) J).card ≤ 1 := by
    calc
      _ ≤ ((∅ : Finset (Fin n)).powerset).card := Finset.card_filter_le _ _
      _ = 1 := by simp
  simpa only [IdempotentApplyProgram.Bounds.capacity, Nat.mul_one] using
    Nat.mul_le_mul_left (u * J) h

theorem indicatorBudget_polynomial (ctx : Context p t n d)
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length := by
  have hs := hashService_le ctx hu hJ minus one one incidence hone hone hi ws digits k hk
  have hc := empty_capacity_le (n:=n) ctx.u ctx.J
  let Z := inputScale (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length
  have hp := FactorBounds.hashServiceBound_le (baseWidth p t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) ctx.u ctx.J)
    k ws.length digits.length Z
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
  change _ ≤ 14000000 * Z ^ 9
  omega

theorem clauseBudget_polynomial (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0 := by
  have hs := markedService_le ctx minus one one incidence hone hone hi ls
  have hc := empty_capacity_le (n:=n) ctx.u ctx.J
  let Z := inputScale (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
  have hZ : 1 ≤ Z := by dsimp [Z, inputScale]; omega
  have hp := FactorBounds.markedServiceBound_le (baseWidth p t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) ctx.u ctx.J)
    ls.length Z hZ
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega)
  have hpow : Z ^ 8 ≤ Z ^ 9 := Nat.pow_le_pow_right hZ (by decide)
  change _ ≤ 14000000 * Z ^ 9
  omega

/-- Concrete wide indicator execution, its actual result, and total space at
all prefixes of the same compiled run. Only its polynomial local runtime is
used to control allocation; this estimate is never applied to the exponential
outer traversal. -/
theorem indicator_run_space (ctx : Context p t n d) (hd : 0 < d)
    (hB : 0 < baseWidth p t) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (width : ℕ) (hwidth : ∀ w ∈ ws, w.literals.length ≤ width)
    (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Factor.indicatorStacks (Memory.lowPort i)) = low ctx i)
    (hsource : a.stacks 64 = Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (htape : a.stacks 143 = IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length = n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch, a.stacks (Factor.indicatorStacks i) = []) :
    let budget := serviceBudget (baseWidth p t) d n ctx.u ctx.J width ws.length digits.length
    let output := Indicator.result ctx minus one incidence ws digits
    let program := compiled Factor.indicator 64 67
    ∃ steps rr, steps ≤ budget ∧ Good ∅ ctx.u ctx.J output ∧
      Eval Factor.indicator steps a (FactorServices.indicatorFinished a rr
        (Product.bytes (Indicator.rawHash ctx minus one incidence ws)) (Product.bytes output)) ∧
      Trace program (steps + 1) (a.withPC (some program.entry))
        ((FactorServices.indicatorFinished a rr
          (Product.bytes (Indicator.rawHash ctx minus one incidence ws))
          (Product.bytes output)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  obtain ⟨steps, rr, hs, he⟩ := FactorServices.indicator_eval ctx hd hB minus one incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    ws digits a hlow hsource htable honeTape hminus htape hshape hwork
  have hb := hs.trans (indicatorBudget_polynomial ctx hu hJ minus one incidence hone hi
    ws digits width hwidth)
  refine ⟨steps, rr, hb, result_good ctx hu hJ minus one incidence hone hi ws digits,
    he, compiled_halt_trace he 64 67, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled Factor.indicator 64 67) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

theorem clause_run_space (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i)
    (hsource : a.stacks 63 = Encoding.encodeList id (ls.map Clause.literalBits))
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch, a.stacks (Clause.callerStacks i) = []) :
    let budget := serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
    let output := FactorServices.clauseResult ctx minus one incidence ls
    let program := compiled Clause.caller 63 67
    ∃ steps rr, steps ≤ budget ∧ Good ∅ ctx.u ctx.J output ∧
      Eval Clause.caller steps a (FactorServices.clauseFinished a rr (Product.bytes output)) ∧
      Trace program (steps + 1) (a.withPC (some program.entry))
        ((FactorServices.clauseFinished a rr (Product.bytes output)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  obtain ⟨steps, rr, hs, he⟩ := FactorServices.clause_eval ctx minus one incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    ls a hlow hsource htable honeTape hminus hwork
  have hb := hs.trans (clauseBudget_polynomial ctx minus one incidence hone hi ls)
  refine ⟨steps, rr, hb, clauseResult_good ctx minus one incidence hone hi ls,
    he, compiled_halt_trace he 63 67, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled Clause.caller 63 67) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

theorem hashWork_polynomial (ctx : Context p t n d)
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits +
      (2 * (Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length +
        2 * (Squarefree.Program.lookupRecords (Cost.entries incidence)).length + 6 +
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)) ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length := by
  have hs := hashService_le ctx hu hJ minus one seed incidence hone hseed hi ws digits k hk
  have hc := empty_capacity_le (n:=n) ctx.u ctx.J
  let Z := inputScale (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length
  exact hs.trans (FactorBounds.hashServiceBound_le (baseWidth p t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) ctx.u ctx.J)
    k ws.length digits.length Z
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega))

theorem markedWork_polynomial (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls +
      (2 * (Squarefree.Program.lookupRecords (Cost.entries incidence)).length + 3 +
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls)) ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0 := by
  have hs := markedService_le ctx minus one seed incidence hone hseed hi ls
  have hc := empty_capacity_le (n:=n) ctx.u ctx.J
  let Z := inputScale (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
  have hZ : 1 ≤ Z := by dsimp [Z, inputScale]; omega
  have hp := FactorBounds.markedServiceBound_le (baseWidth p t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) ctx.u ctx.J)
    ls.length Z hZ
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega)
  have hpow : Z ^ 8 ≤ Z ^ 9 := Nat.pow_le_pow_right hZ (by decide)
  change _ ≤ 14000000 * Z ^ 9
  omega

theorem hashArithmetic_run_space (ctx : Context p t n d) (hd : 0 < d)
    (hB : 0 < baseWidth p t) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (width : ℕ) (hwidth : ∀ w ∈ ws, w.literals.length ≤ width)
    (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Factor.indicatorStacks (Memory.lowPort i)) = low ctx i)
    (hsource : a.stacks 64 = Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (htape : a.stacks 143 = IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length = n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch, a.stacks (Factor.indicatorStacks i) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    let budget := serviceBudget (baseWidth p t) d n ctx.u ctx.J width ws.length digits.length
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (Indicator.result ctx minus one incidence ws digits) []
    let program := compiled hashArithmetic 64 151
    ∃ steps b, steps ≤ budget ∧ Good ∅ ctx.u ctx.J result ∧
      Eval hashArithmetic steps a b ∧
      b.stacks = Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result) ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  obtain ⟨steps, b, hs, he, hb⟩ := Factor.hash_value_eval ctx hd hB minus one seed incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    ws digits a hlow hsource htable honeTape hminus htape hshape hwork hseedTape htmp
  rw [htable] at hs
  have hbound := hs.trans (hashWork_polynomial ctx hu hJ minus one seed incidence hone hseed hi
    ws digits width hwidth)
  have hgood := product_good p t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J seed _ hseed
    (result_good ctx hu hJ minus one incidence hone hi ws digits)
  refine ⟨steps, b, hbound, hgood, he, hb, compiled_halt_trace he 64 151, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled hashArithmetic 64 151) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

theorem markedArithmetic_run_space (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i)
    (hsource : a.stacks 63 = Encoding.encodeList id (ls.map Clause.literalBits))
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch, a.stacks (Clause.callerStacks i) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    let budget := serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (FactorServices.clauseResult ctx minus one incidence ls) []
    let program := compiled markedArithmetic 63 151
    ∃ steps b, steps ≤ budget ∧ Good ∅ ctx.u ctx.J result ∧
      Eval markedArithmetic steps a b ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result) ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  obtain ⟨steps, b, hs, he, hb⟩ := Factor.marked_value_eval ctx minus one seed incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    ls a hlow hsource htable honeTape hminus hwork hseedTape htmp
  rw [htable] at hs
  have hbound := hs.trans (markedWork_polynomial ctx minus one seed incidence hone hseed hi ls)
  have hgood := product_good p t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J seed _ hseed
    (clauseResult_good ctx minus one incidence hone hi ls)
  refine ⟨steps, b, hbound, hgood, he, hb, compiled_halt_trace he 63 151, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled markedArithmetic 63 151) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
