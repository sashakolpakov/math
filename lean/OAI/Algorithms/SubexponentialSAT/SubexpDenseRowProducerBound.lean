import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowServiceBound
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyBound

namespace OAI.Algorithms

/-!
# Concrete uniform bound for the fixed dense-row producer

The auxiliary classifier, emitted-code, and traversal estimates live in
`SubexpDenseRowServiceBound`. The final endpoints instantiate the actual
universal-source polynomial estimate, with no supplied callback cap.
-/

namespace SubexponentialSAT.SubexpDenseRowProducerBound

open BitProgram StructuredCalls SubexpDenseRowTableProgram
open SubexpLiftRing SubexpQuarticRing
open Subexp.ConstructivePacking SubexpDenseRowServiceBound
open SubexpRowPostfixInterpreter (contextStore)

/-- Persistent source-generation data only. The three per-row type/slot
words are bounded from the dimensions instead of from their old contents. -/
def sourceMasterPorts : List (Fin 288) :=
  [128, 129, 131, 132, 133, 134, 135, 136, 137, 243, 252, 253, 254]

def sourceSize (p r Q Δ R : ℕ) (a : Data) : ℕ :=
  r + Q + Δ + R + Subexp.MatrixWordEncoding.width p +
    Subexp.CollisionProgram.typeWidth r Q Δ +
    (sourceMasterPorts.map (fun j => (a.stacks j).length)).sum + 1

theorem sourceSize_parameters (p r Q Δ R : ℕ) (a : Data) :
    1 ≤ sourceSize p r Q Δ R a ∧ r ≤ sourceSize p r Q Δ R a ∧
      Q ≤ sourceSize p r Q Δ R a ∧ Δ ≤ sourceSize p r Q Δ R a ∧
      R ≤ sourceSize p r Q Δ R a ∧
      Subexp.MatrixWordEncoding.width p ≤ sourceSize p r Q Δ R a ∧
      Subexp.CollisionProgram.typeWidth r Q Δ ≤ sourceSize p r Q Δ R a := by
  unfold sourceSize
  omega

theorem sourceMaster_length (p r Q Δ R : ℕ) (a : Data)
    (j : Fin 288) (hj : j ∈ sourceMasterPorts) :
    (a.stacks j).length ≤ sourceSize p r Q Δ R a := by
  have hm : (a.stacks j).length ∈ sourceMasterPorts.map (fun k => (a.stacks k).length) :=
    List.mem_map.mpr ⟨j, hj, rfl⟩
  have hs := List.le_sum_of_mem hm
  unfold sourceSize
  omega

theorem staged_input_lengths {r Q Δ : ℕ} (p R : ℕ) (a : Data) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (j : Fin 288)
    (hj : j ∈ Subexp.UniversalRowAssembly.boundInputPorts) :
    ((SubexpGlobalRowUniversal.inner (SubexpGlobalRowUniversal.staged a i u y)).stacks j).length ≤
      sourceSize p r Q Δ R a := by
  have hd := sourceSize_parameters p r Q Δ R a
  change ((SubexpGlobalRowUniversal.staged a i u y).stacks j).length ≤ _
  by_cases h272 : j = 272
  · subst j
    simpa [SubexpGlobalRowUniversal.staged, Subexp.CollisionProgram.encodeType_length] using hd.2.2.2.2.2.2
  by_cases h275 : j = 275
  · subst j
    simpa [SubexpGlobalRowUniversal.staged, Subexp.CollisionProgram.encodeType_length] using hd.2.2.2.2.2.2
  by_cases h284 : j = 284
  · subst j
    have hi : i.val + 1 ≤ Δ := i.isLt
    simpa [SubexpGlobalRowUniversal.staged, unary] using hi.trans hd.2.2.2.1
  have hm : j ∈ sourceMasterPorts := by
    simp only [Subexp.UniversalRowAssembly.boundInputPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (h272 rfl).elim | exact (h275 rfl).elim |
      exact (h284 rfl).elim | decide
  simpa [SubexpGlobalRowUniversal.staged, h272, h275, h284] using
    sourceMaster_length p r Q Δ R a j hm

theorem sourceSize_sameContext (p r Q Δ R : ℕ) (a b : Data)
    (h : SubexpDenseRowTableAssembly.SameContext a.stacks b.stacks) :
    sourceSize p r Q Δ R b = sourceSize p r Q Δ R a := by
  have hm : sourceMasterPorts.map (fun j => (b.stacks j).length) =
      sourceMasterPorts.map (fun j => (a.stacks j).length) := by
    apply List.map_congr_left
    intro j hj
    have hn : j ∉ SubexpDenseRowTableAssembly.varyingPorts := by
      simp only [sourceMasterPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    exact congrArg List.length (h j hn)
  simp only [sourceSize, hm]

def tableBudget (p r Q Δ D μ R sourceLimit : ℕ) (scopes : List (List ℕ)) (a : Data) : ℕ :=
  tablePolynomialBound (scopesCode scopes).length D
    (uniformRowBound p r Q Δ D μ R sourceLimit scopes a)
    (rowLength p μ R) (a.stacks 265).length

/-- Includes the compiled source producer's halt. -/
def sourceLimit (p r Q Δ R : ℕ) (a : Data) : ℕ :=
  Subexp.UniversalRowAssemblyBound.uniformBound (sourceSize p r Q Δ R a) + 1

/-- An explicit polynomial in the dimensions, selected source-word
lengths, source/target widths, encoded scope lengths and lookup length. -/
def runtimeBound (p r Q Δ D μ R : ℕ) (scopes : List (List ℕ)) (a : Data) : ℕ :=
  tableBudget p r Q Δ D μ R (sourceLimit p r Q Δ R a) scopes a

/-- The full table budget is unchanged by current parser tails, counters,
or previously accumulated rows. -/
theorem runtimeBound_sameContext (p r Q Δ D μ R : ℕ) (scopes : List (List ℕ))
    (a b : Data) (h : SubexpDenseRowTableAssembly.SameContext a.stacks b.stacks) :
    runtimeBound p r Q Δ D μ R scopes b = runtimeBound p r Q Δ D μ R scopes a := by
  have htable : b.stacks 265 = a.stacks 265 := h 265 (by decide)
  simp only [runtimeBound, tableBudget, uniformRowBound, sourceLimit,
    sourceSize_sameContext p r Q Δ R a b h, htable]

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
variable (scopes : List (List ℕ))
  (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The actual source-generation cost is bounded uniformly before any
incidence, ambient coordinate, or pair of types is selected. -/
theorem sourceCost_le (a : Data)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ) :
    SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y ≤
      sourceLimit p r Q Δ xs.length a := by
  rcases sourceSize_parameters p r Q Δ xs.length a with ⟨hS, hr, hQ, hΔ, hR, hb, ht⟩
  have hp := staged_prepared xs inverse negative difference a hm i u y
  have he := Subexp.UniversalRowAssemblyBound.executionBound_le p i u y xs
    inverse negative difference _ hp (sourceSize p r Q Δ xs.length a)
    hS hr hQ hΔ hR hb ht (staged_input_lengths p xs.length a i u y)
  exact Nat.add_le_add_right he 1

theorem rowCost_le (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) (e v w : ℕ) :
    SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a e v w ≤
      uniformRowBound p r Q Δ D μ xs.length (sourceLimit p r Q Δ xs.length a) scopes a :=
  rowCost_le_of_sourceBound μ source xs inverse negative difference P scopes hd a h2 hm htable
    hzero hone _ (sourceCost_le xs inverse negative difference a hm) e v w

theorem rowBounds (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    RowBounds (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
      (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a)
      D (uniformRowBound p r Q Δ D μ xs.length (sourceLimit p r Q Δ xs.length a) scopes a)
      (rowLength p μ xs.length) 0 scopes :=
  rowBounds_of_sourceBound μ source xs inverse negative difference P scopes hd a h2 hm htable
    hzero hone _ (sourceCost_le xs inverse negative difference a hm)

private theorem table_cost_le_of_sourceBound (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (ha : TableReady a D scopes) (sourceLimit : ℕ)
    (hs : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y ≤ sourceLimit) :
    tableRunCost a (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
      (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a)
      D scopes + 1 ≤ tableBudget p r Q Δ D μ xs.length sourceLimit scopes a := by
  exact tableRunCost_add_one_le a _ _ D
    (uniformRowBound p r Q Δ D μ xs.length sourceLimit scopes a) (rowLength p μ xs.length) scopes ha
    (rowBounds_of_sourceBound μ source xs inverse negative difference P scopes hd a h2 hm htable
      hzero hone sourceLimit hs)

theorem tableRunCost_le (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (ha : TableReady a D scopes) :
    tableRunCost a (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
      (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a)
      D scopes + 1 ≤ runtimeBound p r Q Δ D μ xs.length scopes a :=
  table_cost_le_of_sourceBound μ source xs inverse negative difference P scopes hd a h2 hm htable
    hzero hone ha _ (sourceCost_le xs inverse negative difference a hm)

variable (reference : Data)
variable (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D)
variable (h2 : (2 : ZMod p) ≠ 0) (hμ : 0 < μ)
variable (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference reference)
variable (htable : reference.stacks 265 =
  SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
variable (hscopes : reference.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
variable (hclean : SubexpGlobalRowSelection.HighClean reference) (href87 : reference.stacks 87 = [])
variable (hzero : reference.stacks 131 = SubexpFlatAdd.encode source.zero)
variable (hone : reference.stacks 132 = SubexpFlatAdd.encode source.one)
variable (sw tw : Word) (frame : Fin 6 → Word) (context : Fin 252 → Word)
variable (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
  (xs.length + 1) sw frame context)
variable (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
variable (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
variable (hB : tw.length = baseWidth p μ)
variable (hf : ∀ j, reference.stacks (SubexpRowToTaylorCalls.stack j) = contextStore context j)

include hvalid h2 hμ hm htable hscopes hclean href87 hzero hone H hz h74 h87 hB hf

private theorem program_runsIn_of_sourceBound (ha : TableReady reference D scopes)
    (sourceLimit : ℕ)
    (hs : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      SubexpGlobalRowUniversal.sourceCost xs inverse negative difference reference i u y ≤ sourceLimit) :
    ∃ regs, RunsIn SubexpDenseRowProducer.program
      (tableBudget p r Q Δ D μ xs.length sourceLimit scopes reference)
      (reference.withPC (some SubexpDenseRowProducer.program.entry))
      ((tableResult reference regs
        (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D scopes).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := SubexpDenseRowProducer.program_runsIn μ source xs inverse negative difference
    P scopes hd reference hvalid h2 hμ hm htable hscopes hclean href87 hzero hone
    sw tw frame context H hz h74 h87 hB hf ha
  exact ⟨regs, n, hn.trans (table_cost_le_of_sourceBound μ source xs inverse negative difference
    P scopes hd reference h2 hm htable hzero hone ha sourceLimit hs), ht⟩

/-- One fixed finite producer runs within the concrete polynomial bound.
All remaining premises identify physical input words and work readiness. -/
theorem program_runsIn (ha : TableReady reference D scopes) :
    ∃ regs, RunsIn SubexpDenseRowProducer.program
      (runtimeBound p r Q Δ D μ xs.length scopes reference)
      (reference.withPC (some SubexpDenseRowProducer.program.entry))
      ((tableResult reference regs
        (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D scopes).withPC none) :=
  program_runsIn_of_sourceBound μ source xs inverse negative difference P scopes hd reference
    hvalid h2 hμ hm htable hscopes hclean href87 hzero hone sw tw frame context
    H hz h74 h87 hB hf ha _ (sourceCost_le xs inverse negative difference reference hm)

/-- The primitive-machine multiplier depends only on the fixed program. -/
theorem primitive_runsIn (ha : TableReady reference D scopes) :
    ∃ regs, Computation.RunsIn (primitive SubexpDenseRowProducer.program).step
      (primitiveOverhead SubexpDenseRowProducer.program * runtimeBound p r Q Δ D μ xs.length scopes reference)
      (primitiveCfg SubexpDenseRowProducer.program
        (reference.withPC (some SubexpDenseRowProducer.program.entry)))
      (primitiveCfg SubexpDenseRowProducer.program
        ((tableResult reference regs
          (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D scopes).withPC none)) := by
  obtain ⟨regs, hr⟩ := program_runsIn μ source xs inverse negative difference P scopes hd reference
    hvalid h2 hμ hm htable hscopes hclean href87 hzero hone sw tw frame context H hz h74 h87 hB hf ha
  exact ⟨regs, BitProgram.primitive_execution _ hr⟩

end SubexponentialSAT.SubexpDenseRowProducerBound

end OAI.Algorithms
