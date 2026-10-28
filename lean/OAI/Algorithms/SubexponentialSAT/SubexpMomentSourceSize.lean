import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceUniform
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceComplete
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceShape

namespace OAI.Algorithms

/-!
Uniform bounds for the actual current-exponent source constructor.

The words used below are length witnesses. Replacing a computed weight by a
word of the same length preserves every framing length and assembly count.
The execution theorem still uses the computed weights and their real traces.
-/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open scoped BigOperators
open SubexpMomentSourceShape

-- All bounds use the published literal-length theorem. Expanding a symbolic
-- zero key here would only add work to definitional equality checks.
attribute [local irreducible] WeightResult.literal
  SubexpScalarLiteralProgram.rawLiteral SubexpSymbolicCost.fixedKey

/-- A length witness for each computed scalar literal. -/
def uniformWeight (ctx : Context) : Word :=
  List.replicate (literalBytes ctx.dimension ctx.target.length) false

def uniformPreparedTerm {ctx : Context} (t : TermData ctx) : SubexpBlockAssembly.Term :=
  ⟨uniformWeight ctx,t.factors⟩

def uniformPreparedBlock {ctx : Context} (b : BlockData ctx) : SubexpBlockAssembly.Block :=
  ⟨uniformWeight ctx,b.groups.map (List.map uniformPreparedTerm)⟩

def uniformPreparedBlocks {ctx : Context} (bs : List (BlockData ctx)) :
    List SubexpBlockAssembly.Block := bs.map uniformPreparedBlock

private theorem term_uniform_shape {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {t : TermData ctx} {out : TermResult ctx a} (h : out.input = t) :
    SameTermShape out.prepared (uniformPreparedTerm t) := by
  subst t
  constructor
  · simpa only [TermResult.prepared,uniformPreparedTerm,uniformWeight,List.length_replicate]
      using out.weight.literal_length
  · rfl

private theorem group_uniform_shape {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {ts : List (TermData ctx)} {outs : List (TermResult ctx a)}
    (h : List.Forall₂ (fun t out => out.input = t) ts outs) :
    List.Forall₂ SameTermShape (outs.map TermResult.prepared) (ts.map uniformPreparedTerm) :=
  map_related_rev _ _ h (fun _ _ he => term_uniform_shape he)

private theorem block_uniform_shape {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {b : BlockData ctx} {out : BlockResult ctx a} (h : out.input = b) :
    SameBlockShape out.prepared (uniformPreparedBlock b) := by
  subst b
  constructor
  · simpa only [BlockResult.prepared,uniformPreparedBlock,uniformWeight,List.length_replicate]
      using out.weight.literal_length
  · exact map_related_rev _ _ out.agreement (fun _ _ he => group_uniform_shape he)

private theorem blocks_uniform_shape {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {bs : List (BlockData ctx)} {outs : List (BlockResult ctx a)}
    (h : List.Forall₂ (fun b out => out.input = b) bs outs) :
    List.Forall₂ SameBlockShape (preparedBlocks outs) (uniformPreparedBlocks bs) :=
  map_related_rev _ _ h (fun _ _ he => block_uniform_shape he)

def uniformScan {α : Type*} (encode : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => 9*(encode x).length+cost x+11)).sum

private theorem scanSteps_le_uniform {α β : Type*} {R : α → β → Prop}
    (encode : α → Word) (cost : α → β → ℕ) (bound : α → ℕ)
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (hc : ∀ x y, R x y → cost x y ≤ bound x) :
    scanSteps encode cost xs ys ≤ uniformScan encode bound xs := by
  induction h with
  | nil => exact le_rfl
  | cons he ht ih =>
      simp only [scanSteps,List.zipWith_cons_cons,List.sum_cons,uniformScan,List.map_cons] at *
      have hb := hc _ _ he
      omega

def uniformTermBudget (ctx : Context) (t : TermData ctx) : ℕ :=
  uniformFrameBudget ctx.dimension ctx.target.length+
    12*(Encoding.encodeList SubexpTableSource.encodeRows t.factors).length+12+
    13*(SubexpBlockAssembly.encodeTerm (uniformPreparedTerm t)).length+16

def uniformGroupBudget (ctx : Context) (ts : List (TermData ctx)) : ℕ :=
  uniformScan (fun t => encodeTerm t.template) (uniformTermBudget ctx) ts+
    13*(SubexpBlockAssembly.encodeGroup (ts.map uniformPreparedTerm)).length+21

def uniformBlockBudget (ctx : Context) (b : BlockData ctx) : ℕ :=
  uniformFrameBudget ctx.dimension ctx.target.length+28+
    uniformScan (fun ts => encodeGroup (ts.map TermData.template)) (uniformGroupBudget ctx) b.groups+
    6*(Encoding.encodeList SubexpBlockAssembly.encodeGroup
      (b.groups.map (List.map uniformPreparedTerm))).length+
    13*(SubexpBlockAssembly.encodeBlock (uniformPreparedBlock b)).length

def uniformPreparationBudget (ctx : Context) (bs : List (BlockData ctx)) : ℕ :=
  7*ctx.template.length+
    uniformScan (fun b => encodeBlock b.template) (uniformBlockBudget ctx) bs+
    3*(SubexpBlockAssembly.encodeBlocks (uniformPreparedBlocks bs)).length+19

/-- A source-length bound depending only on fixed data and word widths. -/
def uniformSourceBytes (ctx : Context) (bs : List (BlockData ctx)) : ℕ :=
  (16*ctx.zero.length+8*ctx.one.length+136)*
    (SubexpBlockAssembly.assembled ctx.zero ctx.one (uniformPreparedBlocks bs)).length

/-- A bound on the measured source program, independent of the current
exponent and of the contents of its computed weight words. One copy of
`uniformSourceBytes` bounds the kernel, and nine bound the final transfer. -/
def uniformTotalBudget (ctx : Context) (bs : List (BlockData ctx)) : ℕ :=
  uniformPreparationBudget ctx bs+
    SubexpBlockAssembly.assemblySteps ctx.zero ctx.one (uniformPreparedBlocks bs)+
    10*uniformSourceBytes ctx bs+17

/-- Updating the current exponent leaves every reusable data field intact. -/
def Context.withExponent (ctx : Context) (bits : Word) : Context :=
  {ctx with exponent := bits}

def PointData.withExponent {ctx : Context} (p : PointData ctx) (bits : Word) :
    PointData (ctx.withExponent bits) :=
  ⟨p.coordinates,p.support,p.nodup,p.width⟩

def TermData.withExponent {ctx : Context} (t : TermData ctx) (bits : Word) :
    TermData (ctx.withExponent bits) :=
  ⟨t.point.withExponent bits,t.factors⟩

def BlockData.withExponent {ctx : Context} (b : BlockData ctx) (bits : Word) :
    BlockData (ctx.withExponent bits) :=
  ⟨b.point.withExponent bits,b.groups.map (List.map (fun t => t.withExponent bits))⟩

@[simp] theorem PointData.descriptor_withExponent {ctx : Context} (p : PointData ctx)
    (bits : Word) : (p.withExponent bits).descriptor = p.descriptor := rfl

@[simp] theorem TermData.template_withExponent {ctx : Context} (t : TermData ctx)
    (bits : Word) : (t.withExponent bits).template = t.template := rfl

@[simp] theorem BlockData.template_withExponent {ctx : Context} (b : BlockData ctx)
    (bits : Word) : (b.withExponent bits).template = b.template := by
  simp only [BlockData.template,BlockData.withExponent,PointData.descriptor_withExponent,
    List.map_map,Function.comp_def,TermData.template_withExponent]

theorem encodeTemplate_withExponent {ctx : Context} (bs : List (BlockData ctx)) (bits : Word) :
    encodeTemplate ((bs.map (fun b => b.withExponent bits)).map BlockData.template) =
      encodeTemplate (bs.map BlockData.template) := by
  simp only [List.map_map,Function.comp_def,BlockData.template_withExponent]

theorem ContextGood.withExponent {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (a' : Fin ctx.dimension → ℕ) :
    ContextGood (ctx.withExponent (SymbolicCost.unaryWords (List.ofFn a'))) a' :=
  ⟨rfl,hc.indexWidth,hc.padding,hc.unitLength,hc.unitValue,
    hc.modulusLength,hc.positive,hc.capacity⟩

@[simp] theorem uniformPreparedTerm_withExponent {ctx : Context} (t : TermData ctx)
    (bits : Word) : uniformPreparedTerm (t.withExponent bits) = uniformPreparedTerm t := rfl

@[simp] theorem uniformPreparedBlock_withExponent {ctx : Context} (b : BlockData ctx)
    (bits : Word) : uniformPreparedBlock (b.withExponent bits) = uniformPreparedBlock b := by
  apply congrArg₂ SubexpBlockAssembly.Block.mk
  · rfl
  · simp only [BlockData.withExponent]
    rw [List.map_map]
    apply List.map_congr_left
    intro group _
    simp only [List.map_map,Function.comp_def,uniformPreparedTerm_withExponent]

@[simp] theorem uniformPreparedBlocks_withExponent {ctx : Context} (bs : List (BlockData ctx))
    (bits : Word) :
    uniformPreparedBlocks (bs.map (fun b => b.withExponent bits)) = uniformPreparedBlocks bs := by
  simp only [uniformPreparedBlocks,List.map_map,Function.comp_def,uniformPreparedBlock_withExponent]

@[simp] theorem uniformTermBudget_withExponent {ctx : Context} (t : TermData ctx) (bits : Word) :
    uniformTermBudget (ctx.withExponent bits) (t.withExponent bits) = uniformTermBudget ctx t := rfl

@[simp] theorem uniformGroupBudget_withExponent {ctx : Context} (ts : List (TermData ctx))
    (bits : Word) :
    uniformGroupBudget (ctx.withExponent bits) (ts.map (fun t => t.withExponent bits)) =
      uniformGroupBudget ctx ts := by
  simp only [uniformGroupBudget,uniformScan,List.map_map,Function.comp_def,
    TermData.template_withExponent,uniformTermBudget_withExponent,uniformPreparedTerm_withExponent]

@[simp] theorem uniformBlockBudget_withExponent {ctx : Context} (b : BlockData ctx) (bits : Word) :
    uniformBlockBudget (ctx.withExponent bits) (b.withExponent bits) = uniformBlockBudget ctx b := by
  unfold uniformBlockBudget
  rw [uniformPreparedBlock_withExponent]
  simp only [uniformScan,BlockData.withExponent,List.map_map,Function.comp_def,
    TermData.template_withExponent,uniformGroupBudget_withExponent,uniformPreparedTerm_withExponent]
  rfl

@[simp] theorem uniformPreparationBudget_withExponent {ctx : Context} (bs : List (BlockData ctx))
    (bits : Word) :
    uniformPreparationBudget (ctx.withExponent bits) (bs.map (fun b => b.withExponent bits)) =
      uniformPreparationBudget ctx bs := by
  simp only [uniformPreparationBudget,uniformScan,List.map_map,Function.comp_def,
    BlockData.template_withExponent,uniformBlockBudget_withExponent,uniformPreparedBlocks_withExponent]
  rfl

/-- The same output bound applies at every current exponent word. -/
@[simp] theorem uniformSourceBytes_withExponent {ctx : Context} (bs : List (BlockData ctx))
    (bits : Word) :
    uniformSourceBytes (ctx.withExponent bits) (bs.map (fun b => b.withExponent bits)) =
      uniformSourceBytes ctx bs := by
  unfold uniformSourceBytes
  rw [uniformPreparedBlocks_withExponent]
  rfl

/-- The same measured runtime bound applies at every current exponent word. -/
@[simp] theorem uniformTotalBudget_withExponent {ctx : Context} (bs : List (BlockData ctx))
    (bits : Word) :
    uniformTotalBudget (ctx.withExponent bits) (bs.map (fun b => b.withExponent bits)) =
      uniformTotalBudget ctx bs := by
  unfold uniformTotalBudget
  rw [uniformPreparationBudget_withExponent,uniformPreparedBlocks_withExponent,
    uniformSourceBytes_withExponent]
  rfl

theorem termBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {t : TermData ctx} {out : TermResult ctx a} (h : out.input = t) :
    termBudget ctx a t out ≤ uniformTermBudget ctx t := by
  subst t
  have hw := captureBudget_le_uniform hc hdegree out.weight
  have he := term_encoded_length (term_uniform_shape (out := out) rfl)
  unfold termBudget uniformTermBudget uniformFrameBudget
  rw [he]
  omega

theorem groupBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {ts : List (TermData ctx)} {outs : List (TermResult ctx a)}
    (h : List.Forall₂ (fun t out => out.input = t) ts outs) :
    groupBudget ctx a ts outs ≤ uniformGroupBudget ctx ts := by
  have hs := scanSteps_le_uniform (fun t => encodeTerm t.template) (termBudget ctx a)
    (uniformTermBudget ctx) h (fun _ _ he => termBudget_le_uniform hc hdegree he)
  have he := group_encoded_length (group_uniform_shape h)
  unfold groupBudget uniformGroupBudget
  rw [he]
  omega

theorem blockBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {b : BlockData ctx} {out : BlockResult ctx a} (h : out.input = b) :
    blockBudget ctx a b out ≤ uniformBlockBudget ctx b := by
  subst b
  have hw := captureBudget_le_uniform hc hdegree out.weight
  have hs := scanSteps_le_uniform (fun ts => encodeGroup (ts.map TermData.template))
    (groupBudget ctx a) (uniformGroupBudget ctx) out.agreement
    (fun _ _ he => groupBudget_le_uniform hc hdegree he)
  have he := block_encoded_length (block_uniform_shape (out := out) rfl)
  have hg :
      (Encoding.encodeList SubexpBlockAssembly.encodeGroup
        (out.groups.map (List.map TermResult.prepared))).length =
      (Encoding.encodeList SubexpBlockAssembly.encodeGroup
        (out.input.groups.map (List.map uniformPreparedTerm))).length :=
    groups_encoded_length
      (map_related_rev _ _ out.agreement (fun _ _ hr => group_uniform_shape hr))
  unfold blockBudget uniformBlockBudget uniformFrameBudget blockGroupBytes
  rw [he,hg]
  omega

theorem preparationBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {bs : List (BlockData ctx)} {outs : List (BlockResult ctx a)}
    (h : List.Forall₂ (fun b out => out.input = b) bs outs) :
    preparationBudget ctx a bs outs ≤ uniformPreparationBudget ctx bs := by
  have hs := scanSteps_le_uniform (fun b => encodeBlock b.template) (blockBudget ctx a)
    (uniformBlockBudget ctx) h (fun _ _ he => blockBudget_le_uniform hc hdegree he)
  have he := blocks_encoded_length (blocks_uniform_shape h)
  unfold preparationBudget uniformPreparationBudget
  rw [he]
  omega

theorem kernelCost_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {bs : List (BlockData ctx)} {outs : List (BlockResult ctx a)}
    (h : List.Forall₂ (fun b out => out.input = b) bs outs) :
    SubexpKernelControl.kernelCost ctx.zero ctx.one
      ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one)) ≤
      uniformSourceBytes ctx bs := by
  have hk := SubexpKernelControl.kernelCost_le_input ctx.zero ctx.one
    ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one))
  have he := assembled_length_eq ctx.zero ctx.one (blocks_uniform_shape h)
  change (SubexpKernelControl.encodeBlocks _).length = _ at he
  rw [he] at hk
  exact hk

theorem source_length_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {bs : List (BlockData ctx)} {outs : List (BlockResult ctx a)}
    (h : List.Forall₂ (fun b out => out.input = b) bs outs) :
    (source ctx outs).length ≤ uniformSourceBytes ctx bs :=
  (SubexpKernelControl.momentCode_length_le ctx.zero ctx.one
    ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one))).trans
      (kernelCost_le_uniform h)

theorem totalBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {bs : List (BlockData ctx)} {outs : List (BlockResult ctx a)}
    (h : List.Forall₂ (fun b out => out.input = b) bs outs) :
    totalBudget ctx a bs outs ≤ uniformTotalBudget ctx bs := by
  have hp := preparationBudget_le_uniform hc hdegree h
  have ha := assembly_steps_eq ctx.zero ctx.one (blocks_uniform_shape h)
  have hk := kernelCost_le_uniform h
  have hl := source_length_le_uniform h
  unfold totalBudget uniformTotalBudget
  rw [ha]
  omega

/-- The existing finite program satisfies the uniform time and output-size
bounds for every retained current exponent. No execution premise is supplied
by the caller. -/
theorem program_runs_uniform (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    (bs : List (BlockData ctx))
    (hTemplate : ctx.template = encodeTemplate (bs.map BlockData.template))
    (r : Fin 8 → Bool) :
    ∃ (outs : List (BlockResult ctx a)) (rf : Fin 8 → Bool),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      BitProgram.RunsIn program (uniformTotalBudget ctx bs)
        ((state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] []).withPC (some program.entry))
        ((state ctx (flags rf false false false) [] SubexpBlockAssembly.emptyBuffers [] [] []
          (source ctx outs)).withPC none) ∧
      (source ctx outs).length ≤ uniformSourceBytes ctx bs := by
  obtain ⟨outs,rf,h,⟨n,hn,ht⟩⟩ := program_runs ctx a hc bs hTemplate r
  exact ⟨outs,rf,h,⟨n,hn.trans (totalBudget_le_uniform hc hdegree h),ht⟩,
    source_length_le_uniform h⟩

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
