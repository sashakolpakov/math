import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceSize
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateCostBounds
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyBound
import OAI.Algorithms.SubexponentialSAT.SubexpTableSourceBounds

namespace OAI.Algorithms

/-! Input-size bounds for the actual moment-source constructor. Every local
coefficient payload is charged through its serialized template bytes. -/

namespace SubexponentialSAT.SubexpMomentSourceInputBounds

open SubexpMomentSourceProgram
open SubexpTemplateCostBounds (mass encoded_length sum_le_mass encoded_map_le)

abbrev Bits := List Bool

def sizeParameter (ctx : Context) : ℕ :=
  ctx.dimension + ctx.width.length + ctx.target.length +
    SubexpSymbolicCost.indexBits ctx.dimension + ctx.zero.length + ctx.one.length + 1

def weightUnit (ctx : Context) : ℕ := literalBytes ctx.dimension ctx.target.length + 1
def frameUnit (ctx : Context) : ℕ := uniformFrameBudget ctx.dimension ctx.target.length
def termUnit (ctx : Context) : ℕ := frameUnit ctx + 20 * weightUnit ctx + 40
def groupUnit (ctx : Context) : ℕ := frameUnit ctx + 40 * weightUnit ctx + 100
def blockUnit (ctx : Context) : ℕ := 2 * frameUnit ctx + 80 * weightUnit ctx + 200
def preparationUnit (ctx : Context) : ℕ := 2 * frameUnit ctx + 100 * weightUnit ctx + 300

theorem weightUnit_pos (ctx : Context) : 1 ≤ weightUnit ctx := by unfold weightUnit; omega

theorem mass_le_encoded {α : Type*} (enc : α → Bits) (xs : List α) :
    mass enc xs ≤ (Encoding.encodeList enc xs).length + 1 := by
  have h := encoded_length enc xs
  omega

theorem uniformScan_le_encoded {α : Type*} (enc : α → Bits) (cost : α → ℕ)
    (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, cost x ≤ K * ((enc x).length + 1)) :
    uniformScan enc cost xs ≤ (K + 20) * ((Encoding.encodeList enc xs).length + 1) := by
  have hs : uniformScan enc cost xs ≤ (K + 20) * mass enc xs := by
    apply sum_le_mass
    intro x hx
    have hc := h x hx
    nlinarith
  exact hs.trans (Nat.mul_le_mul_left _ (mass_le_encoded enc xs))

theorem descriptor_length_ge (d : Descriptor) : 2 ≤ (encodeDescriptor d).length := by
  simp only [encodeDescriptor, List.length_append, Encoding.length_frame]
  omega

theorem prepared_term_length (ctx : Context) (t : TermData ctx) :
    (SubexpBlockAssembly.encodeTerm (uniformPreparedTerm t)).length + 1 ≤
      weightUnit ctx * ((encodeTerm t.template).length + 1) := by
  have hd := descriptor_length_ge t.point.descriptor
  have hU := weightUnit_pos ctx
  have hm := Nat.mul_le_mul_right
    (Encoding.encodeList SubexpTableSource.encodeRows t.factors).length hU
  simp only [weightUnit, uniformPreparedTerm, uniformWeight, List.length_replicate,
    SubexpBlockAssembly.encodeTerm, encodeTerm, TermData.template,
    List.length_append, Encoding.length_frame] at *
  nlinarith [Nat.zero_le (literalBytes ctx.dimension ctx.target.length *
    (encodeDescriptor t.point.descriptor).length)]

theorem prepared_group_length (ctx : Context) (ts : List (TermData ctx)) :
    (SubexpBlockAssembly.encodeGroup (ts.map uniformPreparedTerm)).length + 1 ≤
      weightUnit ctx * ((encodeGroup (ts.map TermData.template)).length + 1) := by
  have h := encoded_map_le (fun t : TermData ctx => encodeTerm t.template)
    (fun t => SubexpBlockAssembly.encodeTerm (uniformPreparedTerm t)) ts
    (weightUnit ctx) (weightUnit_pos ctx) (fun t _ => prepared_term_length ctx t)
  simpa only [SubexpBlockAssembly.encodeGroup, encodeGroup,
    SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem prepared_groups_length (ctx : Context) (gs : List (List (TermData ctx))) :
    (Encoding.encodeList SubexpBlockAssembly.encodeGroup
      (gs.map (List.map uniformPreparedTerm))).length + 1 ≤
      weightUnit ctx * ((Encoding.encodeList encodeGroup
        (gs.map (List.map TermData.template))).length + 1) := by
  have h := encoded_map_le
    (fun ts : List (TermData ctx) => encodeGroup (ts.map TermData.template))
    (fun ts => SubexpBlockAssembly.encodeGroup (ts.map uniformPreparedTerm)) gs
    (weightUnit ctx) (weightUnit_pos ctx) (fun ts _ => prepared_group_length ctx ts)
  simpa only [SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem prepared_block_length (ctx : Context) (b : BlockData ctx) :
    (SubexpBlockAssembly.encodeBlock (uniformPreparedBlock b)).length + 1 ≤
      weightUnit ctx * ((encodeBlock b.template).length + 1) := by
  have hg := prepared_groups_length ctx b.groups
  have hd := descriptor_length_ge b.point.descriptor
  have hm := Nat.mul_le_mul_left (weightUnit ctx) hd
  simp only [uniformPreparedBlock, SubexpBlockAssembly.encodeBlock,
    uniformWeight, List.length_replicate, encodeBlock, BlockData.template,
    List.length_append, Encoding.length_frame]
  unfold weightUnit at *
  nlinarith

theorem prepared_blocks_length (ctx : Context) (bs : List (BlockData ctx)) :
    (SubexpBlockAssembly.encodeBlocks (uniformPreparedBlocks bs)).length + 1 ≤
      weightUnit ctx * ((encodeTemplate (bs.map BlockData.template)).length + 1) := by
  have h := encoded_map_le (fun b : BlockData ctx => encodeBlock b.template)
    (fun b => SubexpBlockAssembly.encodeBlock (uniformPreparedBlock b)) bs
    (weightUnit ctx) (weightUnit_pos ctx) (fun b _ => prepared_block_length ctx b)
  simpa only [SubexpBlockAssembly.encodeBlocks, uniformPreparedBlocks, encodeTemplate,
    SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem uniformTermBudget_le (ctx : Context) (t : TermData ctx) :
    uniformTermBudget ctx t ≤ termUnit ctx * ((encodeTerm t.template).length + 1) := by
  let R := (encodeTerm t.template).length + 1
  have hp := prepared_term_length ctx t
  have hf : (Encoding.encodeList SubexpTableSource.encodeRows t.factors).length ≤ R := by
    simp only [R, encodeTerm, TermData.template, List.length_append, Encoding.length_frame]
    omega
  have hc : frameUnit ctx + 28 ≤ (frameUnit ctx + 28) * R :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hf' := Nat.mul_le_mul_left 12 hf
  have hp' := Nat.mul_le_mul_left 13 hp
  have hU := Nat.mul_le_mul_right R (show 0 ≤ 7 * weightUnit ctx by omega)
  unfold uniformTermBudget termUnit frameUnit at *
  dsimp only [R] at *
  nlinarith

theorem uniformGroupBudget_le (ctx : Context) (ts : List (TermData ctx)) :
    uniformGroupBudget ctx ts ≤ groupUnit ctx *
      ((encodeGroup (ts.map TermData.template)).length + 1) := by
  have hs := uniformScan_le_encoded (fun t : TermData ctx => encodeTerm t.template)
    (uniformTermBudget ctx) ts (termUnit ctx) (fun t _ => uniformTermBudget_le ctx t)
  have hp := prepared_group_length ctx ts
  have hc := Nat.le_mul_of_pos_right 21
    (Nat.succ_pos (encodeGroup (ts.map TermData.template)).length)
  simp only [encodeGroup, SubexpBlueprintRows.encodeList_map] at hp hc ⊢
  unfold uniformGroupBudget groupUnit
  unfold termUnit at hs
  nlinarith [Nat.zero_le (weightUnit ctx *
    ((Encoding.encodeList (fun t : TermData ctx => encodeTerm t.template) ts).length + 1))]

theorem uniformBlockBudget_le (ctx : Context) (b : BlockData ctx) :
    uniformBlockBudget ctx b ≤ blockUnit ctx * ((encodeBlock b.template).length + 1) := by
  let R := (encodeBlock b.template).length + 1
  let G := (Encoding.encodeList encodeGroup (b.groups.map (List.map TermData.template))).length + 1
  have hGR : G ≤ R := by
    simp only [G, R, encodeBlock, BlockData.template, List.length_append]
    omega
  have hs := uniformScan_le_encoded
    (fun ts : List (TermData ctx) => encodeGroup (ts.map TermData.template))
    (uniformGroupBudget ctx) b.groups (groupUnit ctx) (fun ts _ => uniformGroupBudget_le ctx ts)
  have hs' : uniformScan (fun ts => encodeGroup (ts.map TermData.template))
      (uniformGroupBudget ctx) b.groups ≤ (groupUnit ctx + 20) * R := by
    apply hs.trans
    apply Nat.mul_le_mul_left
    simpa only [G, SubexpBlueprintRows.encodeList_map, Function.comp_def] using hGR
  have hg := (prepared_groups_length ctx b.groups).trans
    (Nat.mul_le_mul_left (weightUnit ctx) hGR)
  have hp := prepared_block_length ctx b
  have hc : frameUnit ctx + 28 ≤ (frameUnit ctx + 28) * R :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold uniformBlockBudget blockUnit groupUnit frameUnit at *
  dsimp only [R] at *
  nlinarith [Nat.zero_le (weightUnit ctx *
    ((encodeBlock b.template).length + 1))]

theorem uniformPreparationBudget_le (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    uniformPreparationBudget ctx bs ≤ preparationUnit ctx * (ctx.template.length + 1) := by
  have hs := uniformScan_le_encoded (fun b : BlockData ctx => encodeBlock b.template)
    (uniformBlockBudget ctx) bs (blockUnit ctx) (fun b _ => uniformBlockBudget_le ctx b)
  have hp := prepared_blocks_length ctx bs
  have he : (Encoding.encodeList (fun b : BlockData ctx => encodeBlock b.template) bs).length =
      ctx.template.length := by
    rw [htemplate]
    simp only [encodeTemplate, SubexpBlueprintRows.encodeList_map]
  rw [he] at hs
  rw [← htemplate] at hp
  have hc := Nat.le_mul_of_pos_right 19 (Nat.succ_pos ctx.template.length)
  unfold uniformPreparationBudget preparationUnit
  unfold blockUnit at hs
  nlinarith [Nat.zero_le (weightUnit ctx * (ctx.template.length + 1))]

theorem sum_square_encoded {α : Type*} (enc : α → Bits) (cost : α → ℕ)
    (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, cost x ≤ K * ((enc x).length + 1)^2) :
    (xs.map cost).sum ≤ K * ((Encoding.encodeList enc xs).length + 1)^2 :=
  (SubexpTableSourceBounds.sum_le_square_mass enc cost xs K h).trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_left (mass_le_encoded enc xs) 2))

def baseUnit (zero one : Bits) : ℕ := zero.length + one.length + 1

theorem baseUnit_pos (zero one : Bits) : 1 ≤ baseUnit zero one := by
  unfold baseUnit
  omega

theorem factorProduct_length_le (zero one : Bits) (fs : List (List SubexpTableSource.Row)) :
    (SubexpBlockAssembly.factorProduct zero one fs).length + 1 ≤
      2000 * baseUnit zero one *
        ((Encoding.encodeList SubexpTableSource.encodeRows fs).length + 1)^2 := by
  let H := baseUnit zero one
  let N := (Encoding.encodeList SubexpTableSource.encodeRows fs).length + 1
  have hH : 1 ≤ H := baseUnit_pos zero one
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hs := sum_square_encoded SubexpTableSource.encodeRows
    (fun rows => (SubexpTableSource.tableCode zero one rows).length) fs (1000 * H)
    (fun rows _ => SubexpTableSourceBounds.tableCode_length_le zero one rows)
  have hn : fs.length ≤ N := by
    have h := Encoding.length_encodeList_lower SubexpTableSource.encodeRows fs
    dsimp [N]
    omega
  have hpow : N ≤ N^2 := by nlinarith only [hN]
  have hscale : N ≤ H * N^2 :=
    hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hOne : one.length + 1 ≤ H * N^2 :=
    (show one.length + 1 ≤ H by dsimp [H, baseUnit]; omega).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  simp only [SubexpBlockAssembly.factorProduct, List.length_append, List.length_flatten,
    List.map_map, Function.comp_def, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length]
  change _ ≤ 2000 * H * N^2
  change _ ≤ 1000 * H * N^2 at hs
  nlinarith only [hs, hn, hscale, hOne, hH, hN,
    Nat.zero_le (H * N^2)]

theorem pair_size_bound (a e b K : ℕ) (hK : 1 ≤ K)
    (hb : b + 1 ≤ K * (e + 1)^2) :
    2*a + 2*b + 6 ≤ 4*K*(2*a + e + 2)^2 := by
  let N := 2*a + e + 2
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hb' : b + 1 ≤ K * N^2 :=
    hb.trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left (by dsimp [N]; omega) 2))
  have hpow : N ≤ N^2 := by nlinarith only [hN]
  have hscale : N ≤ K * N^2 :=
    hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  have ha : 2*a + 4 ≤ 2*N := by dsimp [N]; omega
  change _ ≤ 4*K*N^2
  nlinarith only [hb', hscale, ha]

theorem compiled_term_length_le (zero one : Bits) (t : SubexpBlockAssembly.Term) :
    (SubexpKernelControl.encodeTerm (SubexpBlockAssembly.compiledTerm zero one t)).length + 1 ≤
      8000 * baseUnit zero one * ((SubexpBlockAssembly.encodeTerm t).length + 1)^2 := by
  have h := pair_size_bound t.weight.length
    (Encoding.encodeList SubexpTableSource.encodeRows t.factors).length
    (SubexpBlockAssembly.factorProduct zero one t.factors).length
    (2000 * baseUnit zero one) (by have := baseUnit_pos zero one; omega)
    (factorProduct_length_le zero one t.factors)
  simp only [SubexpKernelControl.encodeTerm, SubexpBlockAssembly.compiledTerm,
    SubexpBlockAssembly.encodeTerm, Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil, id_eq, List.length_append, Encoding.length_frame]
  ring_nf at h ⊢
  exact h

theorem compiled_group_length_le (zero one : Bits) (ts : List SubexpBlockAssembly.Term) :
    (SubexpKernelControl.encodeGroup (ts.map (SubexpBlockAssembly.compiledTerm zero one))).length + 1 ≤
      8000 * baseUnit zero one * ((SubexpBlockAssembly.encodeGroup ts).length + 1)^2 := by
  have h := SubexpTableSourceBounds.encoded_map_square SubexpBlockAssembly.encodeTerm
    (fun t => SubexpKernelControl.encodeTerm (SubexpBlockAssembly.compiledTerm zero one t))
    ts (8000 * baseUnit zero one) (by have := baseUnit_pos zero one; omega)
    (fun t _ => compiled_term_length_le zero one t)
  simpa only [SubexpKernelControl.encodeGroup, SubexpBlockAssembly.encodeGroup,
    SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem compiled_groups_length_le (zero one : Bits) (gs : List (List SubexpBlockAssembly.Term)) :
    (Encoding.encodeList SubexpKernelControl.encodeGroup
      (gs.map (List.map (SubexpBlockAssembly.compiledTerm zero one)))).length + 1 ≤
      8000 * baseUnit zero one * ((Encoding.encodeList SubexpBlockAssembly.encodeGroup gs).length + 1)^2 := by
  have h := SubexpTableSourceBounds.encoded_map_square SubexpBlockAssembly.encodeGroup
    (fun ts => SubexpKernelControl.encodeGroup (ts.map (SubexpBlockAssembly.compiledTerm zero one)))
    gs (8000 * baseUnit zero one) (by have := baseUnit_pos zero one; omega)
    (fun ts _ => compiled_group_length_le zero one ts)
  simpa only [SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem compiled_block_length_le (zero one : Bits) (b : SubexpBlockAssembly.Block) :
    (SubexpKernelControl.encodeBlock (SubexpBlockAssembly.compiledBlock zero one b)).length + 1 ≤
      32000 * baseUnit zero one * ((SubexpBlockAssembly.encodeBlock b).length + 1)^2 := by
  have h := pair_size_bound b.outside.length
    (Encoding.encodeList SubexpBlockAssembly.encodeGroup b.groups).length
    (Encoding.encodeList SubexpKernelControl.encodeGroup
      (b.groups.map (List.map (SubexpBlockAssembly.compiledTerm zero one)))).length
    (8000 * baseUnit zero one) (by have := baseUnit_pos zero one; omega)
    (compiled_groups_length_le zero one b.groups)
  simp only [SubexpKernelControl.encodeBlock, SubexpBlockAssembly.compiledBlock,
    SubexpBlockAssembly.encodeBlock, Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil, id_eq, List.length_append, Encoding.length_frame]
  ring_nf at h ⊢
  exact h

theorem assembled_length_le (zero one : Bits) (bs : List SubexpBlockAssembly.Block) :
    (SubexpBlockAssembly.assembled zero one bs).length + 1 ≤
      32000 * baseUnit zero one * ((SubexpBlockAssembly.encodeBlocks bs).length + 1)^2 := by
  have h := SubexpTableSourceBounds.encoded_map_square SubexpBlockAssembly.encodeBlock
    (fun b => SubexpKernelControl.encodeBlock (SubexpBlockAssembly.compiledBlock zero one b))
    bs (32000 * baseUnit zero one) (by have := baseUnit_pos zero one; omega)
    (fun b _ => compiled_block_length_le zero one b)
  simpa only [SubexpBlockAssembly.assembled, SubexpKernelControl.encodeBlocks,
    SubexpBlockAssembly.encodeBlocks, SubexpBlueprintRows.encodeList_map, Function.comp_def] using h

theorem factorWork_le (zero one : Bits) (fs : List (List SubexpTableSource.Row)) :
    SubexpBlockAssembly.factorWork zero one fs ≤ 1000 * baseUnit zero one *
      ((Encoding.encodeList SubexpTableSource.encodeRows fs).length + 1)^2 :=
  sum_square_encoded SubexpTableSource.encodeRows (SubexpTableSource.tableCost zero one)
    fs (1000 * baseUnit zero one) (fun rows _ => SubexpTableSourceBounds.tableCost_le zero one rows)

theorem termWork_le (zero one : Bits) (t : SubexpBlockAssembly.Term) :
    SubexpBlockAssembly.termWork zero one t ≤ 1000 * baseUnit zero one *
      ((SubexpBlockAssembly.encodeTerm t).length + 1)^2 := by
  apply (factorWork_le zero one t.factors).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [SubexpBlockAssembly.encodeTerm, List.length_append, Encoding.length_frame]
  omega

theorem groupWork_le (zero one : Bits) (ts : List SubexpBlockAssembly.Term) :
    SubexpBlockAssembly.groupWork zero one ts ≤ 1000 * baseUnit zero one *
      ((SubexpBlockAssembly.encodeGroup ts).length + 1)^2 :=
  sum_square_encoded SubexpBlockAssembly.encodeTerm (SubexpBlockAssembly.termWork zero one)
    ts (1000 * baseUnit zero one) (fun t _ => termWork_le zero one t)

theorem blockWork_le (zero one : Bits) (b : SubexpBlockAssembly.Block) :
    SubexpBlockAssembly.blockWork zero one b ≤ 1000 * baseUnit zero one *
      ((SubexpBlockAssembly.encodeBlock b).length + 1)^2 := by
  apply (sum_square_encoded SubexpBlockAssembly.encodeGroup
    (SubexpBlockAssembly.groupWork zero one) b.groups (1000 * baseUnit zero one)
    (fun ts _ => groupWork_le zero one ts)).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [SubexpBlockAssembly.encodeBlock, List.length_append, Encoding.length_frame]
  omega

theorem tableWork_le (zero one : Bits) (bs : List SubexpBlockAssembly.Block) :
    SubexpBlockAssembly.tableWork zero one bs ≤ 1000 * baseUnit zero one *
      ((SubexpBlockAssembly.encodeBlocks bs).length + 1)^2 :=
  sum_square_encoded SubexpBlockAssembly.encodeBlock (SubexpBlockAssembly.blockWork zero one)
    bs (1000 * baseUnit zero one) (fun b _ => blockWork_le zero one b)

theorem assemblySteps_le (zero one : Bits) (bs : List SubexpBlockAssembly.Block) :
    SubexpBlockAssembly.assemblySteps zero one bs ≤ 1000000 * baseUnit zero one *
      ((SubexpBlockAssembly.encodeBlocks bs).length + 1)^2 := by
  have h := SubexpBlockAssembly.assemblySteps_le zero one bs
  have hw := tableWork_le zero one bs
  have hl := assembled_length_le zero one bs
  let N := (SubexpBlockAssembly.encodeBlocks bs).length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hpow : N ≤ N^2 := by nlinarith only [hN]
  have hi : (SubexpBlockAssembly.encodeBlocks bs).length ≤ baseUnit zero one * N^2 :=
    (Nat.le_succ _).trans (hpow.trans (Nat.le_mul_of_pos_left _
      (by have := baseUnit_pos zero one; omega)))
  change _ ≤ 1000000 * baseUnit zero one * N^2
  change _ ≤ 1000 * baseUnit zero one * N^2 at hw
  change _ ≤ 32000 * baseUnit zero one * N^2 at hl
  nlinarith only [h, hw, hl, hi, Nat.zero_le (baseUnit zero one * N^2)]

theorem sizeParameter_pos (ctx : Context) : 1 ≤ sizeParameter ctx := by
  unfold sizeParameter
  omega

theorem baseUnit_le (ctx : Context) : baseUnit ctx.zero ctx.one ≤ sizeParameter ctx := by
  unfold baseUnit sizeParameter
  omega

theorem weightUnit_le (ctx : Context) : weightUnit ctx ≤ 28 * sizeParameter ctx := by
  unfold weightUnit literalBytes sizeParameter
  omega

def frameMajorant (W : ℕ) : ℕ :=
  W*(32*W^2+161*W+14*W*W+40*W+184) +
    ((2*W+1)*(6010*(W+1)^2+16*(2*W+1)+16) +
      W*(5*W+8*W+24*(2*W+1)+37)+3) +
    173*W+12*W+32*W+117 + 17*W*W+15*(1+(2*W+2)*W)+31 + 40*W+160*W+82

theorem frameUnit_le (ctx : Context) : frameUnit ctx ≤ 1000000 * (sizeParameter ctx)^3 := by
  let W := sizeParameter ctx
  have hW : 1 ≤ W := sizeParameter_pos ctx
  have hD : ctx.dimension ≤ W := by dsimp [W, sizeParameter]; omega
  have hB : ctx.target.length ≤ W := by dsimp [W, sizeParameter]; omega
  have hI : SubexpSymbolicCost.indexBits ctx.dimension ≤ W := by dsimp [W, sizeParameter]; omega
  have hm : frameUnit ctx ≤ frameMajorant W := by
    unfold frameUnit uniformFrameBudget uniformCaptureBudget uniformDescriptorBudget
      SubexpWeightDescriptorProgram.retainedWeightBudget frameMajorant
    gcongr
  have h1 : W ≤ W^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < W) (by decide : 1 ≤ 3)
  have h2 : W^2 ≤ W^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h0 : 1 ≤ W^3 := hW.trans h1
  apply hm.trans
  unfold frameMajorant
  change _ ≤ 1000000 * W^3
  ring_nf
  omega

theorem preparationUnit_le (ctx : Context) :
    preparationUnit ctx ≤ 4000000 * (sizeParameter ctx)^3 := by
  have hf := frameUnit_le ctx
  have hu := weightUnit_le ctx
  have hS := sizeParameter_pos ctx
  have h1 : sizeParameter ctx ≤ (sizeParameter ctx)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < sizeParameter ctx)
      (by decide : 1 ≤ 3)
  unfold preparationUnit
  omega

theorem prepared_input_le (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    (SubexpBlockAssembly.encodeBlocks (uniformPreparedBlocks bs)).length + 1 ≤
      28 * sizeParameter ctx * (ctx.template.length + 1) := by
  have h := prepared_blocks_length ctx bs
  rw [← htemplate] at h
  exact h.trans (Nat.mul_le_mul_right _ (weightUnit_le ctx))

theorem assembled_input_le (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    (SubexpBlockAssembly.assembled ctx.zero ctx.one (uniformPreparedBlocks bs)).length + 1 ≤
      25088000 * (sizeParameter ctx)^3 * (ctx.template.length + 1)^2 := by
  calc
    _ ≤ 32000 * baseUnit ctx.zero ctx.one *
        ((SubexpBlockAssembly.encodeBlocks (uniformPreparedBlocks bs)).length + 1)^2 :=
      assembled_length_le ctx.zero ctx.one _
    _ ≤ 32000 * sizeParameter ctx * (28 * sizeParameter ctx * (ctx.template.length + 1))^2 := by
      gcongr
      · exact baseUnit_le ctx
      · exact prepared_input_le ctx bs htemplate
    _ = _ := by ring

theorem assemblySteps_input_le (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    SubexpBlockAssembly.assemblySteps ctx.zero ctx.one (uniformPreparedBlocks bs) ≤
      784000000 * (sizeParameter ctx)^3 * (ctx.template.length + 1)^2 := by
  calc
    _ ≤ 1000000 * baseUnit ctx.zero ctx.one *
        ((SubexpBlockAssembly.encodeBlocks (uniformPreparedBlocks bs)).length + 1)^2 :=
      assemblySteps_le ctx.zero ctx.one _
    _ ≤ 1000000 * sizeParameter ctx * (28 * sizeParameter ctx * (ctx.template.length + 1))^2 := by
      gcongr
      · exact baseUnit_le ctx
      · exact prepared_input_le ctx bs htemplate
    _ = _ := by ring

theorem uniformSourceBytes_le_small (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    uniformSourceBytes ctx bs ≤
      3411968000 * (sizeParameter ctx)^4 * (ctx.template.length + 1)^2 := by
  have hp : 16*ctx.zero.length+8*ctx.one.length+136 ≤ 136 * sizeParameter ctx := by
    unfold sizeParameter
    omega
  have ha := Nat.le_of_succ_le (assembled_input_le ctx bs htemplate)
  calc
    _ ≤ 136 * sizeParameter ctx *
        (25088000 * (sizeParameter ctx)^3 * (ctx.template.length + 1)^2) := Nat.mul_le_mul hp ha
    _ = _ := by ring

def inputBound (ctx : Context) : ℕ :=
  1000000000000 * (sizeParameter ctx)^8 * (ctx.template.length + 1)^2

theorem uniformSourceBytes_le_input (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    uniformSourceBytes ctx bs ≤ inputBound ctx := by
  have hS := sizeParameter_pos ctx
  have h4 : (sizeParameter ctx)^4 ≤ (sizeParameter ctx)^8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  apply (uniformSourceBytes_le_small ctx bs htemplate).trans
  unfold inputBound
  gcongr
  norm_num

theorem uniformTotalBudget_le_input (ctx : Context) (bs : List (BlockData ctx))
    (htemplate : ctx.template = encodeTemplate (bs.map BlockData.template)) :
    uniformTotalBudget ctx bs ≤ inputBound ctx := by
  let S := sizeParameter ctx
  let T := ctx.template.length + 1
  have hS : 1 ≤ S := sizeParameter_pos ctx
  have hT : 1 ≤ T := by dsimp [T]; omega
  have h3 : S^3 ≤ S^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : S^4 ≤ S^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hT2 : T ≤ T^2 := by nlinarith only [hT]
  have hp : uniformPreparationBudget ctx bs ≤ 4000000 * S^8 * T^2 := by
    calc
      _ ≤ preparationUnit ctx * T := uniformPreparationBudget_le ctx bs htemplate
      _ ≤ (4000000 * S^3) * T := Nat.mul_le_mul_right _ (preparationUnit_le ctx)
      _ ≤ _ := by gcongr
  have ha : SubexpBlockAssembly.assemblySteps ctx.zero ctx.one (uniformPreparedBlocks bs) ≤
      784000000 * S^8 * T^2 := by
    apply (assemblySteps_input_le ctx bs htemplate).trans
    change 784000000 * S^3 * T^2 ≤ _
    gcongr
  have hs : uniformSourceBytes ctx bs ≤ 3411968000 * S^8 * T^2 := by
    apply (uniformSourceBytes_le_small ctx bs htemplate).trans
    change 3411968000 * S^4 * T^2 ≤ _
    gcongr
  have hc : 17 ≤ 17 * (S^8 * T^2) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
  unfold uniformTotalBudget inputBound
  change _ ≤ 1000000000000 * S^8 * T^2
  nlinarith only [hp, ha, hs, hc, Nat.zero_le (S^8 * T^2)]

end SubexponentialSAT.SubexpMomentSourceInputBounds

end OAI.Algorithms
