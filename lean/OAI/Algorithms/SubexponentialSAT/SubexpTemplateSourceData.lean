import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateData
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceBlocks

namespace OAI.Algorithms

/-! The concrete unweighted template output supplies the source constructor's
typed inputs. Ordered support and term lists are preserved. The inner point
bank uses the same executed modular addition as the template program. -/

namespace SubexponentialSAT.SubexpTemplateSourceData

open SubexpTemplatePointServices

abbrev SourceContext := SubexpMomentSourceProgram.Context
abbrev TemplateContext := SubexpTemplateProgram.Context

variable {p : ℕ} [Fact p.Prime]

def pointData (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup) :
    SubexpMomentSourceProgram.PointData ctx where
  coordinates i := (words i).val
  support := support
  nodup := hn
  width i := (words i).property.trans hwidth.symm

omit [Fact p.Prime] in
@[simp] theorem pointData_coordinates (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup) (i : Fin ctx.dimension) :
    (pointData ctx hwidth words support hn).coordinates i = (words i).val := rfl

omit [Fact p.Prime] in
@[simp] theorem pointData_support (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup) :
    (pointData ctx hwidth words support hn).support = support := rfl

omit [Fact p.Prime] in
theorem pointData_descriptor (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup) :
    (pointData ctx hwidth words support hn).descriptor =
      ⟨SubexpTemplateData.bankBytes words, SubexpTemplateData.supportBytes support⟩ := by
  simp only [SubexpMomentSourceProgram.PointData.descriptor,
    SubexpMomentSourceProgram.pointDescriptor, pointData,
    SubexpTemplateData.bankBytes, SubexpTemplateData.supportBytes,
    DensePolynomialLoop.flatten, List.ofFn_eq_map, List.map_map, Function.comp_def]

theorem pointData_canonical_label (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup)
    (i : Fin ctx.dimension) (hi : BinaryArithmetic.toNat (words i).val < p) :
    BinaryArithmetic.toNat ((pointData ctx hwidth words support hn).coordinates i) =
      (SubexpWordLift.sourceValue p (words i)).val := by
  change BinaryArithmetic.toNat (words i).val =
    (BinaryArithmetic.toNat (words i).val : ZMod p).val
  exact (ZMod.val_natCast_of_lt hi).symm

theorem pointData_lift_label (ctx : SourceContext)
    (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
    (words : Fin ctx.dimension → BaseWord p)
    (support : List (Fin ctx.dimension)) (hn : support.Nodup)
    (i : Fin ctx.dimension) (hi : BinaryArithmetic.toNat (words i).val < p)
    (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1))) :
    LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat ((pointData ctx hwidth words support hn).coordinates i) :
        ZMod (p ^ (ctx.dimension + 1))) =
      ((SubexpWordLift.sourceValue p (words i)).val : LiftRing.Extension (QuarticSearch.poly c)) := by
  rw [pointData_canonical_label ctx hwidth words support hn i hi]
  exact map_natCast _ _

def GroupGood {D : ℕ} (ts : List (SubexpTemplateData.Term p D)) : Prop :=
  ∀ t ∈ ts, t.support.Nodup

structure BlockGood {D : ℕ} (b : SubexpTemplateData.Block p D) : Prop where
  outside : b.support.Nodup
  groups : ∀ ts ∈ b.groups, GroupGood ts

section Conversion

variable (ctx : SourceContext)
  (hwidth : ctx.width.length = SubexpLiftRing.baseWidth p 1)
  (templateCtx : TemplateContext)
  (source : SubexpSelectedConversions.Prepared p 0)
  (target : SubexpSelectedConversions.Prepared p ctx.dimension)
  (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (ctx.dimension + 1)))

def termData (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) :
    SubexpMomentSourceProgram.TermData ctx where
  point := pointData ctx hwidth (scalarPoint p source.modulus base t.increment) t.support hn
  factors := SubexpTemplateData.preparedFactors templateCtx source target minusOne base t

@[simp] theorem termData_template (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) :
    (termData ctx hwidth templateCtx source target minusOne base t hn).template =
      SubexpTemplateData.preparedTerm templateCtx source target minusOne base t := by
  unfold SubexpMomentSourceProgram.TermData.template termData
  rw [pointData_descriptor]
  rfl

@[simp] theorem termData_support (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) :
    (termData ctx hwidth templateCtx source target minusOne base t hn).point.support = t.support := rfl

@[simp] theorem termData_coordinates (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) (i : Fin ctx.dimension) :
    (termData ctx hwidth templateCtx source target minusOne base t hn).point.coordinates i =
      (scalarPoint p source.modulus base t.increment i).val := rfl

@[simp] theorem termData_factors (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) :
    (termData ctx hwidth templateCtx source target minusOne base t hn).factors =
      SubexpTemplateData.preparedFactors templateCtx source target minusOne base t := rfl

theorem termData_canonical_label (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) (i : Fin ctx.dimension) :
    BinaryArithmetic.toNat
      ((termData ctx hwidth templateCtx source target minusOne base t hn).point.coordinates i) =
      (SubexpWordLift.sourceValue p (base i) +
        SubexpWordLift.sourceValue p (t.increment i)).val :=
  scalarPoint_label p source.modulus base t.increment i

theorem termData_lift_label (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup) (i : Fin ctx.dimension)
    (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1))) :
    LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat
        ((termData ctx hwidth templateCtx source target minusOne base t hn).point.coordinates i) :
          ZMod (p ^ (ctx.dimension + 1))) =
      ((SubexpWordLift.sourceValue p (base i) + SubexpWordLift.sourceValue p (t.increment i)).val :
        LiftRing.Extension (QuarticSearch.poly c)) := by
  rw [termData_canonical_label]
  exact map_natCast _ _

def groupData (base : Fin ctx.dimension → BaseWord p)
    (ts : List (SubexpTemplateData.Term p ctx.dimension)) (hn : GroupGood ts) :
    List (SubexpMomentSourceProgram.TermData ctx) :=
  ts.attach.map fun t => termData ctx hwidth templateCtx source target minusOne base t.val (hn t.val t.property)

theorem groupData_templates (base : Fin ctx.dimension → BaseWord p)
    (ts : List (SubexpTemplateData.Term p ctx.dimension)) (hn : GroupGood ts) :
    (groupData ctx hwidth templateCtx source target minusOne base ts hn).map
      SubexpMomentSourceProgram.TermData.template =
      ts.map (SubexpTemplateData.preparedTerm templateCtx source target minusOne base) := by
  simp only [groupData, List.map_map, Function.comp_def, termData_template, List.attach_map_val]

theorem groupData_supports (base : Fin ctx.dimension → BaseWord p)
    (ts : List (SubexpTemplateData.Term p ctx.dimension)) (hn : GroupGood ts) :
    (groupData ctx hwidth templateCtx source target minusOne base ts hn).map (fun t => t.point.support) =
      ts.map (fun t => t.support) := by
  simp only [groupData, List.map_map, Function.comp_def, termData_support, List.attach_map_val]

@[simp] theorem groupData_length (base : Fin ctx.dimension → BaseWord p)
    (ts : List (SubexpTemplateData.Term p ctx.dimension)) (hn : GroupGood ts) :
    (groupData ctx hwidth templateCtx source target minusOne base ts hn).length = ts.length := by
  simp [groupData]

def blockData (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b) :
    SubexpMomentSourceProgram.BlockData ctx where
  point := pointData ctx hwidth b.base b.support hn.outside
  groups := b.groups.attach.map fun ts =>
    groupData ctx hwidth templateCtx source target minusOne b.base ts.val (hn.groups ts.val ts.property)

@[simp] theorem blockData_template (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b) :
    (blockData ctx hwidth templateCtx source target minusOne b hn).template =
      SubexpTemplateData.preparedBlock templateCtx source target minusOne b := by
  simp only [SubexpMomentSourceProgram.BlockData.template, blockData, pointData_descriptor,
    List.map_map, Function.comp_def, groupData_templates, List.attach_map_val,
    SubexpTemplateData.preparedBlock]

@[simp] theorem blockData_support (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b) :
    (blockData ctx hwidth templateCtx source target minusOne b hn).point.support = b.support := rfl

@[simp] theorem blockData_coordinates (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b)
    (i : Fin ctx.dimension) :
    (blockData ctx hwidth templateCtx source target minusOne b hn).point.coordinates i = (b.base i).val := rfl

@[simp] theorem blockData_groups_length (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b) :
    (blockData ctx hwidth templateCtx source target minusOne b hn).groups.length = b.groups.length := by
  simp [blockData]

theorem blockData_group_lengths (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b) :
    (blockData ctx hwidth templateCtx source target minusOne b hn).groups.map List.length =
      b.groups.map List.length := by
  simp only [blockData, List.map_map, Function.comp_def, groupData_length, List.attach_map_val]

theorem blockData_lift_label (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b)
    (i : Fin ctx.dimension) (hi : BinaryArithmetic.toNat (b.base i).val < p)
    (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1))) :
    LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat
        ((blockData ctx hwidth templateCtx source target minusOne b hn).point.coordinates i) :
          ZMod (p ^ (ctx.dimension + 1))) =
      ((SubexpWordLift.sourceValue p (b.base i)).val : LiftRing.Extension (QuarticSearch.poly c)) :=
  pointData_lift_label ctx hwidth b.base b.support hn.outside i hi c

def blocksData (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b) : List (SubexpMomentSourceProgram.BlockData ctx) :=
  bs.attach.map fun b => blockData ctx hwidth templateCtx source target minusOne b.val (hn b.val b.property)

theorem blocksData_templates (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b) :
    (blocksData ctx hwidth templateCtx source target minusOne bs hn).map
      SubexpMomentSourceProgram.BlockData.template =
      bs.map (SubexpTemplateData.preparedBlock templateCtx source target minusOne) := by
  simp only [blocksData, List.map_map, Function.comp_def, blockData_template, List.attach_map_val]

theorem blocksData_template_bytes (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b) :
    SubexpMomentSourceProgram.encodeTemplate
      ((blocksData ctx hwidth templateCtx source target minusOne bs hn).map
        SubexpMomentSourceProgram.BlockData.template) =
      SubexpMomentSourceProgram.encodeTemplate
        (bs.map (SubexpTemplateData.preparedBlock templateCtx source target minusOne)) := by
  rw [blocksData_templates]

@[simp] theorem blocksData_length (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b) :
    (blocksData ctx hwidth templateCtx source target minusOne bs hn).length = bs.length := by
  simp [blocksData]

end Conversion

end SubexponentialSAT.SubexpTemplateSourceData

end OAI.Algorithms
