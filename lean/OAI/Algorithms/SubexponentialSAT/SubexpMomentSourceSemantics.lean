import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceComplete
import OAI.Algorithms.SubexponentialSAT.SubexpWeightLiteralSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpMomentStep
import OAI.Algorithms.SubexponentialSAT.SubexpSourceFactors

namespace OAI.Algorithms

/-!
# Typed meaning of the actual current-exponent source output

The weight words come from the executed weight program. The only typing
witnesses added to its output concern the individual prepared factor rows.
These local witnesses determine the exact source bytes and its polynomial
meaning, including literals emitted in a different term order.
-/

namespace SubexponentialSAT.SubexpMomentSourceSemantics

open SubexpMomentSourceProgram
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing
open SubexpSourceSemantics

abbrev Raw (p D : ℕ) := SymbolicCost.CoeffList D (QuarticCode p D)

noncomputable def coefficientValue (p D : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p ^ (D + 1))) (x : QuarticCode p D) :
    LiftRing.Extension (QuarticSearch.poly c) :=
  quotientDenote c (x.map (wordValue p (D + 1)))

private theorem serialized_raw (p D : ℕ) [Fact p.Prime] (raw : Raw p D) :
    Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode) raw =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D raw := by
  rw [← SubexpMomentStep.encodedRecords_bytes]
  induction raw with
  | nil => rfl
  | cons term rest ih =>
      change true :: (Encoding.frame
        (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode term) ++
          Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode) rest) = _
      rw [ih]
      rfl

section Weights

variable {p : ℕ} [Fact p.Prime] {ctx : Context}
  (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))

def weightRaw {a : Fin ctx.dimension → ℕ} {point : PointData ctx}
    (w : WeightResult ctx a point) : Raw p ctx.dimension :=
  SubexpWeightLiteralSemantics.constantRaw ctx.dimension p (ctx.dimension + 1)
    w.output (w.length.trans htarget)

theorem weightRaw_bytes {a : Fin ctx.dimension → ℕ} {point : PointData ctx}
    (w : WeightResult ctx a point) :
    SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension
      (weightRaw htarget w) = w.literal := by
  rw [← serialized_raw]
  exact (SubexpWeightLiteralSemantics.serialized_constantRaw ctx.dimension p
    (ctx.dimension + 1) w.output ctx.target (w.length.trans htarget) htarget).symm

noncomputable def pointWeight
    (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
    (a : Fin ctx.dimension → ℕ) (point : PointData ctx) :
    LiftRing.Extension (QuarticSearch.poly c) :=
  Separation.coordinateWeight point.support.toFinset
    (fun word => LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat word : ZMod (p ^ (ctx.dimension + 1))))
    a point.coordinates

/-- The physical word's local residue theorem determines its lifted
coordinate weight. A canonical byte representation is unnecessary here. -/
theorem weightRaw_denote
    (hmodulus : BinaryArithmetic.toNat ctx.modulus = p ^ (ctx.dimension + 1))
    (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
    {a : Fin ctx.dimension → ℕ} {point : PointData ctx}
    (w : WeightResult ctx a point) :
    SymbolicCost.denote
      (decodeRaw (coefficientValue p ctx.dimension c) (weightRaw htarget w)) =
      WeightedSupport.scalarHom (pointWeight c a point) := by
  have hv : (BinaryArithmetic.toNat w.output : ZMod (p ^ (ctx.dimension + 1))) =
      Separation.coordinateWeight point.support.toFinset id a
        (fun i => (BinaryArithmetic.toNat (point.coordinates i) :
          ZMod (p ^ (ctx.dimension + 1)))) := by
    let claim (modulus : ℕ) : Prop :=
      (BinaryArithmetic.toNat w.output : ZMod modulus) =
        Separation.coordinateWeight point.support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (point.coordinates i) : ZMod modulus))
    exact Eq.mp (congrArg claim hmodulus) w.value
  change SymbolicCost.denote ((SubexpWeightLiteralSemantics.constantRaw
    ctx.dimension p (ctx.dimension + 1) w.output (w.length.trans htarget)).map
      (fun term => (term.1,quotientDenote c (term.2.map (wordValue p (ctx.dimension + 1)))))) = _
  rw [SubexpWeightLiteralSemantics.denote_weightRaw _ _ _ _ _ _ _ hv]
  simp only [pointWeight, Separation.coordinateWeight, Function.id_def, map_prod, map_pow]

end Weights

section TypedOutput

variable (p : ℕ) [Fact p.Prime] (ctx : Context) (a : Fin ctx.dimension → ℕ)

/-- A typing witness for one actual term adds only the provenance of its
individual factor packets. The executed weight word remains unchanged. -/
structure TypedTerm where
  result : TermResult ctx a
  factors : List (SubexpBlockAssemblySemantics.Factor
    (QuarticCode p ctx.dimension) (Raw p ctx.dimension))
  rows : factors.map (SubexpBlockAssemblySemantics.Factor.prepared
    (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
    (SubexpWeightCode.rawScalar ctx.dimension)) = result.input.factors

structure TypedBlock where
  result : BlockResult ctx a
  groups : List (List (TypedTerm p ctx a))
  terms : groups.map (List.map TypedTerm.result) = result.groups

variable {p ctx a}

def FactorsTyped (t : TermResult ctx a) : Prop :=
  ∃ fs : List (SubexpBlockAssemblySemantics.Factor
      (QuarticCode p ctx.dimension) (Raw p ctx.dimension)),
    fs.map (SubexpBlockAssemblySemantics.Factor.prepared
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension)) = t.input.factors

private theorem map_lift_exists {A B : Type*} (f : B → A) (xs : List A)
    (h : ∀ x ∈ xs, ∃ y, f y = x) : ∃ ys : List B, ys.map f = xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
      obtain ⟨y,hy⟩ := h x (by simp)
      obtain ⟨ys,hys⟩ := ih (fun z hz => h z (by simp [hz]))
      exact ⟨y::ys,by simp only [List.map_cons,hy,hys]⟩

omit [Fact p.Prime] in
/-- A packet-level factor typing theorem suffices to type every actual
source output. The weight words and the output order are preserved. -/
theorem typing_exists (outs : List (BlockResult ctx a))
    (h : ∀ b ∈ outs, ∀ group ∈ b.groups, ∀ t ∈ group, FactorsTyped (p := p) t) :
    ∃ bs : List (TypedBlock p ctx a), bs.map TypedBlock.result = outs := by
  apply map_lift_exists
  intro b hb
  have hg : ∀ group ∈ b.groups,
      ∃ ts : List (TypedTerm p ctx a), ts.map TypedTerm.result = group := by
    intro group hgroup
    apply map_lift_exists
    intro t ht
    obtain ⟨fs,hfs⟩ := h b hb group hgroup t ht
    exact ⟨⟨t,fs,hfs⟩,rfl⟩
  obtain ⟨groups,hgroups⟩ := map_lift_exists (List.map TypedTerm.result) b.groups hg
  exact ⟨⟨b,groups,hgroups⟩,rfl⟩

variable
  (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))

def TypedTerm.syntax (t : TypedTerm p ctx a) :
    SubexpBlockAssemblySemantics.Term (QuarticCode p ctx.dimension) (Raw p ctx.dimension) :=
  ⟨weightRaw htarget t.result.weight,t.factors⟩

def TypedBlock.syntax (b : TypedBlock p ctx a) :
    SubexpBlockAssemblySemantics.Block (QuarticCode p ctx.dimension) (Raw p ctx.dimension) :=
  ⟨weightRaw htarget b.result.weight,b.groups.map (List.map (TypedTerm.syntax htarget))⟩

theorem TypedTerm.prepared (t : TypedTerm p ctx a) :
    (t.syntax htarget).prepared
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension) = t.result.prepared := by
  change SubexpBlockAssembly.Term.mk
    (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension
      (weightRaw htarget t.result.weight))
    (t.factors.map (SubexpBlockAssemblySemantics.Factor.prepared
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension))) = _
  rw [weightRaw_bytes, t.rows]
  rfl

theorem TypedBlock.prepared (b : TypedBlock p ctx a) :
    (b.syntax htarget).prepared
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension) = b.result.prepared := by
  have hg := congrArg
    (fun groups : List (List (TermResult ctx a)) =>
      groups.map (List.map TermResult.prepared)) b.terms
  simp only [List.map_map, Function.comp_def] at hg
  simp only [TypedBlock.syntax, SubexpBlockAssemblySemantics.Block.prepared,
    List.map_map, Function.comp_def, TypedTerm.prepared, weightRaw_bytes]
  rw [hg]
  rfl

variable [Zero (Raw p ctx.dimension)] [One (Raw p ctx.dimension)]

def blocks (bs : List (TypedBlock p ctx a)) :
    List (SubexpAlgorithm.Block (Raw p ctx.dimension)) :=
  bs.map fun b => (b.syntax htarget).expression (SubexpWeightCode.rawScalar ctx.dimension)

def expression (bs : List (TypedBlock p ctx a)) : Algorithm.Expr (Raw p ctx.dimension) :=
  SubexpAlgorithm.momentExpression (blocks htarget bs)

/-- Exact source identity reconstructed from local prepared rows and the
weight words that the machine actually produced. -/
theorem source_bytes
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    (bs : List (TypedBlock p ctx a)) :
    SubexpMomentSourceProgram.source ctx (bs.map TypedBlock.result) =
      SubexpPostfixControl.serializeCode
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
        (expression htarget bs).compile := by
  have hp : ((bs.map (TypedBlock.syntax htarget)).map
      (SubexpBlockAssemblySemantics.Block.prepared
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
        (SubexpWeightCode.rawScalar ctx.dimension))) =
      preparedBlocks (bs.map TypedBlock.result) := by
    simp only [List.map_map, Function.comp_def, TypedBlock.prepared, preparedBlocks]
  unfold SubexpMomentSourceProgram.source
  rw [hzero, hone, ← hp]
  simpa only [expression, blocks, List.map_map, Function.comp_def] using
    SubexpBlockAssemblySemantics.source_eq
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension) (bs.map (TypedBlock.syntax htarget))

end TypedOutput

end SubexponentialSAT.SubexpMomentSourceSemantics

end OAI.Algorithms
