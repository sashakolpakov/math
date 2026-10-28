import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceData
import OAI.Algorithms.SubexponentialSAT.SubexpProducedSourceRefinement

namespace OAI.Algorithms

/-!
# Local provenance for the actual prepared template

The point words and their supports come from the template's actual output.
Only individual factor witnesses remain in the hypotheses; the weight and
nested block relations are derived here in the preserved list order.
-/

namespace SubexponentialSAT.SubexpTemplateSourceProvenance

noncomputable section

open SubexpTemplateSourceData SubexpProducedSourceRefinement
open SubexpMomentSourceSemantics SubexpTemplatePointServices
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing

variable {p : ℕ} [Fact p.Prime] {ctx : SourceContext}
  (hwidth : ctx.width.length = baseWidth p 1)
  (templateCtx : TemplateContext)
  (source : SubexpSelectedConversions.Prepared p 0)
  (target : SubexpSelectedConversions.Prepared p ctx.dimension)
  (minusOne : Word (baseWidth p (ctx.dimension + 1)))
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [One (QuarticCode p ctx.dimension)]

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "RefFactor" => SubexpBlockAssemblySemantics.Factor R
  (SymbolicCost.CoeffList ctx.dimension R)
local notation "RefTerm" => SubexpBlockAssemblySemantics.Term R
  (SymbolicCost.CoeffList ctx.dimension R)
local notation "RefBlock" => SubexpBlockAssemblySemantics.Block R
  (SymbolicCost.CoeffList ctx.dimension R)

def referenceTerm (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (factors : List RefFactor)
    (a : Fin ctx.dimension → ℕ) : RefTerm :=
  ⟨(SubexpWeightCode.rawWeightWithCost
      (fun i => ((SubexpWordLift.sourceValue p (base i) +
        SubexpWordLift.sourceValue p (t.increment i)).val : R)) a t.support).1,
    factors⟩

def referenceBlock
    (referenceFactors : (Fin ctx.dimension → BaseWord p) →
      SubexpTemplateData.Term p ctx.dimension → List RefFactor)
    (b : SubexpTemplateData.Block p ctx.dimension) (a : Fin ctx.dimension → ℕ) : RefBlock :=
  ⟨(SubexpWeightCode.rawWeightWithCost
      (fun i => ((SubexpWordLift.sourceValue p (b.base i)).val : R)) a b.support).1,
    b.groups.map fun ts => ts.map fun t =>
      referenceTerm c b.base t (referenceFactors b.base t) a⟩

/-- This is the local factor packet boundary supplied by the checked
beta/Taylor/literal and interpolation-cache proofs. -/
def FactorWitness (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (refs : List RefFactor) : Prop :=
  ∃ actual : List (SubexpBlockAssemblySemantics.Factor
      (QuarticCode p ctx.dimension) (Raw p ctx.dimension)),
    actual.map (SubexpBlockAssemblySemantics.Factor.prepared
      (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
      (SubexpWeightCode.rawScalar ctx.dimension)) =
        SubexpTemplateData.preparedFactors templateCtx source target minusOne base t ∧
    List.Forall₂ (SubexpSourceReference.FactorRel (coefficientValue p ctx.dimension c))
      actual refs

theorem term_provenance (base : Fin ctx.dimension → BaseWord p)
    (t : SubexpTemplateData.Term p ctx.dimension) (hn : t.support.Nodup)
    (refs : List RefFactor)
    (hf : FactorWitness templateCtx source target minusOne c base t refs)
    (a : Fin ctx.dimension → ℕ) :
    TermProvenance c a
      (termData ctx hwidth templateCtx source target minusOne base t hn)
      (referenceTerm c base t refs a) := by
  constructor
  · exact pointWeight_refines c a
      (termData ctx hwidth templateCtx source target minusOne base t hn).point
      (fun i => ((SubexpWordLift.sourceValue p (base i) +
        SubexpWordLift.sourceValue p (t.increment i)).val : R)) t.support hn rfl
      (fun i _ => termData_lift_label ctx hwidth templateCtx source target minusOne
        base t hn i c)
  · exact hf

private theorem map_related {A B C : Type*} (xs : List A)
    (f : A → B) (g : A → C) (rel : B → C → Prop)
    (h : ∀ x, rel (f x) (g x)) : List.Forall₂ rel (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x) ih

private theorem attach_related {A B C : Type*} (xs : List A)
    (f : {x // x ∈ xs} → B) (g : A → C) (rel : B → C → Prop)
    (h : ∀ x, rel (f x) (g x.val)) :
    List.Forall₂ rel (xs.attach.map f) (xs.map g) := by
  have he := map_related xs.attach f (fun x => g x.val) rel h
  simpa only [List.attach_map_val] using he

theorem group_provenance (base : Fin ctx.dimension → BaseWord p)
    (ts : List (SubexpTemplateData.Term p ctx.dimension)) (hn : GroupGood ts)
    (referenceFactors : SubexpTemplateData.Term p ctx.dimension → List RefFactor)
    (hf : ∀ t ∈ ts,
      FactorWitness templateCtx source target minusOne c base t (referenceFactors t))
    (a : Fin ctx.dimension → ℕ) :
    List.Forall₂ (TermProvenance c a)
      (groupData ctx hwidth templateCtx source target minusOne base ts hn)
      (ts.map fun t => referenceTerm c base t (referenceFactors t) a) := by
  apply attach_related
  intro t
  exact term_provenance hwidth templateCtx source target minusOne c base t.val
    (hn t.val t.property) (referenceFactors t.val) (hf t.val t.property) a

theorem block_provenance
    (referenceFactors : (Fin ctx.dimension → BaseWord p) →
      SubexpTemplateData.Term p ctx.dimension → List RefFactor)
    (b : SubexpTemplateData.Block p ctx.dimension) (hn : BlockGood b)
    (hbase : ∀ i, BinaryArithmetic.toNat (b.base i).val < p)
    (hf : ∀ ts ∈ b.groups, ∀ t ∈ ts,
      FactorWitness templateCtx source target minusOne c b.base t (referenceFactors b.base t))
    (a : Fin ctx.dimension → ℕ) :
    BlockProvenance c a
      (blockData ctx hwidth templateCtx source target minusOne b hn)
      (referenceBlock c referenceFactors b a) := by
  constructor
  · exact pointWeight_refines c a
      (blockData ctx hwidth templateCtx source target minusOne b hn).point
      (fun i => ((SubexpWordLift.sourceValue p (b.base i)).val : R)) b.support hn.outside rfl
      (fun i _ => blockData_lift_label ctx hwidth templateCtx source target minusOne
        b hn i (hbase i) c)
  · apply attach_related
    intro ts
    exact group_provenance hwidth templateCtx source target minusOne c b.base ts.val
      (hn.groups ts.val ts.property) (referenceFactors b.base) (hf ts.val ts.property) a

/-- The full nested provenance relation follows from canonical point words,
preserved supports, and the individual factor packet witnesses. -/
theorem blocks_provenance
    (referenceFactors : (Fin ctx.dimension → BaseWord p) →
      SubexpTemplateData.Term p ctx.dimension → List RefFactor)
    (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b)
    (hbase : ∀ b ∈ bs, ∀ i, BinaryArithmetic.toNat (b.base i).val < p)
    (hf : ∀ b ∈ bs, ∀ ts ∈ b.groups, ∀ t ∈ ts,
      FactorWitness templateCtx source target minusOne c b.base t (referenceFactors b.base t))
    (a : Fin ctx.dimension → ℕ) :
    List.Forall₂ (BlockProvenance c a)
      (blocksData ctx hwidth templateCtx source target minusOne bs hn)
      (bs.map fun b => referenceBlock c referenceFactors b a) := by
  apply attach_related
  intro b
  exact block_provenance hwidth templateCtx source target minusOne c referenceFactors b.val
    (hn b.val b.property) (hbase b.val b.property) (hf b.val b.property) a

end

end SubexponentialSAT.SubexpTemplateSourceProvenance

end OAI.Algorithms
