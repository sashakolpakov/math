import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceFamily

namespace OAI.Algorithms

/-! The physical raw template and the separated reference builder visit the
same bases, colors, increments, and factor occurrences. The proof keeps the
original indices, even when two encoded packet payloads are equal. -/

namespace SubexponentialSAT.SubexpOrderedSourceProvenance

noncomputable section

open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpProducedSourceRefinement SubexpTemplateSourceProvenance
open SubexpTemplateSourceData SubexpTemplatePointServices
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost
open MulticolorTypes Subexp.ConstructivePacking

variable {p r Q Δ q : ℕ} [Fact p.Prime] {ctx : Context}
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [One (QuarticCode p ctx.dimension)]
  (hwidth : ctx.width.length = baseWidth p 1)
  (templateCtx : TemplateContext)
  (source : SubexpSelectedConversions.Prepared p 0)
  (target : SubexpSelectedConversions.Prepared p ctx.dimension)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (ctx.dimension + 1)))
  (packing : PackingData (Fin ctx.dimension) (UniversalType r Q Δ))
  (node : Fin Q)
  {F K : Type*} [Zero K] [Add K] [Mul K]
  (es : List F) (words : F → MulticolorTypes.Word r Q)
  (packets : F → SubexpTemplateFactors.Factor p ctx.dimension)
  (embed : ZMod p → K)

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "RefFactor" => SubexpBlockAssemblySemantics.Factor R
  (SymbolicCost.CoeffList ctx.dimension R)

variable (lift : K → LiftRing.Extension (QuarticSearch.poly c))
  (cache : List (List (LiftRing.Extension (QuarticSearch.poly c))))
  (fs : List (SubexpProgramBuilder.FactorData ctx.dimension p q r K
    (LiftRing.Extension (QuarticSearch.poly c))))

def referenceFactors (g : Fin r) (base increment : Fin ctx.dimension → ZMod p) :
    List RefFactor :=
  (fs.filter (fun f => decide (f.color = g))).map fun f =>
    SubexpSourceReference.factor (D := ctx.dimension) (p := p) (q := q) (r := r)
      (K := K) («R» := R) lift cache f
      (fun i => embed (base i + increment i))

def FactorWitnesses (bases : List (Fin ctx.dimension → ZMod p))
    (increments : Fin r → List (Fin ctx.dimension → ZMod p)) : Prop :=
  ∀ base ∈ bases, ∀ g, ∀ increment ∈ increments g,
    FactorWitness templateCtx source target minusOne c (Subexp.RawTemplateRefinement.scalarWords base)
      (Subexp.RawTemplateRefinement.term packing node es words packets g increment)
      (referenceFactors c embed lift cache fs g base increment)

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
  have hx := map_related xs.attach f (fun x => g x.val) rel h
  simpa only [List.attach_map_val] using hx

private theorem attach_ofFn_related {A B C : Type*} {n : ℕ}
    (items : Fin n → A) (f : {x // x ∈ List.ofFn items} → B)
    (g : Fin n → C) (rel : B → C → Prop)
    (h : ∀ i, rel (f ⟨items i, List.mem_ofFn.mpr ⟨i, rfl⟩⟩) (g i)) :
    List.Forall₂ rel ((List.ofFn items).attach.map f) (List.ofFn g) := by
  apply List.forall₂_of_length_eq_of_get
  · simp only [List.length_map, List.length_attach, List.length_ofFn]
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_ofFn] using hj
    simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_attach,
      List.getElem_ofFn] using h ⟨i, hin⟩

theorem term_provenance (g : Fin r) (base increment : Fin ctx.dimension → ZMod p)
    (hn : (Subexp.RawTemplateRefinement.term packing node es words packets g increment).support.Nodup)
    (hf : FactorWitness templateCtx source target minusOne c (Subexp.RawTemplateRefinement.scalarWords base)
      (Subexp.RawTemplateRefinement.term packing node es words packets g increment)
      (referenceFactors c embed lift cache fs g base increment))
    (a : Fin ctx.dimension → ℕ) :
    TermProvenance c a
      (termData ctx hwidth templateCtx source target minusOne (Subexp.RawTemplateRefinement.scalarWords base)
        (Subexp.RawTemplateRefinement.term packing node es words packets g increment) hn)
      (SubexpSourceReference.term (D := ctx.dimension) (p := p) (q := q) (r := r)
        (F := ZMod p) (K := K) («R» := R) embed lift (fun z : ZMod p => (z.val : R)) cache fs
        (Subexp.RawTemplateRefinement.colorSupport packing node g) g (SubexpProgramBuilder.shifted base increment) a) := by
  have h := SubexpTemplateSourceProvenance.term_provenance hwidth templateCtx source target
    minusOne c (Subexp.RawTemplateRefinement.scalarWords base) (Subexp.RawTemplateRefinement.term packing node es words packets g increment)
    hn (referenceFactors c embed lift cache fs g base increment) hf a
  simpa only [SubexpTemplateSourceProvenance.referenceTerm, Subexp.RawTemplateRefinement.term, Subexp.RawTemplateRefinement.scalarWords_value,
    SubexpSourceReference.term, SubexpProgramBuilder.shifted, referenceFactors] using h

theorem group_provenance (g : Fin r) (base : Fin ctx.dimension → ZMod p)
    (increments : List (Fin ctx.dimension → ZMod p))
    (hn : GroupGood (Subexp.RawTemplateRefinement.group packing node es words packets g increments))
    (hf : ∀ increment ∈ increments,
      FactorWitness templateCtx source target minusOne c (Subexp.RawTemplateRefinement.scalarWords base)
        (Subexp.RawTemplateRefinement.term packing node es words packets g increment)
        (referenceFactors c embed lift cache fs g base increment))
    (a : Fin ctx.dimension → ℕ) :
    List.Forall₂ (TermProvenance c a)
      (groupData ctx hwidth templateCtx source target minusOne (Subexp.RawTemplateRefinement.scalarWords base)
        (Subexp.RawTemplateRefinement.group packing node es words packets g increments) hn)
      (increments.map fun increment =>
        SubexpSourceReference.term (D := ctx.dimension) (p := p) (q := q) (r := r)
        (F := ZMod p) (K := K) («R» := R) embed lift (fun z : ZMod p => (z.val : R)) cache fs
          (Subexp.RawTemplateRefinement.colorSupport packing node g) g (SubexpProgramBuilder.shifted base increment) a) := by
  simp only [groupData, Subexp.RawTemplateRefinement.group, List.attach_map, List.map_map, Function.comp_def]
  apply attach_related
  intro increment
  exact term_provenance c hwidth templateCtx source target minusOne packing node es words packets
    embed lift cache fs g base increment.val _ (hf increment.val increment.property) a

theorem block_provenance (base : Fin ctx.dimension → ZMod p)
    (increments : Fin r → List (Fin ctx.dimension → ZMod p))
    (hn : BlockGood (Subexp.RawTemplateRefinement.block packing node es words packets increments base))
    (hf : ∀ g, ∀ increment ∈ increments g,
      FactorWitness templateCtx source target minusOne c (Subexp.RawTemplateRefinement.scalarWords base)
        (Subexp.RawTemplateRefinement.term packing node es words packets g increment)
        (referenceFactors c embed lift cache fs g base increment))
    (a : Fin ctx.dimension → ℕ) :
    BlockProvenance c a
      (blockData ctx hwidth templateCtx source target minusOne
        (Subexp.RawTemplateRefinement.block packing node es words packets increments base) hn)
      (SubexpSourceReference.block (D := ctx.dimension) (p := p) (q := q) (r := r)
        (F := ZMod p) (K := K) («R» := R) embed lift (fun z : ZMod p => (z.val : R)) cache fs
        (Subexp.RawTemplateRefinement.colorSupport packing node) (Subexp.RawTemplateRefinement.outsideSupport packing) base increments a) := by
  constructor
  · have h := pointWeight_refines c a
      (blockData ctx hwidth templateCtx source target minusOne
        (Subexp.RawTemplateRefinement.block packing node es words packets increments base) hn).point
      (fun i => ((base i).val : R)) (Subexp.RawTemplateRefinement.outsideSupport packing) hn.outside rfl
      (fun i _ => by
        simpa only [Subexp.RawTemplateRefinement.block, Subexp.RawTemplateRefinement.scalarWords_value] using
          blockData_lift_label ctx hwidth templateCtx source target minusOne
            (Subexp.RawTemplateRefinement.block packing node es words packets increments base) hn i
            (Subexp.RawTemplateRefinement.scalarWords_canonical base i) c)
    exact h
  · change List.Forall₂ (List.Forall₂ (TermProvenance c a))
      ((List.ofFn (fun g => Subexp.RawTemplateRefinement.group packing node es words packets g (increments g))).attach.map _)
      (List.ofFn fun g => (increments g).map fun increment =>
        SubexpSourceReference.term (D := ctx.dimension) (p := p) (q := q) (r := r)
        (F := ZMod p) (K := K) («R» := R) embed lift (fun z : ZMod p => (z.val : R)) cache fs
          (Subexp.RawTemplateRefinement.colorSupport packing node g) g (SubexpProgramBuilder.shifted base increment) a)
    apply attach_ofFn_related
    intro g
    exact group_provenance c hwidth templateCtx source target minusOne packing node es words packets
      embed lift cache fs g base (increments g) _ (hf g) a

/-- Exact ordered reference blocks, with no reordering or quotient of
duplicate packets. The factor witnesses are local to their original visit. -/
theorem blocks_provenance (bases : List (Fin ctx.dimension → ZMod p))
    (increments : Fin r → List (Fin ctx.dimension → ZMod p))
    (hf : FactorWitnesses c templateCtx source target minusOne packing node es words packets
      embed lift cache fs bases increments)
    (a : Fin ctx.dimension → ℕ) :
    List.Forall₂ (BlockProvenance c a)
      (blocksData ctx hwidth templateCtx source target minusOne
        (Subexp.RawTemplateRefinement.blocks packing node es words packets bases increments)
        (Subexp.RawTemplateRefinement.blocks_good packing node es words packets bases increments))
      (SubexpSourceReference.blocks (D := ctx.dimension) (p := p) (q := q) (r := r)
        (F := ZMod p) (K := K) («R» := R) embed lift (fun z : ZMod p => (z.val : R)) cache fs
        (Subexp.RawTemplateRefinement.colorSupport packing node) (Subexp.RawTemplateRefinement.outsideSupport packing) bases increments a) := by
  simp only [blocksData, Subexp.RawTemplateRefinement.blocks, List.attach_map, List.map_map,
    Function.comp_def, SubexpSourceReference.blocks]
  apply attach_related
  intro base
  exact block_provenance c hwidth templateCtx source target minusOne packing node es words packets
    embed lift cache fs base.val increments _ (hf base.val base.property) a

end

end SubexponentialSAT.SubexpOrderedSourceProvenance

end OAI.Algorithms
