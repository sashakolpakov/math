import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpSourceReference

namespace OAI.Algorithms

/-!
# Local refinement facts for the physically produced source

The executed weight word is identified from its coordinate labels. A factor
is identified from its own table, interpolation cache, and emitted arguments.
The nested list relation retains the actual incidence and enumeration order.
-/

namespace SubexponentialSAT.SubexpProducedSourceRefinement

noncomputable section

open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing
open SubexpSourceSemantics

variable {p : ℕ} [Fact p.Prime] {ctx : Context}
  (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))
  (hmodulus : BinaryArithmetic.toNat ctx.modulus = p ^ (ctx.dimension + 1))
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "decode" => coefficientValue p ctx.dimension c

omit [Fact p.Prime] in
/-- The reusable point-bank and support data determine a reference weight
before the weight program has run. -/
theorem pointWeight_refines (a : Fin ctx.dimension → ℕ) (point : PointData ctx)
    (x : Fin ctx.dimension → R) (support : List (Fin ctx.dimension))
    (hn : support.Nodup) (hs : point.support.toFinset = support.toFinset)
    (hx : ∀ i ∈ support, LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat (point.coordinates i) : ZMod (p ^ (ctx.dimension + 1))) = x i) :
    WeightedSupport.scalarHom (pointWeight c a point) =
      SymbolicCost.denote (SubexpWeightCode.rawWeightWithCost x a support).1 := by
  rw [SubexpWeightCode.rawWeightWithCost_coordinateWeight x a support hn]
  apply congrArg WeightedSupport.scalarHom
  unfold pointWeight Separation.coordinateWeight
  rw [hs]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun value : R => value ^ a i) (hx i (List.mem_toFinset.mp hi))

include hmodulus in
/-- Canonical coordinate bytes and the support list determine the reference
weight. This discharges the weight premise without assuming its output word. -/
theorem weight_refines {a : Fin ctx.dimension → ℕ} {point : PointData ctx}
    (w : WeightResult ctx a point)
    (x : Fin ctx.dimension → R) (support : List (Fin ctx.dimension))
    (hn : support.Nodup) (hs : point.support.toFinset = support.toFinset)
    (hx : ∀ i ∈ support, LiftRing.of (QuarticSearch.poly c)
      (BinaryArithmetic.toNat (point.coordinates i) : ZMod (p ^ (ctx.dimension + 1))) = x i) :
    SymbolicCost.denote (decodeRaw decode (weightRaw htarget w)) =
      SymbolicCost.denote (SubexpWeightCode.rawWeightWithCost x a support).1 :=
  (weightRaw_denote htarget hmodulus c w).trans (pointWeight_refines c a point x support hn hs hx)

section Lists

variable [One (QuarticCode p ctx.dimension)]

local instance : Zero (Raw p ctx.dimension) := ⟨[]⟩
local instance : One (Raw p ctx.dimension) := ⟨SubexpAlgorithm.rawOne ctx.dimension⟩
local instance : Zero (SymbolicCost.CoeffList ctx.dimension R) := ⟨[]⟩
local instance : One (SymbolicCost.CoeffList ctx.dimension R) := ⟨SubexpAlgorithm.rawOne ctx.dimension⟩

def TermAgreement {a : Fin ctx.dimension → ℕ}
    (actual : TypedTerm p ctx a)
    (reference : SubexpBlockAssemblySemantics.Term R (SymbolicCost.CoeffList ctx.dimension R)) : Prop :=
  WeightedSupport.scalarHom (pointWeight c a actual.result.input.point) =
      SymbolicCost.denote reference.weight ∧
    List.Forall₂ (SubexpSourceReference.FactorRel decode) actual.factors reference.factors

def BlockAgreement {a : Fin ctx.dimension → ℕ}
    (actual : TypedBlock p ctx a)
    (reference : SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)) : Prop :=
  WeightedSupport.scalarHom (pointWeight c a actual.result.input.point) =
      SymbolicCost.denote reference.outside ∧
    List.Forall₂ (List.Forall₂ (TermAgreement c)) actual.groups reference.groups

/-- Provenance belongs to the reusable input packets. It describes each
selected factor and the coordinate labels, not the later computed weights. -/
def TermProvenance (a : Fin ctx.dimension → ℕ) (input : TermData ctx)
    (reference : SubexpBlockAssemblySemantics.Term R (SymbolicCost.CoeffList ctx.dimension R)) : Prop :=
  WeightedSupport.scalarHom (pointWeight c a input.point) =
      SymbolicCost.denote reference.weight ∧
    ∃ fs : List (SubexpBlockAssemblySemantics.Factor
        (QuarticCode p ctx.dimension) (Raw p ctx.dimension)),
      fs.map (SubexpBlockAssemblySemantics.Factor.prepared
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
        (SubexpWeightCode.rawScalar ctx.dimension)) = input.factors ∧
      List.Forall₂ (SubexpSourceReference.FactorRel decode) fs reference.factors

def BlockProvenance (a : Fin ctx.dimension → ℕ) (input : BlockData ctx)
    (reference : SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)) : Prop :=
  WeightedSupport.scalarHom (pointWeight c a input.point) =
      SymbolicCost.denote reference.outside ∧
    List.Forall₂ (List.Forall₂ (TermProvenance c a)) input.groups reference.groups

private theorem refine_aligned {A B C E : Type*}
    {r : A → B → Prop} {s : A → C → Prop} {t : E → C → Prop}
    (f : E → B)
    (lift : ∀ a b c, r a b → s a c → ∃ e, f e = b ∧ t e c)
    {xs : List A} {ys : List B} {zs : List C}
    (hxy : List.Forall₂ r xs ys) (hxz : List.Forall₂ s xs zs) :
    ∃ es : List E, es.map f = ys ∧ List.Forall₂ t es zs := by
  induction hxy generalizing zs with
  | nil =>
      cases hxz
      exact ⟨[],rfl,.nil⟩
  | @cons x y xs ys hxy hrest ih =>
      cases hxz with
      | @cons _ z _ zs hxz hzs =>
          obtain ⟨e,he,ht⟩ := lift x y z hxy hxz
          obtain ⟨es,hes,hts⟩ := ih hzs
          exact ⟨e::es,by simp only [List.map_cons,he,hes],.cons ht hts⟩

theorem term_result_refinement {a : Fin ctx.dimension → ℕ}
    (input : TermData ctx) (output : TermResult ctx a)
    (reference : SubexpBlockAssemblySemantics.Term R (SymbolicCost.CoeffList ctx.dimension R))
    (hi : output.input = input) (hp : TermProvenance c a input reference) :
    ∃ t : TypedTerm p ctx a, t.result = output ∧ TermAgreement c t reference := by
  obtain ⟨fs,hfs,hf⟩ := hp.2
  let t : TypedTerm p ctx a := ⟨output,fs,by simpa only [hi] using hfs⟩
  refine ⟨t,rfl,?_,hf⟩
  simpa only [t,hi] using hp.1

theorem block_result_refinement {a : Fin ctx.dimension → ℕ}
    (input : BlockData ctx) (output : BlockResult ctx a)
    (reference : SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R))
    (hi : output.input = input) (hp : BlockProvenance c a input reference) :
    ∃ b : TypedBlock p ctx a, b.result = output ∧ BlockAgreement c b reference := by
  have ha : List.Forall₂ (List.Forall₂ (fun t out => out.input = t))
      input.groups output.groups := by simpa only [hi] using output.agreement
  have liftGroup (ts : List (TermData ctx)) (outs : List (TermResult ctx a))
      (refs : List (SubexpBlockAssemblySemantics.Term R
        (SymbolicCost.CoeffList ctx.dimension R)))
      (ha : List.Forall₂ (fun t out => out.input = t) ts outs)
      (hr : List.Forall₂ (TermProvenance c a) ts refs) :
      ∃ typed : List (TypedTerm p ctx a),
        typed.map TypedTerm.result = outs ∧
          List.Forall₂ (TermAgreement c) typed refs :=
    refine_aligned TypedTerm.result (term_result_refinement c) ha hr
  obtain ⟨groups,hgroups,hg⟩ := refine_aligned
    (r := List.Forall₂ (fun t out => out.input = t))
    (s := List.Forall₂ (TermProvenance c a))
    (t := List.Forall₂ (TermAgreement c))
    (List.map TypedTerm.result) liftGroup ha hp.2
  let b : TypedBlock p ctx a := ⟨output,groups,hgroups⟩
  refine ⟨b,rfl,?_,hg⟩
  simpa only [b,hi] using hp.1

/-- The actual producer's input/output agreement transports packet-local
provenance to its computed output, preserving all bytes and list order. -/
theorem refine_outputs {a : Fin ctx.dimension → ℕ}
    {inputs : List (BlockData ctx)} {outputs : List (BlockResult ctx a)}
    {reference : List (SubexpBlockAssemblySemantics.Block R
      (SymbolicCost.CoeffList ctx.dimension R))}
    (ha : List.Forall₂ (fun input output => output.input = input) inputs outputs)
    (hp : List.Forall₂ (BlockProvenance c a) inputs reference) :
    ∃ bs : List (TypedBlock p ctx a), bs.map TypedBlock.result = outputs ∧
      List.Forall₂ (BlockAgreement c) bs reference :=
  refine_aligned TypedBlock.result (block_result_refinement c) ha hp

include hmodulus in
theorem term_refines {a : Fin ctx.dimension → ℕ}
    {actual : TypedTerm p ctx a}
    {reference : SubexpBlockAssemblySemantics.Term R (SymbolicCost.CoeffList ctx.dimension R)}
    (h : TermAgreement c actual reference) :
    SubexpSourceReference.TermRel decode (actual.syntax htarget) reference := by
  refine ⟨?_,h.2⟩
  exact (weightRaw_denote htarget hmodulus c actual.result.weight).trans h.1

private theorem forall₂_map_left {A B A' : Type*} {rel : A → B → Prop}
    {rel' : A' → B → Prop} (f : A → A')
    {xs : List A} {ys : List B} (h : List.Forall₂ rel xs ys)
    (he : ∀ a b, rel a b → rel' (f a) b) :
    List.Forall₂ rel' (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | @cons a b xs ys hab hrest ih => exact .cons (he a b hab) ih

include hmodulus in
theorem block_refines {a : Fin ctx.dimension → ℕ}
    {actual : TypedBlock p ctx a}
    {reference : SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)}
    (h : BlockAgreement c actual reference) :
    SubexpSourceReference.BlockRel decode (actual.syntax htarget) reference := by
  refine ⟨(weightRaw_denote htarget hmodulus c actual.result.weight).trans h.1,?_⟩
  exact forall₂_map_left _ h.2 (fun _ _ hg =>
    forall₂_map_left _ hg (fun _ _ ht => term_refines htarget hmodulus c ht))

include hmodulus in
/-- The leaf conditions assemble into the exact relation consumed by the
true-global-jet theorem. No whole-group equality is an input. -/
theorem blocks_refine {a : Fin ctx.dimension → ℕ}
    {actual : List (TypedBlock p ctx a)}
    {reference : List (SubexpBlockAssemblySemantics.Block R
      (SymbolicCost.CoeffList ctx.dimension R))}
    (h : List.Forall₂ (BlockAgreement c) actual reference) :
    List.Forall₂ (SubexpSourceReference.BlockRel decode)
      (actual.map (TypedBlock.syntax htarget)) reference :=
  forall₂_map_left _ h (fun _ _ hb => block_refines htarget hmodulus c hb)

include hmodulus in
/-- Source syntax and semantic refinement are derived together from the
actual output and the reusable input's local packet provenance. -/
theorem source_refinement_exists
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (honeBytes : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    {a : Fin ctx.dimension → ℕ}
    {inputs : List (BlockData ctx)} {outputs : List (BlockResult ctx a)}
    {reference : List (SubexpBlockAssemblySemantics.Block R
      (SymbolicCost.CoeffList ctx.dimension R))}
    (ha : List.Forall₂ (fun input output => output.input = input) inputs outputs)
    (hp : List.Forall₂ (BlockProvenance c a) inputs reference) :
    ∃ bs : List (TypedBlock p ctx a),
      SubexpMomentSourceProgram.source ctx outputs =
        SubexpPostfixControl.serializeCode
          (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
          (expression htarget bs).compile ∧
      List.Forall₂ (SubexpSourceReference.BlockRel decode)
        (bs.map (TypedBlock.syntax htarget)) reference := by
  obtain ⟨bs,hbs,hr⟩ := refine_outputs c ha hp
  have hb := source_bytes htarget hzero honeBytes bs
  rw [hbs] at hb
  exact ⟨bs,hb,blocks_refine htarget hmodulus c hr⟩

include hmodulus in
theorem jet_eq_reference
    (hone : coefficientValue p ctx.dimension c
      (1 : QuarticCode p ctx.dimension) =
        (1 : LiftRing.Extension (QuarticSearch.poly c)))
    (actual : (a : Fin ctx.dimension → ℕ) → List (TypedBlock p ctx a))
    (reference : (Fin ctx.dimension → ℕ) →
      List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)))
    (h : ∀ a ∈ Algorithm.exponentList ctx.dimension (2*ctx.dimension+1),
      List.Forall₂ (BlockAgreement c) (actual a) (reference a)) :
    Algorithm.executeRawJet (fun a =>
      (expression htarget (actual a)).map (decodeRaw decode)) =
      SubexpAlgorithm.executeJet (fun a => (reference a).map
        (SubexpBlockAssemblySemantics.Block.expression
          (SubexpWeightCode.rawScalar ctx.dimension))) := by
  have he := SubexpSourceReference.jet_eq_reference decode hone
    (fun a => (actual a).map (TypedBlock.syntax htarget)) reference
    (fun a ha => blocks_refine htarget hmodulus c (h a ha))
  simpa only [expression, blocks, List.map_map, Function.comp_def] using he

end Lists

end

end SubexponentialSAT.SubexpProducedSourceRefinement

end OAI.Algorithms
