import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRouting
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSerialization
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorBlueprint
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutChoices

namespace OAI.Algorithms

/-! Connect the physical router to the actual assignment and factor packets.
The assignment list is factors first, followed by vertex heads and padding.
The factor packet input is in original factor order, before color filtering. -/

namespace SubexponentialSAT.SubexpFactorRoutingAssignment

open BitProgram StructuredCalls SubexpFactorRoutingControl SubexpFactorRoutingCalls
open SubexpFactorRoutingTraversal MulticolorTypes SubexpTypeVariance
open Subexp.FactorBlueprint
open Subexp.ConstructivePacking

variable {V E : Type*} {r Q Δ : ℕ}

def factorItems (factors : List E) (ω : Assignment V E r Q Δ)
    (rows : E → List Row) : List (Item r Q) :=
  factors.map (fun e => (ω (.inl e), encodeRows (rows e)))

def assignmentSuffix (vertices : List V) (ω : Assignment V E r Q Δ) : List Bool :=
  ((Subexp.AssignmentEnumeration.sumList vertices
    (vertices.product (List.finRange Δ))).map
      (fun s => Subexp.ReadPlan.encodeWord (ω (.inr s)))).flatten

theorem seedRows_factor_prefix (vertices : List V) (factors : List E)
    (ω : Assignment V E r Q Δ) (rows : E → List Row) :
    (Subexp.ReadPlan.seedRows vertices factors ω).flatten =
      words (factorItems factors ω rows) ++ assignmentSuffix vertices ω := by
  simp [Subexp.ReadPlan.seedRows, Subexp.ReadPlan.seedWords,
    Subexp.AssignmentEnumeration.seedIndices, Subexp.AssignmentEnumeration.sumList,
    factorItems, words, assignmentSuffix, List.map_map, Function.comp_def,
    List.flatten_append]

theorem encodeList_map {A B : Type*} (enc : B → List Bool) (f : A → B) (xs : List A) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

theorem factorItems_packets (factors : List E) (ω : Assignment V E r Q Δ)
    (rows : E → List Row) :
    Encoding.encodeList id ((factorItems factors ω rows).map Prod.snd) =
      Encoding.encodeList encodeRows (factors.map rows) := by
  simp only [factorItems, List.map_map, Function.comp_def, encodeList_map, id_eq]

theorem retained_factorItems (factors : List E) (ω : Assignment V E r Q Δ)
    (rows : E → List Row) (t : Fin Q) (g : Fin r) :
    retained t g (factorItems factors ω rows) =
      ((factors.filter (fun e => decide (ω (.inl e) t = g))).map rows).map encodeRows := by
  induction factors with
  | nil => rfl
  | cons e es ih =>
      by_cases h : ω (.inl e) t = g
      · simpa [factorItems, retained, h] using congrArg (List.cons (encodeRows (rows e))) ih
      · simpa [factorItems, retained, h] using ih

/-- Exact routing of original factor packets using the supplied assignment.
The caller supplies the ungrouped packet master; the machine performs the
color test and stable filtering. -/
theorem factor_program_runs (vertices : List V) (factors : List E)
    (ω : Assignment V E r Q Δ) (rows : E → List Row) (t : Fin Q) (g : Fin r)
    (d : Data) (hc : Clean d)
    (h0 : d.stacks 0 = (Subexp.ReadPlan.seedRows vertices factors ω).flatten)
    (h1 : d.stacks 1 = Encoding.encodeList encodeRows (factors.map rows))
    (h2 : CounterPrograms.value (d.stacks 2) = g.val)
    (h3 : d.stacks 3 = unary t.val) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r) :
    RunsIn program (SubexpFactorRouting.runtime d t g
      (factorItems factors ω rows) (assignmentSuffix vertices ω))
      (d.withPC (some program.entry))
      ((result d (Encoding.encodeList encodeRows
        ((factors.filter (fun e => decide (ω (.inl e) t = g))).map rows))).withPC none) := by
  have hr := SubexpFactorRouting.program_runs t g (factorItems factors ω rows)
    (assignmentSuffix vertices ω) d hc
    (h0.trans (seedRows_factor_prefix vertices factors ω rows))
    (h1.trans (factorItems_packets factors ω rows).symm) h2 h3 h4 h5
  simpa only [retained_factorItems, encodeList_map, id_eq] using hr

section NaturalAssignment

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [NeZero r]

omit [NeZero r] in
/-- The physical natural-assignment output is interpreted in its proven
seed order. This is the assignment produced by the existing frontend. -/
theorem natural_program_runs (P : Factor.Pattern V E) (slots : SlotAssignment.SlotMap P Δ)
    (a : Word r Q) (tail : List (Word r Q)) (vertices : List V) (factors : List E)
    (hv : vertices.Nodup) (he : factors.Nodup) (rows : E → List Row)
    (t : Fin Q) (g : Fin r) (d : Data) (hc : Clean d)
    (h0 : d.stacks 0 = ((Subexp.NaturalAssignment.naturalValues P slots a tail vertices
      (Subexp.AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map
        Subexp.ReadPlan.encodeWord).flatten)
    (h1 : d.stacks 1 = Encoding.encodeList encodeRows (factors.map rows))
    (h2 : CounterPrograms.value (d.stacks 2) = g.val)
    (h3 : d.stacks 3 = unary t.val) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r) :
    let ω := Subexp.NaturalAssignment.naturalAssignment P slots a tail vertices
      (Subexp.AssignmentEnumeration.seedIndices vertices factors Δ)
    RunsIn program (SubexpFactorRouting.runtime d t g
      (factorItems factors ω rows) (assignmentSuffix vertices ω))
      (d.withPC (some program.entry))
      ((result d (Encoding.encodeList encodeRows
        ((factors.filter (fun e => decide (ω (.inl e) t = g))).map rows))).withPC none) := by
  apply factor_program_runs vertices factors _ rows t g d hc
  · exact h0.trans (Subexp.AssignmentSerialization.naturalValues_bytes_eq_seedRows
      P slots a tail vertices factors hv he)
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

omit [Fintype V] [NeZero r] in
theorem computed_color_eq (P : Factor.Pattern V E) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V)
    (indices : FiniteEnumeration (SeedIndex V E Δ)) (a : Word r Q)
    (tail : List (Word r Q)) (e : E) (t : Fin Q) :
    Subexp.ComputedLayout.factorWordsWithWords P slots vertices indices a tail e t =
      Subexp.NaturalAssignment.naturalAssignment P slots a tail
        vertices.values indices.values (.inl e) t := rfl

end NaturalAssignment

end SubexponentialSAT.SubexpFactorRoutingAssignment

end OAI.Algorithms
