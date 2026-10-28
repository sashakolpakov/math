import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayout

namespace OAI.Algorithms

/-!
# Computed layouts with the actual runtime enumeration orders

The word, seed, vertex, and universal-type lists may have any complete nodup
order. The construction uses those lists directly, so no equality to an
independently chosen assignment or packing is required.
-/

namespace SubexponentialSAT.Subexp.ComputedLayout

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes ConstructivePacking

section Assignment

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {r Q Δ k : ℕ} [NeZero r]

/-- Factor words selected with the supplied word and seed orders. -/
def factorWordsWithWords (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V)
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q)) : F → Word r Q :=
  fun e => NaturalAssignment.naturalAssignment P slots a tail
    vertices.values indices.values (.inl e)

/-- Bucket precisely the labels selected by the supplied runtime lists. -/
def packingWithWords (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q)) : PackingData V (UniversalType r Q Δ) where
  vertices := vertices
  types := types
  label := SubexpTypeVariance.assignmentType P slots
    (NaturalAssignment.naturalAssignment P slots a tail vertices.values indices.values)

omit [NeZero r] in
theorem packingWithWords_compatible (P : Factor.Pattern V F)
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q))
    (v : V) (e : SlotAssignment.Incident P v) :
    ((packingWithWords P slots vertices types indices a tail).label v).slot (slots v e) =
      factorWordsWithWords P slots vertices indices a tail e.val :=
  NaturalAssignment.naturalAssignment_consistent P slots a tail
    vertices.values indices.values v e

theorem packingWithWords_deviation (P : Factor.Pattern V F)
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail) (hP : P.Bounded k Δ) :
    (∑ u : UniversalType r Q Δ,
      ((BlockPacking.count (packingWithWords P slots vertices types indices a tail).label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType r Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * Fintype.card V := by
  have h := NaturalAssignment.naturalAssignment_deviation_le P slots a tail haNodup haFull
    vertices.values vertices.nodup vertices.complete
    indices.values indices.nodup indices.complete hP
  simpa only [LocalExpectation.pairObjective, Variance.typeCount,
    BlockPacking.count_eq_filter_card, packingWithWords] using h

theorem packingWithWords_coverage (P : Factor.Pattern V F)
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (hP : P.Bounded k Δ) (τ : ℚ) (hτ : 0 ≤ τ)
    (hlarge : (Fintype.card (UniversalType r Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * Fintype.card V) :
    (1 - τ) * (Fintype.card V : ℚ) ≤
      ((packingWithWords P slots vertices types indices a tail).blockCount : ℚ) *
        Fintype.card (UniversalType r Q Δ) := by
  have hN : 0 < Fintype.card (UniversalType r Q Δ) := by
    rw [MulticolorTypes.card_universalType]
    exact pow_pos (Nat.pos_of_neZero r) _
  exact (packingWithWords P slots vertices types indices a tail).coverage_of_deviation_bound
    (1 + (Δ * k : ℕ)) τ hN hτ hlarge
    (packingWithWords_deviation P slots vertices types indices a tail haNodup haFull hP)

end Assignment

section SemanticLayout

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable [Field E] [Algebra (ZMod p) E]

/-- The semantic layout interpreted from exactly the supplied runtime orders. -/
noncomputable def layoutWithWords (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : Layout.UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r c.Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r c.Q) (tail : List (Word r c.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail) :
    SubexpLayoutSpec.Layout (E := E) P c :=
  Layout.fromBlocks P c hP hsize hE nodes B slots
    (factorWordsWithWords P slots vertices indices a tail)
    (packingWithWords P slots vertices types indices a tail).label
    (packingWithWords_compatible P slots vertices types indices a tail)
    (packingWithWords P slots vertices types indices a tail).completeBlocks
    (packingWithWords_coverage P slots vertices types indices a tail haNodup haFull
      hP τ (le_of_lt c.tau_pos)
      (hthreshold.trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) (sq_nonneg τ))))

variable (P : Factor.Pattern V F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
variable (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
  (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
variable (hE : Module.finrank (ZMod p) E = c.h)
variable (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
variable (B : Layout.UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val))
variable (slots : SlotAssignment.SlotMap P Δ)
variable (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)

@[simp] theorem layoutWithWords_color :
    (layoutWithWords P c hP hsize hthreshold hE nodes B slots
      vertices types indices a tail haNodup haFull).color =
      factorWordsWithWords P slots vertices indices a tail := rfl

@[simp] theorem layoutWithWords_K (t : Fin c.Q) :
    (layoutWithWords P c hP hsize hthreshold hE nodes B slots
      vertices types indices a tail haNodup haFull).K t =
      fun g => DirectSums.packedSubspace
        (packingWithWords P slots vertices types indices a tail).completeBlocks.embed
        (B.space t g) := rfl

theorem layoutWithWords_supportAt (t : Fin c.Q) (g : Fin r) (v : V) :
    supportAt (packingWithWords P slots vertices types indices a tail)
      (MulticolorTypes.side (Δ := Δ) t g).toFinset v = true ↔
    v ∈ (layoutWithWords P c hP hsize hthreshold hE nodes B slots
      vertices types indices a tail haNodup haFull).support t g :=
  supportAt_iff _ _ _

theorem layoutWithWords_row_eval (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) :
    ((layoutWithWords P c hP hsize hthreshold hE nodes B slots
      vertices types indices a tail haNodup haFull).row e v w).eval z =
      rowValue (packingWithWords P slots vertices types indices a tail)
        (fun u i y => (B.row u i y).eval z) (slots v.val ⟨e, v.property⟩) v.val w :=
  (rowValue_eval _ B.row _ v.val w z).symm

include hP hsize hthreshold hE haNodup haFull in
/-- Actual searched coefficients and the stated tail bound discharge the
universal block input, with no restriction on runtime enumeration order. -/
noncomputable def layoutWithWordsOfTail (A : ℕ)
    (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ)) :
    SubexpLayoutSpec.Layout (E := E) P c := by
  let units := unitsForNodes nodes
  let B : Layout.UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val) :=
    Layout.universalBlockOfSearch c.p_odd τ (le_of_lt c.tau_pos) A c.R units
      ((SpectralRank.normalizedTail_le_iff r (c.Q - 1) A c.R Δ τ
        (by have := c.r_ge_two; omega) c.delta_pos).mp htail)
  exact layoutWithWords P c hP hsize hthreshold hE nodes B slots
    vertices types indices a tail haNodup haFull

/-- Scalar row access through the actual assignment and packing orders. -/
def computedRowAtWithWords (A : ℕ) (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) : E :=
  rowValue (packingWithWords P slots vertices types indices a tail)
    (fun u i y => universalRowValue (algebraMap (ZMod p) E) u i c.R
      (CoefficientSearch.coefficientsNat p A c.R) (unitsForNodes nodes) y z)
    (slots v.val ⟨e, v.property⟩) v.val w

theorem layoutWithWordsOfTail_row_eval (A : ℕ)
    (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) :
    ((layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
      vertices types indices a tail haNodup haFull A htail).row e v w).eval z =
      computedRowAtWithWords P c nodes slots vertices types indices a tail A e v w z := by
  simp only [layoutWithWordsOfTail, layoutWithWords_row_eval, computedRowAtWithWords,
    universalRowValue_eq, Layout.universalBlockOfSearch, Layout.universalBlockOfRank]

end SemanticLayout

end SubexponentialSAT.Subexp.ComputedLayout

end OAI.Algorithms
