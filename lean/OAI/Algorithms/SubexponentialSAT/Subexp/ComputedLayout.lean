import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.Layout
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix
import OAI.Algorithms.SubexponentialSAT.Subexp.NaturalAssignment

namespace OAI.Algorithms

/-!
# The layout with its computed assignment and computed block packing

The raw packing, inverse lookup, support test, and row lookup below are
executable definitions. Their correctness is connected to the full semantic
layout. No finite fiber equivalence is selected by classical choice.
-/

namespace SubexponentialSAT.Subexp.ComputedLayout

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open ConstructivePacking

section Assignment

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {r Q Δ k : ℕ} [NeZero r]

/-- Enumerate the whole universal block by its words. -/
def typeEnumeration (r Q Δ : ℕ) : FiniteEnumeration (UniversalType r Q Δ) where
  values := AssignmentEnumeration.universalAlphabet r Q Δ
  nodup := AssignmentEnumeration.universalAlphabet_nodup r Q Δ
  complete := AssignmentEnumeration.mem_universalAlphabet r Q Δ

/-- The exact computed factor words, using the explicit input enumerations. -/
def factorWords (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F) : F → Word r Q :=
  fun e => NaturalAssignment.enumeratedNaturalAssignment P slots
    vertices.values factors.values (.inl e)

/-- Bucket the exact computed labels and select the minimum full-block count. -/
def packing (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F) :
    PackingData V (UniversalType r Q Δ) where
  vertices := vertices
  types := typeEnumeration r Q Δ
  label := SubexpTypeVariance.assignmentType P slots
    (NaturalAssignment.enumeratedNaturalAssignment P slots vertices.values factors.values)

theorem packing_compatible (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F)
    (v : V) (e : SlotAssignment.Incident P v) :
    ((packing (r := r) (Q := Q) P slots vertices factors).label v).slot (slots v e) =
      factorWords P slots vertices factors e.val := by
  simpa only [packing, factorWords, NaturalAssignment.enumeratedNaturalAssignment_eq,
    AssignmentEnumeration.enumeratedAssignment] using
    (LocalExpectation.computedAssignment_consistent P slots
      (AssignmentEnumeration.firstWord r Q (Nat.pos_of_neZero r))
      (AssignmentEnumeration.remainingWords r Q) vertices.values
      (AssignmentEnumeration.seedIndices vertices.values factors.values Δ) v e)

theorem packing_deviation (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F) (hP : P.Bounded k Δ) :
    (∑ u : UniversalType r Q Δ,
      ((BlockPacking.count (packing P slots vertices factors).label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType r Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * Fintype.card V := by
  have h := NaturalAssignment.enumeratedNaturalAssignment_deviation_le (r := r) (Q := Q)
    P slots vertices.values factors.values vertices.nodup vertices.complete
    factors.nodup factors.complete hP
  simpa only [LocalExpectation.pairObjective, Variance.typeCount,
    BlockPacking.count_eq_filter_card, packing] using h

theorem packing_coverage (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F)
    (hP : P.Bounded k Δ) (τ : ℚ) (hτ : 0 ≤ τ)
    (hlarge : (Fintype.card (UniversalType r Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * Fintype.card V) :
    (1 - τ) * (Fintype.card V : ℚ) ≤
      ((packing (r := r) (Q := Q) P slots vertices factors).blockCount : ℚ) *
        Fintype.card (UniversalType r Q Δ) := by
  have hN : 0 < Fintype.card (UniversalType r Q Δ) := by
    rw [MulticolorTypes.card_universalType]
    exact pow_pos (Nat.pos_of_neZero r) _
  exact (packing P slots vertices factors).coverage_of_deviation_bound
    (1 + (Δ * k : ℕ)) τ hN hτ hlarge (packing_deviation P slots vertices factors hP)

end Assignment

section Lookup

variable {V U I C : Type*} [DecidableEq V] [DecidableEq U]

/-- Evaluate one embedded row by two explicit inverse lookups. -/
def rowValue [Zero C] [One C] (P : PackingData V U) (localRow : U → I → U → C)
    (i : I) (v w : V) : C :=
  match P.lookup v with
  | none => if w = v then 1 else 0
  | some (j, u) =>
      match P.lookup w with
      | none => 0
      | some (k, y) => if j = k then localRow u i y else 0

/-- Test a packed support using the same inverse lookup. -/
def supportAt (P : PackingData V U) (S : Finset U) (v : V) : Bool :=
  match P.lookup v with
  | none => false
  | some (_, u) => decide (u ∈ S)

theorem supportAt_iff (P : PackingData V U) (S : Finset U) (v : V) :
    supportAt P S v = true ↔ v ∈ DirectSums.packedSupportFinset P.completeBlocks.embed S := by
  rw [DirectSums.mem_packedSupportFinset]
  cases hv : P.lookup v with
  | none =>
      simp only [supportAt, hv, Bool.false_eq_true, false_iff]
      rintro ⟨j, u, _, h⟩
      have hh := (P.lookup_some_iff v (j, u)).mpr h
      simp [hv] at hh
  | some z =>
      rcases z with ⟨j, u⟩
      simp only [supportAt, hv, decide_eq_true_eq]
      constructor
      · intro hu
        exact ⟨j, u, hu, (P.lookup_some_iff v (j, u)).mp hv⟩
      · rintro ⟨k, y, hy, h⟩
        have hh := (P.lookup_some_iff v (k, y)).mpr h
        have he : (j, u) = (k, y) := Option.some.inj (hv.symm.trans hh)
        have hey : u = y := congrArg Prod.snd he
        simpa only [hey] using hy

variable {E : Type*} [Field E]

/-- The executable inverse lookup realizes the semantic extension-by-zero
row exactly, including coordinate rows on all uncovered vertices. -/
theorem rowValue_polynomial_eq (P : PackingData V U)
    (localRow : U → I → U → Polynomial E) (i : I) (v w : V) :
    rowValue P localRow i v w =
      _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow P.completeBlocks.embed localRow i v w := by
  cases hv : P.lookup v with
  | none =>
      rw [_root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_outside _ _ _ _ ((P.lookup_none_iff v).mp hv)]
      simp only [rowValue, hv]
      split_ifs <;> simp
  | some z =>
      rcases z with ⟨j, u⟩
      have hv' := (P.lookup_some_iff v (j, u)).mp hv
      rw [← hv', _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_apply]
      cases hw : P.lookup w with
      | none =>
          have hw' : w ∉ Set.range (_root_.OAI.Algorithms.SubexponentialSAT.Layout.blockEmbedding P.completeBlocks.embed j) := by
            rintro ⟨a, ha⟩
            exact (P.lookup_none_iff w).mp hw ⟨(j, a), ha⟩
          rw [_root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow_outside _ _ w hw']
          simp [rowValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hw]
      | some z =>
          rcases z with ⟨k, y⟩
          have hw' := (P.lookup_some_iff w (k, y)).mp hw
          rw [← hw']
          by_cases hj : j = k
          · subst k
            have hvalue : _root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow
                (_root_.OAI.Algorithms.SubexponentialSAT.Layout.blockEmbedding P.completeBlocks.embed j) (localRow u i)
                (P.completeBlocks.embed (j, y)) = localRow u i y :=
              _root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow_apply _ _ y
            rw [hvalue]
            simp [rowValue, PackingData.completeBlocks_apply, PackingData.lookup_at]
          · have hout : P.completeBlocks.embed (k, y) ∉
                Set.range (_root_.OAI.Algorithms.SubexponentialSAT.Layout.blockEmbedding P.completeBlocks.embed j) := by
              rintro ⟨a, ha⟩
              have he := P.completeBlocks.embed.injective ha
              exact hj (congrArg Prod.fst he)
            rw [_root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow_outside _ _ _ hout]
            simp [rowValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hj]

/-- Evaluated local row values may be embedded directly, without materializing
the global polynomial row. -/
theorem rowValue_eval (P : PackingData V U)
    (localRow : U → I → U → Polynomial E) (i : I) (v w : V) (z : E) :
    rowValue P (fun u i y => (localRow u i y).eval z) i v w =
      (_root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow P.completeBlocks.embed localRow i v w).eval z := by
  rw [← rowValue_polynomial_eq]
  cases hv : P.lookup v with
  | none => by_cases h : w = v <;> simp [rowValue, hv, h]
  | some v' =>
      cases hw : P.lookup w with
      | none => simp [rowValue, hv, hw]
      | some w' => by_cases h : v'.1 = w'.1 <;> simp [rowValue, hv, hw, h]

end Lookup

section LocalEvaluation

variable {K E : Type*} [Field K] [CommRing E]
variable {r Q Δ : ℕ} {node : Fin Q → E}

/-- Evaluate the actual universal row through the executable matrix recurrence
and explicit interpolation units. No polynomial object is materialized. -/
def universalRowValue (φ : K →+* E) (u : UniversalType r Q Δ) (i : Fin Δ)
    (R : ℕ) (coeff : ℕ → K) (units : SubexpRowInterpolation.NodeUnits node)
    (y : UniversalType r Q Δ) (x : E) : E :=
  SubexpAnnihilation.rowEvalForMatrices φ
    (fun t g i => ElementaryMatrix.jointMatrixDP i t g R coeff) u i R units y x

theorem universalRowValue_eq (φ : K →+* E) (u : UniversalType r Q Δ) (i : Fin Δ)
    (R : ℕ) (coeff : ℕ → K) (units : SubexpRowInterpolation.NodeUnits node)
    (y : UniversalType r Q Δ) (x : E) :
    universalRowValue φ u i R coeff units y x =
      (SubexpAnnihilation.universalRow φ u i R coeff units y).eval x := by
  unfold universalRowValue
  rw [SubexpAnnihilation.rowEvalForMatrices_eq]
  have hM : (fun (t : Fin Q) (g : Fin r) (i : Fin Δ) =>
      ElementaryMatrix.jointMatrixDP i t g R coeff) =
      (fun (t : Fin Q) (g : Fin r) (i : Fin Δ) =>
        MatrixSupport.jointMatrix i t g R coeff) := by
    funext t g i
    exact ElementaryMatrix.jointMatrixDP_eq i t g R coeff
  rw [hM]
  rfl

end LocalEvaluation

section SemanticLayout

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable [Field E] [Algebra (ZMod p) E]

/-- Inverse data for the supplied concrete nonzero node enumeration. -/
def unitsForNodes {Q : ℕ} (nodes : Fin Q ≃ {z : E // z ≠ 0}) :
    SubexpRowInterpolation.NodeUnits (fun t => (nodes t).val) :=
  SubexpRowInterpolation.NodeUnits.ofField (fun t => (nodes t).val)
    (Subtype.val_injective.comp nodes.injective) (fun t => (nodes t).property)

/-- The full semantic layout uses exactly the computed factor words, labels,
minimum-count blocks, and their explicit placement. Its row lookup is related
to an executable function below. -/
noncomputable def layout (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : Layout.UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F) :
    SubexpLayoutSpec.Layout (E := E) P c :=
  Layout.fromBlocks P c hP hsize hE nodes B slots
    (factorWords P slots vertices factors) (packing P slots vertices factors).label
    (packing_compatible P slots vertices factors)
    (packing P slots vertices factors).completeBlocks
    (packing_coverage P slots vertices factors hP τ (le_of_lt c.tau_pos)
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
variable (vertices : FiniteEnumeration V) (factors : FiniteEnumeration F)

@[simp] theorem layout_color :
    (layout P c hP hsize hthreshold hE nodes B slots vertices factors).color =
      factorWords P slots vertices factors := rfl

@[simp] theorem layout_K (t : Fin c.Q) :
    (layout P c hP hsize hthreshold hE nodes B slots vertices factors).K t =
      fun g => DirectSums.packedSubspace
        (packing P slots vertices factors).completeBlocks.embed (B.space t g) := rfl

/-- Support membership uses the actual packing lookup, without classical
inversion of the embedding. -/
theorem layout_supportAt (t : Fin c.Q) (g : Fin r) (v : V) :
    supportAt (packing P slots vertices factors)
      (MulticolorTypes.side (Δ := Δ) t g).toFinset v = true ↔
    v ∈ (layout P c hP hsize hthreshold hE nodes B slots vertices factors).support t g :=
  supportAt_iff _ _ _

/-- The semantic incidence row is evaluated by two computed block lookups
and the supplied local row evaluator. -/
theorem layout_row_eval (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) :
    ((layout P c hP hsize hthreshold hE nodes B slots vertices factors).row e v w).eval z =
      rowValue (packing P slots vertices factors)
        (fun u i y => (B.row u i y).eval z) (slots v.val ⟨e, v.property⟩) v.val w :=
  (rowValue_eval _ B.row _ v.val w z).symm

include hP hsize hthreshold hE in
/-- Concrete searched parity coefficients and the displayed probability tail
discharge the local block input of the computed packing construction. -/
noncomputable def layoutOfTail (A : ℕ)
    (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ)) :
    SubexpLayoutSpec.Layout (E := E) P c := by
  let units := unitsForNodes nodes
  let B : Layout.UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val) :=
    Layout.universalBlockOfSearch c.p_odd τ (le_of_lt c.tau_pos) A c.R units
      ((SpectralRank.normalizedTail_le_iff r (c.Q - 1) A c.R Δ τ
        (by have := c.r_ge_two; omega) c.delta_pos).mp htail)
  exact layout P c hP hsize hthreshold hE nodes B slots vertices factors

/-- Actual scalar row access: selected coefficients, DP matrix entries,
explicit interpolation, and the two computed block lookups. -/
def computedRowAt (A : ℕ) (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) : E :=
  rowValue (packing (r := r) (Q := c.Q) P slots vertices factors)
    (fun u i y => universalRowValue (algebraMap (ZMod p) E) u i c.R
      (CoefficientSearch.coefficientsNat p A c.R) (unitsForNodes nodes) y z)
    (slots v.val ⟨e, v.property⟩) v.val w

theorem layoutOfTail_row_eval (A : ℕ)
    (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) (z : E) :
    ((layoutOfTail P c hP hsize hthreshold hE nodes slots vertices factors A htail).row e v w).eval z =
      computedRowAt P c nodes slots vertices factors A e v w z := by
  simp only [layoutOfTail, layout_row_eval, computedRowAt, universalRowValue_eq,
    Layout.universalBlockOfSearch, Layout.universalBlockOfRank]

end SemanticLayout

end SubexponentialSAT.Subexp.ComputedLayout

end OAI.Algorithms
