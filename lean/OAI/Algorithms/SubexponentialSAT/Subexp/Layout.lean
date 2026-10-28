import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Layout
import OAI.Algorithms.SubexponentialSAT.MulticolorTypes
import OAI.Algorithms.SubexponentialSAT.SubexpBlockPacking
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpTypeVariance
import OAI.Algorithms.SubexponentialSAT.SubexpAnnihilation
import OAI.Algorithms.SubexponentialSAT.Subexp.SpectralRank
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearch

namespace OAI.Algorithms

/-!
# Assembly of the multi-color interpolation layout

The rows in this construction annihilate every color other than the factor's
own color. The base-field spaces and extension-field coefficients are kept
separate. This file assembles the finite mathematical layout; a machine-level
uniform construction-cost theorem is not asserted by these structures.
-/

noncomputable section

namespace SubexponentialSAT.Subexp.Layout

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

/-- Concrete universal-block data. Unlike the old binary layout, every row
must annihilate all subspaces whose color differs from its selected slot. -/
structure UniversalBlock (K E : Type*) [Field K] [Field E] [Algebra K E]
    (r Q Δ R : ℕ) (τ : ℚ) (node : Fin Q → E) where
  space : Fin Q → Fin r → Submodule K (UniversalType r Q Δ → K)
  supported : ∀ t g x, x ∈ space t g → ∀ u, u.head t ≠ g → x u = 0
  dimension : ∀ t g,
    (1 - τ) * (Fintype.card (UniversalType r Q Δ) : ℚ) ≤
      (r : ℚ) * Module.finrank K (space t g)
  row : UniversalType r Q Δ → Fin Δ → UniversalType r Q Δ → Polynomial E
  origin : ∀ u i y, (row u i y).eval 0 =
    (Pi.single u (1 : E) : UniversalType r Q Δ → E) y
  degree : ∀ u i y, (row u i y).natDegree ≤ R
  annihilates : ∀ u i t g, g ≠ u.slot i t → ∀ x, x ∈ space t g →
    (∑ y, (row u i y).eval (node t) * algebraMap K E (x y)) = 0

/-- Distinct head colors have disjoint finite supports. -/
theorem side_finset_disjoint {r Q Δ : ℕ} (t : Fin Q) {g h : Fin r} (hne : g ≠ h) :
    Disjoint (MulticolorTypes.side (Δ := Δ) t g).toFinset
      (MulticolorTypes.side (Δ := Δ) t h).toFinset :=
  Set.disjoint_toFinset.mpr (MulticolorTypes.side_disjoint t hne)

section GlobalAssembly

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F]
variable [Field E] [Algebra (ZMod p) E]

/-- Embed the actual multi-color block on every full copy in the packing.
One incidence row is used simultaneously for all other colors. -/
def fromBlocks (P : Factor.Pattern V F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ) (sigma : F → Word r c.Q)
    (label : V → UniversalType r c.Q Δ)
    (compatible : ∀ v (e : SlotAssignment.Incident P v),
      (label v).slot (slots v e) = sigma e.val)
    {b : ℕ} (blocks : BlockPacking.CompleteBlocks label b)
    (hcover : (1 - τ) * (Fintype.card V : ℚ) ≤
      (b : ℚ) * Fintype.card (UniversalType r c.Q Δ)) :
    SubexpLayoutSpec.Layout (E := E) P c := by
  classical
  refine {
    bounded := hP
    size_ge := hsize
    extension_degree := hE
    nodes := nodes
    support := fun t g => DirectSums.packedSupportFinset blocks.embed
      (MulticolorTypes.side (Δ := Δ) t g).toFinset
    support_disjoint := ?_
    support_upper := ?_
    K := fun t g => DirectSums.packedSubspace blocks.embed (B.space t g)
    supported := ?_
    dimension_lower := ?_
    color := sigma
    row := fun e v => _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow blocks.embed B.row
      (slots v.val ⟨e,v.property⟩) v.val
    row_zero := ?_
    row_degree := ?_
    annihilation := ?_
  }
  · intro t g h hne
    exact DirectSums.packedSupportFinset_disjoint blocks.embed _ _
      (side_finset_disjoint t hne)
  · intro t g
    apply SubexpBlockPacking.packed_support_card_upper blocks _ r
    rw [Set.toFinset_card]
    exact le_of_eq (MulticolorTypes.card_full_eq_mul_side (Δ := Δ) t g).symm
  · intro t g x hx v hv
    apply DirectSums.packed_supported_finset blocks.embed (B.space t g)
      (MulticolorTypes.side (Δ := Δ) t g).toFinset _ hx v hv
    intro x hx u hu
    apply B.supported t g x hx u
    simpa only [Set.mem_toFinset, MulticolorTypes.mem_side] using hu
  · intro t g
    apply SubexpBlockPacking.packed_finrank_lower blocks (B.space t g) τ r _ hcover
      (B.dimension t g)
    linarith [c.tau_le_half]
  · intro e v w
    apply _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_origin
    intro u i y
    rw [B.origin]
    simp only [Pi.single_apply]
  · intro e v w
    exact _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_degree blocks.embed B.row B.degree _ v.val w
  · intro t e v g x hother hx
    let i := slots v.val ⟨e,v.property⟩
    change (∑ w, (_root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow blocks.embed B.row i v.val w).eval
      (nodes t).val * algebraMap (ZMod p) E (x w)) = 0
    by_cases hv : v.val ∈ Set.range blocks.embed
    · obtain ⟨⟨j,u⟩, hju⟩ := hv
      have hcolor : u.slot i t = sigma e t := by
        have hh := congrFun (compatible v.val ⟨e,v.property⟩) t
        change (label v.val).slot i t = sigma e t at hh
        rw [← hju, blocks.type_eq j u] at hh
        exact hh
      have hrow : _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow blocks.embed B.row i v.val =
          _root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow
            (_root_.OAI.Algorithms.SubexponentialSAT.Layout.blockEmbedding blocks.embed j) (B.row u i) := by
        rw [← hju, _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_apply]
      rw [hrow, _root_.OAI.Algorithms.SubexponentialSAT.Layout.embeddedRow_pairing]
      apply B.annihilates u i t g
      · simpa only [hcolor] using hother
      · exact DirectSums.packed_restriction_mem blocks.embed (B.space t g) hx j
    · rw [_root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow_outside blocks.embed B.row i v.val hv]
      have hz := DirectSums.packed_zero_outside blocks.embed (B.space t g) hx v.val hv
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w = v.val <;> simp [hw, hz]

/-- Bounded incidence supplies a balanced, globally consistent multicolor
type assignment; the quantitative threshold then supplies the actual blocks. -/
theorem exists_of_universalBlock (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val)) :
    Nonempty (SubexpLayoutSpec.Layout (E := E) P c) := by
  classical
  let : NeZero r := ⟨by have := c.r_ge_two; omega⟩
  let slots := SlotAssignment.slotsOfBounded P hP
  obtain ⟨sigma, label, hcompatible, hdev⟩ :=
    SubexpTypeVariance.exists_consistent_types_deviation_le (r := r) (Q := c.Q) P slots hP
  have hN : 0 < Fintype.card (UniversalType r c.Q Δ) := by
    rw [MulticolorTypes.card_universalType]
    exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne r)) _
  have hdev' : (∑ u : UniversalType r c.Q Δ,
      ((BlockPacking.count label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType r c.Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType r c.Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * Fintype.card V := by
    simpa only [BlockPacking.count_eq_filter_card] using hdev
  have hlarge : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * Fintype.card V :=
    hthreshold.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) (sq_nonneg τ))
  obtain ⟨b, blocks, hcover⟩ := SubexpBlockPacking.exists_completeBlocks_of_deviation_bound
    label (1 + (Δ * k : ℕ)) τ hN (le_of_lt c.tau_pos) hlarge hdev'
  exact ⟨fromBlocks P c hP hsize hE nodes B slots sigma label hcompatible blocks hcover⟩

end GlobalAssembly

section ActualUniversalBlock

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
variable {r Q Δ R : ℕ} {node : Fin Q → E}

/-- The concrete swap matrices, common fixed spaces and explicit mismatch
interpolation give the universal block. Only the actual matrix rank bound is
an input to this assembly; support and all-other-color annihilation are proved. -/
def universalBlockOfRank (τ : ℚ) (hτ : 0 ≤ τ) (coeff : ℕ → K)
    (units : SubexpRowInterpolation.NodeUnits node)
    (hrank : ∀ (t : Fin Q) (g : Fin r) (i : Fin Δ),
      (Δ : ℚ) * Module.finrank K (LinearMap.range
        (LinearMap.id - (Subexp.MatrixSupport.jointMatrix i t g R coeff).mulVecLin)) ≤
          τ * Fintype.card (Joint t g i)) : UniversalBlock K E r Q Δ R τ node where
  space t g := Subexp.SubspaceDimension.universalFixedSpace t g
    (fun i => (Subexp.MatrixSupport.jointMatrix i t g R coeff).mulVecLin)
  supported t g _x hx := Subexp.SubspaceDimension.universalFixedSpace_supported t g _ hx
  dimension t g := Subexp.SubspaceDimension.universalFixedSpace_card_lower t g _ τ hτ
    (hrank t g)
  row u i := SubexpAnnihilation.universalRow (algebraMap K E) u i R coeff units
  origin u i y := congrFun
    (SubexpAnnihilation.universalRow_origin (algebraMap K E) u i R coeff units) y
  degree u i y := SubexpAnnihilation.universalRow_degree
    (algebraMap K E) u i R coeff units y
  annihilates u i t g hg x hx := SubexpAnnihilation.universalRow_annihilates
    (algebraMap K E) u i R coeff units t g hg x hx

/-- The explicit weighted-binomial tail discharges the matrix rank obligation.
Coefficients are the constructed consecutive-binomial parity coefficients. -/
def universalBlockOfTail (h2 : (2 : K) ≠ 0) (τ : ℚ) (hτ : 0 ≤ τ) (A R : ℕ)
    (units : SubexpRowInterpolation.NodeUnits node)
    (htail : (Δ : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (Q - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity r)
        (SubexpSwapMultiplicity.negativeMultiplicity r) A R : ℚ) ≤
      τ * (((SubexpSwapMultiplicity.positiveMultiplicity r +
        SubexpSwapMultiplicity.negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    UniversalBlock K E r Q Δ R τ node :=
  universalBlockOfRank τ hτ
    (BinomialInterpolation.extendCoefficients (BinomialInterpolation.parityCoefficients A R))
    units (fun t g i => Subexp.SpectralRank.jointMatrix_parity_rank_bound h2 t g i A R τ htail)

end ActualUniversalBlock

section SelectedCoefficients

variable {p r Q Δ : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra (ZMod p) E] {node : Fin Q → E}

/-- The universal block can use the coefficients returned by the explicit
finite search. Its executed coefficient computation never inverts an abstract
interpolation matrix. -/
def universalBlockOfSearch (hodd : Odd p) (τ : ℚ) (hτ : 0 ≤ τ) (A R : ℕ)
    (units : SubexpRowInterpolation.NodeUnits node)
    (htail : (Δ : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (Q - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity r)
        (SubexpSwapMultiplicity.negativeMultiplicity r) A R : ℚ) ≤
      τ * (((SubexpSwapMultiplicity.positiveMultiplicity r +
        SubexpSwapMultiplicity.negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    UniversalBlock (ZMod p) E r Q Δ R τ node :=
  universalBlockOfRank τ hτ (Subexp.CoefficientSearch.coefficientsNat p A R) units
    (fun t g i => Subexp.SpectralRank.jointMatrix_rank_bound
      (_root_.OAI.Algorithms.SubexponentialSAT.Layout.two_ne_zero hodd) t g i A R
      (Subexp.CoefficientSearch.coefficientsNat p A R) τ
      (fun w hw => Subexp.CoefficientSearch.coefficientsNat_spec_of_mem p A R w
        (Fact.out : p.Prime).pos (Finset.mem_Ico.mp hw).1 (Finset.mem_Ico.mp hw).2)
      htail)

end SelectedCoefficients

section MainExistence

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]

/-- The concrete construction works over the supplied extension field. In
particular, an explicitly represented quotient field and its enumerated nodes
can be used without transporting through a separately chosen Galois field. -/
theorem exists_of_tail_over {E : Type*} [Field E] [Algebra (ZMod p) E]
    (P : Factor.Pattern V F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0}) (A : ℕ)
    (htail : (Δ : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (c.Q - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity r)
        (SubexpSwapMultiplicity.negativeMultiplicity r) A c.R : ℚ) ≤
      τ * (((SubexpSwapMultiplicity.positiveMultiplicity r +
        SubexpSwapMultiplicity.negativeMultiplicity r) ^ (c.Q - 1) : ℕ) : ℚ)) :
    Nonempty (SubexpLayoutSpec.Layout (E := E) P c) := by
  let units := SubexpRowInterpolation.NodeUnits.ofField (fun t => (nodes t).val)
    (Subtype.val_injective.comp nodes.injective) (fun t => (nodes t).property)
  let B : UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val) :=
    universalBlockOfTail (_root_.OAI.Algorithms.SubexponentialSAT.Layout.two_ne_zero c.p_odd) τ (le_of_lt c.tau_pos)
      A c.R units htail
  exact exists_of_universalBlock P c hP hsize hthreshold hE nodes B

/-- Finite mathematical form of Lemma 3.2. The only quantitative hypotheses
are the actual binomial tail and block threshold. The matrix, row, support,
variance, type assignment and direct-sum layout properties are all discharged. -/
theorem exists_of_tail (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar) (A : ℕ)
    (htail : (Δ : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (c.Q - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity r)
        (SubexpSwapMultiplicity.negativeMultiplicity r) A c.R : ℚ) ≤
      τ * (((SubexpSwapMultiplicity.positiveMultiplicity r +
        SubexpSwapMultiplicity.negativeMultiplicity r) ^ (c.Q - 1) : ℕ) : ℚ)) :
    Nonempty (SubexpLayoutSpec.Layout
      (E := _root_.OAI.Algorithms.SubexponentialSAT.Layout.Extension p c.h) P c) := by
  let nodes : Fin c.Q ≃ {z : _root_.OAI.Algorithms.SubexponentialSAT.Layout.Extension p c.h // z ≠ 0} :=
    (Equiv.cast (congrArg Fin c.Q_eq)).trans
      (_root_.OAI.Algorithms.SubexponentialSAT.Layout.extensionNodes p c.h (Nat.ne_of_gt c.h_pos))
  exact exists_of_tail_over P c hP hsize hthreshold
    (_root_.OAI.Algorithms.SubexponentialSAT.Layout.extension_finrank p c.h (Nat.ne_of_gt c.h_pos)) nodes A htail

/-- The source's explicit ceiling value for Dstar discharges the block-size
inequality in the main constructor. -/
theorem exists_of_tail_ceiling (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hDstar : c.Dstar = SubexpBlockPacking.threshold
      (Fintype.card (UniversalType r c.Q Δ)) (1 + (Δ * k : ℕ)) τ) (A : ℕ)
    (htail : (Δ : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (c.Q - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity r)
        (SubexpSwapMultiplicity.negativeMultiplicity r) A c.R : ℚ) ≤
      τ * (((SubexpSwapMultiplicity.positiveMultiplicity r +
        SubexpSwapMultiplicity.negativeMultiplicity r) ^ (c.Q - 1) : ℕ) : ℚ)) :
    Nonempty (SubexpLayoutSpec.Layout
      (E := _root_.OAI.Algorithms.SubexponentialSAT.Layout.Extension p c.h) P c) := by
  apply exists_of_tail P c hP hsize _ A htail
  apply (SubexpBlockPacking.threshold_le_iff _ c.Dstar _ τ c.tau_pos).mp
  rw [← hDstar]

/-- Probability-tail version over a supplied extension field. The finite
weighted multiplicity denominator is cleared by the proved spectral identity. -/
theorem exists_of_probability_tail_over {E : Type*} [Field E] [Algebra (ZMod p) E]
    (P : Factor.Pattern V F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0}) (A : ℕ)
    (htail : Subexp.SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ)) :
    Nonempty (SubexpLayoutSpec.Layout (E := E) P c) := by
  apply exists_of_tail_over P c hP hsize hthreshold hE nodes A
  exact (Subexp.SpectralRank.normalizedTail_le_iff r (c.Q - 1) A c.R Δ τ
    (by have := c.r_ge_two; omega) c.delta_pos).mp htail

/-- Probability-tail version with the standard finite extension. -/
theorem exists_of_probability_tail (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar) (A : ℕ)
    (htail : Subexp.SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ)) :
    Nonempty (SubexpLayoutSpec.Layout
      (E := _root_.OAI.Algorithms.SubexponentialSAT.Layout.Extension p c.h) P c) := by
  apply exists_of_tail P c hP hsize hthreshold A
  exact (Subexp.SpectralRank.normalizedTail_le_iff r (c.Q - 1) A c.R Δ τ
    (by have := c.r_ge_two; omega) c.delta_pos).mp htail

end MainExistence

section ComputedAssignmentBridge

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {r Q Δ k : ℕ} [NeZero r]

/-- The actual multicolor conditional-expectation program supplies these
exact labels to the packing theorem. The only further selection here is the
finite selection of complete blocks. -/
theorem exists_blocks_for_computedAssignment (P : Factor.Pattern V F)
    (slots : SlotAssignment.SlotMap P Δ) (hP : P.Bounded k Δ) (τ : ℚ) (hτ : 0 ≤ τ)
    (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SubexpTypeVariance.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices)
    (hlarge : (Fintype.card (UniversalType r Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * Fintype.card V) :
    let label := SubexpTypeVariance.assignmentType P slots
      (Subexp.LocalExpectation.computedAssignment P slots a tail vertices indices)
    ∃ b, ∃ _blocks : BlockPacking.CompleteBlocks label b,
      (1 - τ) * (Fintype.card V : ℚ) ≤
        (b : ℚ) * Fintype.card (UniversalType r Q Δ) := by
  dsimp only
  let label := SubexpTypeVariance.assignmentType P slots
    (Subexp.LocalExpectation.computedAssignment P slots a tail vertices indices)
  have hdev := Subexp.LocalExpectation.computedAssignment_deviation_le P slots a tail
    haNodup haFull vertices hvNodup hvFull indices hiNodup hiFull hP
  have hdev' : (∑ u : UniversalType r Q Δ,
      ((BlockPacking.count label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType r Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * Fintype.card V := by
    simpa only [Subexp.LocalExpectation.pairObjective, Variance.typeCount,
      BlockPacking.count_eq_filter_card, label] using hdev
  have hN : 0 < Fintype.card (UniversalType r Q Δ) := by
    rw [MulticolorTypes.card_universalType]
    exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne r)) _
  exact SubexpBlockPacking.exists_completeBlocks_of_deviation_bound label
    (1 + (Δ * k : ℕ)) τ hN hτ hlarge hdev'

variable {p : ℕ} {τ : ℚ} [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra (ZMod p) E]

/-- The returned layout has exactly the factor words computed by the local
program. No separately chosen type assignment is substituted. All matrix and
row choices are supplied by the concrete universal block argument. -/
theorem exists_layout_with_computed_words (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ) (hP : P.Bounded k Δ)
    (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ)
    (a : Word r c.Q) (tail : List (Word r c.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SubexpTypeVariance.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices) :
    ∃ L : SubexpLayoutSpec.Layout (E := E) P c,
      L.color = fun e => Subexp.LocalExpectation.computedAssignment
        P slots a tail vertices indices (.inl e) := by
  let omega := Subexp.LocalExpectation.computedAssignment P slots a tail vertices indices
  let label := SubexpTypeVariance.assignmentType P slots omega
  let sigma := fun e => omega (.inl e)
  have hcompatible : ∀ v (e : SlotAssignment.Incident P v),
      (label v).slot (slots v e) = sigma e.val := by
    intro v e
    exact Subexp.LocalExpectation.computedAssignment_consistent
      P slots a tail vertices indices v e
  have hlarge : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * Fintype.card V :=
    hthreshold.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) (sq_nonneg τ))
  obtain ⟨b, blocks, hcover⟩ := exists_blocks_for_computedAssignment P slots hP τ
    (le_of_lt c.tau_pos) a tail haNodup haFull vertices hvNodup hvFull
    indices hiNodup hiFull hlarge
  exact ⟨fromBlocks P c hP hsize hE nodes B slots sigma label hcompatible blocks hcover, rfl⟩

/-- Concrete coefficients and the concrete conditional-expectation assignment
both feed the actual layout construction. Complete-block selection and its
representation are still separate from the executable search specifications. -/
theorem exists_layout_with_computed_data (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ) (hP : P.Bounded k Δ)
    (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0}) (A : ℕ)
    (htail : Subexp.SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))
    (slots : SlotAssignment.SlotMap P Δ)
    (a : Word r c.Q) (tail : List (Word r c.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SubexpTypeVariance.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices) :
    ∃ L : SubexpLayoutSpec.Layout (E := E) P c,
      L.color = fun e => Subexp.LocalExpectation.computedAssignment
        P slots a tail vertices indices (.inl e) := by
  let units := SubexpRowInterpolation.NodeUnits.ofField (fun t => (nodes t).val)
    (Subtype.val_injective.comp nodes.injective) (fun t => (nodes t).property)
  let B : UniversalBlock (ZMod p) E r c.Q Δ c.R τ (fun t => (nodes t).val) :=
    universalBlockOfSearch c.p_odd τ (le_of_lt c.tau_pos) A c.R units
      ((Subexp.SpectralRank.normalizedTail_le_iff r (c.Q - 1) A c.R Δ τ
        (by have := c.r_ge_two; omega) c.delta_pos).mp htail)
  exact exists_layout_with_computed_words P c hP hsize hthreshold hE nodes B slots
    a tail haNodup haFull vertices hvNodup hvFull indices hiNodup hiFull

end ComputedAssignmentBridge

end SubexponentialSAT.Subexp.Layout

end

end OAI.Algorithms
