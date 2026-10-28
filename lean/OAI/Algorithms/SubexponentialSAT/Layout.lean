import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Types
import OAI.Algorithms.SubexponentialSAT.Factor
import OAI.Algorithms.SubexponentialSAT.SlotAssignment
import OAI.Algorithms.SubexponentialSAT.BlockPacking
import OAI.Algorithms.SubexponentialSAT.RowInterpolation
import OAI.Algorithms.SubexponentialSAT.Annihilation
import OAI.Algorithms.SubexponentialSAT.LayoutSpec
import OAI.Algorithms.SubexponentialSAT.DirectSums
import OAI.Algorithms.SubexponentialSAT.TypeDistribution
import OAI.Algorithms.SubexponentialSAT.SpectralRank
import OAI.Algorithms.SubexponentialSAT.LayoutParameters
import OAI.Algorithms.SubexponentialSAT.BinomialInterpolation
import OAI.Algorithms.SubexponentialSAT.LocalExpectation

namespace OAI.Algorithms

/-!
# Assembly of interpolation layouts

This module constructs the finite extension and records concrete universal-block
and packing data used in the global layout assembly. A universal-block interface
is not itself asserted to exist without the spectral and support construction.
-/

noncomputable section
namespace SubexponentialSAT.Layout

open scoped BigOperators
open SubexponentialSAT.Types SubexponentialSAT.Factor

section Extension

variable (p h : ℕ) [Fact p.Prime]

/-- The actual degree-h finite extension used by the construction. -/
abbrev Extension := GaloisField p h

instance extensionFintype : Fintype (Extension p h) := Fintype.ofFinite _

@[simp] theorem extension_card (hh : h ≠ 0) :
    Fintype.card (Extension p h) = p ^ h := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card p h hh

theorem extension_finrank (hh : h ≠ 0) :
    Module.finrank (ZMod p) (Extension p h) = h :=
  GaloisField.finrank p hh

/-- Enumerate all nonzero extension elements, not an arbitrary selection. -/
def extensionNodes (hh : h ≠ 0) :
    Fin (p ^ h - 1) ≃ {x : Extension p h // x ≠ 0} := by
  classical
  apply (Fintype.equivFinOfCardEq _).symm
  rw [Fintype.card_subtype_compl]
  simp [extension_card p h hh]

/-- The evaluation map consists of pairwise distinct nonzero nodes. -/
def extensionNode (hh : h ≠ 0) (t : Fin (p ^ h - 1)) : Extension p h :=
  (extensionNodes p h hh t).val

theorem extensionNode_injective (hh : h ≠ 0) :
    Function.Injective (extensionNode p h hh) := by
  intro t s hts
  exact (extensionNodes p h hh).injective (Subtype.ext hts)

@[simp] theorem extensionNode_ne_zero (hh : h ≠ 0) (t : Fin (p ^ h - 1)) :
    extensionNode p h hh t ≠ 0 := (extensionNodes p h hh t).property

end Extension

/-- Concrete universal-block data to be furnished by the matrix construction.
The subspaces are over the base field; the row polynomials use the extension. -/
structure UniversalBlock (K E : Type*) [Field K] [Field E] [Algebra K E]
    (Q Δ R : ℕ) (node : Fin Q → E) where
  space : Fin Q → Bool → Submodule K (UniversalType Q Δ → K)
  supported : ∀ t g r, r ∈ space t g → ∀ u, u.head t ≠ g → r u = 0
  dimension : ∀ t g,
    7 * Fintype.card (Side (Δ := Δ) t g) ≤ 8 * Module.finrank K (space t g)
  row : UniversalType Q Δ → Fin Δ → UniversalType Q Δ → Polynomial E
  origin : ∀ u i y, (row u i y).eval 0 = (Pi.single u (1 : E) : UniversalType Q Δ → E) y
  degree : ∀ u i y, (row u i y).natDegree ≤ R
  annihilates : ∀ u i t r, r ∈ space t (u.slot i t) →
    (∑ y, (row u i y).eval (node t) * algebraMap K E (r y)) = 0

/-- The cardinality of either universal side is half of the block size,
expressed without division or a positivity side condition. -/
theorem twice_card_side {Q Δ : ℕ} (t : Fin Q) (g : Bool) :
    2 * Fintype.card (Side (Δ := Δ) t g) = Fintype.card (UniversalType Q Δ) := by
  have h := Fintype.card_congr (Types.fullSideEquiv (Δ := Δ) t g)
  simpa only [Fintype.card_prod, Fintype.card_bool] using h.symm

/-- Combining the universal-side estimate with three-quarter coverage gives
at least one quarter of the global coordinates in each free subspace. -/
theorem packed_dimension_lower {D N b s d : ℕ}
    (hside : 2 * s = N) (hdim : 7 * s ≤ 8 * d)
    (hcover : 3 * D ≤ 4 * (b * N)) :
    D ≤ 4 * (b * d) := by
  have hm := Nat.mul_le_mul_left b hdim
  nlinarith

section PolynomialRows

variable {U V E : Type*} [DecidableEq U] [DecidableEq V] [Field E]

/-- Embed one block row by zero outside that block. -/
def embeddedRow (e : U ↪ V) (P : U → Polynomial E) : V → Polynomial E :=
  Function.extend e P (fun _ => 0)

omit [DecidableEq U] [DecidableEq V] in
@[simp] theorem embeddedRow_apply (e : U ↪ V) (P : U → Polynomial E) (u : U) :
    embeddedRow e P (e u) = P u :=
  e.injective.extend_apply P (fun _ => 0) u

omit [DecidableEq U] [DecidableEq V] in
@[simp] theorem embeddedRow_outside (e : U ↪ V) (P : U → Polynomial E)
    (v : V) (hv : v ∉ Set.range e) : embeddedRow e P v = 0 :=
  Function.extend_apply' P (fun _ => 0) v hv

omit [DecidableEq U] [DecidableEq V] in
theorem embeddedRow_degree (e : U ↪ V) (P : U → Polynomial E) {R : ℕ}
    (hP : ∀ u, (P u).natDegree ≤ R) (v : V) :
    (embeddedRow e P v).natDegree ≤ R := by
  by_cases hv : v ∈ Set.range e
  · obtain ⟨u, rfl⟩ := hv
    simpa using hP u
  · simp [embeddedRow_outside e P v hv]

theorem embeddedRow_origin (e : U ↪ V) (P : U → Polynomial E) (u : U)
    (hP : ∀ w, (P w).eval 0 = if w = u then 1 else 0) (v : V) :
    (embeddedRow e P v).eval 0 = if v = e u then 1 else 0 := by
  by_cases hv : v ∈ Set.range e
  · obtain ⟨w, rfl⟩ := hv
    simp only [embeddedRow_apply, hP, e.injective.eq_iff]
  · have hne : v ≠ e u := by
      intro h
      exact hv ⟨u, h.symm⟩
    simp [embeddedRow_outside e P v hv, hne]

/-- One block of an injective packing. -/
def blockEmbedding {b : ℕ} (pack : Fin b × U ↪ V) (j : Fin b) : U ↪ V where
  toFun u := pack (j,u)
  inj' := fun _ _ h => congrArg Prod.snd (pack.injective h)

/-- Packed vertices use their block row; uncovered vertices use the constant
coordinate selector. The construction does not require entire factors in a block. -/
def assembledRow {b : ℕ} {I : Type*} (pack : Fin b × U ↪ V)
    (P : U → I → U → Polynomial E) (i : I) : V → V → Polynomial E :=
  Function.extend pack
    (fun z => embeddedRow (blockEmbedding pack z.1) (P z.2 i))
    (fun v w => Polynomial.C (if w = v then 1 else 0))

omit [DecidableEq U] in
@[simp] theorem assembledRow_apply {b : ℕ} {I : Type*} (pack : Fin b × U ↪ V)
    (P : U → I → U → Polynomial E) (i : I) (j : Fin b) (u : U) :
    assembledRow pack P i (pack (j,u)) =
      embeddedRow (blockEmbedding pack j) (P u i) :=
  pack.injective.extend_apply _ _ (j,u)

omit [DecidableEq U] in
@[simp] theorem assembledRow_outside {b : ℕ} {I : Type*} (pack : Fin b × U ↪ V)
    (P : U → I → U → Polynomial E) (i : I) (v : V) (hv : v ∉ Set.range pack) :
    assembledRow pack P i v = fun w => Polynomial.C (if w = v then 1 else 0) :=
  Function.extend_apply' _ _ v hv

theorem assembledRow_origin {b : ℕ} {I : Type*} (pack : Fin b × U ↪ V)
    (P : U → I → U → Polynomial E)
    (hP : ∀ u i w, (P u i w).eval 0 = if w = u then 1 else 0)
    (i : I) (v w : V) :
    (assembledRow pack P i v w).eval 0 = if w = v then 1 else 0 := by
  by_cases hv : v ∈ Set.range pack
  · obtain ⟨⟨j,u⟩, rfl⟩ := hv
    rw [assembledRow_apply]
    exact embeddedRow_origin (blockEmbedding pack j) (P u i) u (hP u i) w
  · by_cases hw : w = v <;> simp [assembledRow_outside pack P i v hv, hw]

omit [DecidableEq U] in
theorem assembledRow_degree {b : ℕ} {I : Type*} (pack : Fin b × U ↪ V)
    (P : U → I → U → Polynomial E) {R : ℕ}
    (hP : ∀ u i w, (P u i w).natDegree ≤ R) (i : I) (v w : V) :
    (assembledRow pack P i v w).natDegree ≤ R := by
  by_cases hv : v ∈ Set.range pack
  · obtain ⟨⟨j,u⟩, rfl⟩ := hv
    rw [assembledRow_apply]
    exact embeddedRow_degree (blockEmbedding pack j) (P u i) (hP u i) w
  · by_cases hw : w = v <;> simp [assembledRow_outside pack P i v hv, hw]

end PolynomialRows

section ConcreteUniversalBlock

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {Q Δ R : ℕ}

/-- Bundle the actual matrix, actual common fixed subspaces and actual
interpolated rows. The sole remaining local hypothesis is the explicit rank
bound for the concrete projector matrix. -/
def universalBlockOfRank (coeff : ℕ → K) (node : Fin Q → E)
    (hinj : Function.Injective node) (hne : ∀ t, node t ≠ 0)
    (hrank : ∀ (t : Fin Q) (g : Bool) (i : Fin Δ),
      8 * Δ * Module.finrank K (LinearMap.range
        (LinearMap.id - (MatrixSupport.jointMatrix i t g R coeff).mulVecLin)) ≤
          Fintype.card (Joint t g i)) : UniversalBlock K E Q Δ R node where
  space := Annihilation.universalSpace R coeff
  supported t g r hr := (Annihilation.mem_universalSpace R coeff t g r).mp hr |>.1
  dimension t g := SubspaceDimension.universalFixedSpace_seven_eighths t g
    (fun i => (MatrixSupport.jointMatrix i t g R coeff).mulVecLin) (hrank t g)
  row u i := Annihilation.universalRow (algebraMap K E) u i R coeff node hinj hne
  origin u i y := congrFun
    (Annihilation.universalRow_origin (algebraMap K E) u i R coeff node hinj hne) y
  degree u i y := Annihilation.universalRow_degree
    (algebraMap K E) u i R coeff node hinj hne y
  annihilates u i t r hr := Annihilation.universalRow_annihilates
    (algebraMap K E) u i R coeff node hinj hne t r hr

end ConcreteUniversalBlock

section Pairing

variable {K E U V : Type*} [Semiring K] [Field E]
variable [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

omit [Fintype V] [DecidableEq U] in
/-- Evaluating embedded polynomial coefficients is the same as embedding the
already evaluated row. -/
theorem embeddedRow_eval (e : U ↪ V) (P : U → Polynomial E) (z : E) :
    (fun v => (embeddedRow e P v).eval z) =
      DirectSums.extendLinear e (fun u => (P u).eval z) := by
  funext v
  by_cases hv : v ∈ Set.range e
  · obtain ⟨u, rfl⟩ := hv
    simp
  · rw [embeddedRow_outside e P v hv,
      DirectSums.extendLinear_zero_outside e _ v hv]
    simp

omit [DecidableEq U] in
/-- Pair a block polynomial row with an arbitrary full-coordinate vector. -/
theorem embeddedRow_pairing (e : U ↪ V) (P : U → Polynomial E) (z : E)
    (φ : K →+* E) (r : V → K) :
    (∑ v, (embeddedRow e P v).eval z * φ (r v)) =
      ∑ u, (P u).eval z * φ (r (e u)) := by
  have h := embeddedRow_eval e P z
  simp_rw [show ∀ v, (embeddedRow e P v).eval z =
    DirectSums.extendLinear e (fun u => (P u).eval z) v from congrFun h]
  exact DirectSums.sum_extendLinear_mul_hom e φ _ r

end Pairing

section GlobalAssembly

variable {p k Δ : ℕ} [Fact p.Prime]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F]
variable [Field E] [Fintype E] [Algebra (ZMod p) E]
variable [FiniteDimensional (ZMod p) E]

/-- Assemble every field of the genuine layout interface from a concrete
universal block and a compatible three-quarter packing. No global row-path,
annihilation, support or dimension condition is assumed. -/
def fromBlocks (P : Factor.Pattern V F) (c : LayoutSpec.Constants p k Δ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E c.Q Δ c.R (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ) (sigma : F → Word c.Q)
    (label : V → UniversalType c.Q Δ)
    (compatible : ∀ v (e : SlotAssignment.Incident P v),
      (label v).slot (slots v e) = sigma e.val)
    {b : ℕ} (blocks : BlockPacking.CompleteBlocks label b)
    (hcover : 3 * Fintype.card V ≤ 4 * (b * Fintype.card (UniversalType c.Q Δ))) :
    LayoutSpec.Layout (E := E) P c := by
  classical
  refine {
    bounded := hP
    size_ge := hsize
    extension_degree := hE
    nodes := nodes
    support := fun t g => DirectSums.packedSupportFinset blocks.embed
      (Types.side (Δ := Δ) t g).toFinset
    support_disjoint := ?_
    K := fun t g => DirectSums.packedSubspace blocks.embed (B.space t g)
    supported := ?_
    dimension_lower := ?_
    color := sigma
    row := fun e v => assembledRow blocks.embed B.row (slots v.val ⟨e,v.property⟩) v.val
    row_zero := ?_
    row_degree := ?_
    annihilation := ?_
  }
  · intro t
    apply DirectSums.packedSupportFinset_disjoint
    exact Set.disjoint_toFinset.mpr (Types.side_disjoint t)
  · intro t g r hr v hv
    apply DirectSums.packed_supported_finset blocks.embed (B.space t g)
      (Types.side (Δ := Δ) t g).toFinset _ hr v hv
    intro r hr u hu
    apply B.supported t g r hr u
    simpa only [Set.mem_toFinset, Types.mem_side] using hu
  · intro t g
    apply DirectSums.packed_quarter_dimension blocks.embed (B.space t g)
    · have hd := B.dimension t g
      have hs := twice_card_side (Δ := Δ) t g
      nlinarith
    · simpa only [Fintype.card_fin] using hcover
  · intro e v w
    apply assembledRow_origin
    intro u i y
    rw [B.origin]
    simp only [Pi.single_apply]
  · intro e v w
    exact assembledRow_degree blocks.embed B.row B.degree _ v.val w
  · intro t e v r hr
    let i := slots v.val ⟨e,v.property⟩
    change (∑ w, (assembledRow blocks.embed B.row i v.val w).eval (nodes t).val *
      algebraMap (ZMod p) E (r w)) = 0
    by_cases hv : v.val ∈ Set.range blocks.embed
    · obtain ⟨⟨j,u⟩, hju⟩ := hv
      have hcolor : u.slot i t = sigma e t := by
        have hh := congrFun (compatible v.val ⟨e,v.property⟩) t
        change (label v.val).slot i t = sigma e t at hh
        rw [← hju, blocks.type_eq j u] at hh
        exact hh
      have hrow : assembledRow blocks.embed B.row i v.val =
          embeddedRow (blockEmbedding blocks.embed j) (B.row u i) := by
        rw [← hju, assembledRow_apply]
      rw [hrow, embeddedRow_pairing]
      apply B.annihilates u i t
      change (fun u => r (blocks.embed (j,u))) ∈ B.space t (u.slot i t)
      rw [hcolor]
      exact DirectSums.packed_restriction_mem blocks.embed (B.space t (sigma e t)) hr j
    · rw [assembledRow_outside blocks.embed B.row i v.val hv]
      have hz := DirectSums.packed_zero_outside blocks.embed
        (B.space t (sigma e t)) hr v.val hv
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w = v.val <;> simp [hw, hz]

omit [Fintype E] [FiniteDimensional (ZMod p) E] in
/-- The balancing and packing steps require only bounded incidence and the
explicit fixed threshold. In particular no type-distribution assumption remains. -/
theorem exists_of_universalBlock (P : Factor.Pattern V F)
    (c : LayoutSpec.Constants p k Δ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : 16 * Fintype.card (UniversalType c.Q Δ) ^ 3 * (1 + Δ * k) ≤ c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E c.Q Δ c.R (fun t => (nodes t).val)) :
    Nonempty (LayoutSpec.Layout (E := E) P c) := by
  classical
  let slots := SlotAssignment.slotsOfBounded P hP
  obtain ⟨sigma, label, hcompatible, hdev⟩ :=
    TypeDistribution.exists_consistent_types_deviation_le (Q := c.Q) P slots hP
  have hN : 0 < Fintype.card (UniversalType c.Q Δ) := by
    rw [Types.card_universalType]
    positivity
  have hdev' : (∑ u : UniversalType c.Q Δ,
      ((BlockPacking.count label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType c.Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType c.Q Δ) : ℚ) *
        (1 + Δ * k : ℕ) * Fintype.card V := by
    simpa only [BlockPacking.count_eq_filter_card, Nat.cast_add, Nat.cast_one] using hdev
  obtain ⟨b, blocks, hcover⟩ :=
    BlockPacking.exists_completeBlocks_of_nat_threshold label (1 + Δ * k) hN
      (hthreshold.trans hsize) hdev'
  exact ⟨fromBlocks P c hP hsize hE nodes B slots sigma label hcompatible blocks
    (by simpa only [BlockPacking.CompleteBlocks.card_covered] using hcover)⟩

end GlobalAssembly

/-- A single finite construction is fixed before either the coordinate count
or the factor pattern varies. Its field is an actual finite Galois extension. -/
structure Construction (p k Δ : ℕ) [Fact p.Prime] where
  constants : LayoutSpec.Constants p k Δ
  threshold : 16 * Fintype.card (UniversalType constants.Q Δ) ^ 3 * (1 + Δ * k) ≤
    constants.Dstar
  nodes : Fin constants.Q ≃ {z : Extension p constants.h // z ≠ 0}
  block : UniversalBlock (ZMod p) (Extension p constants.h)
    constants.Q Δ constants.R (fun t => (nodes t).val)

namespace Construction

variable {p k Δ : ℕ} [Fact p.Prime]

/-- The same finite construction works for every sufficiently large bounded
pattern. The coordinate and factor index types are arbitrary finite types. -/
theorem layout_exists (C : Construction p k Δ)
    {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]
    (P : Factor.Pattern V F) (hP : P.Bounded k Δ)
    (hsize : C.constants.Dstar ≤ Fintype.card V) :
    Nonempty (LayoutSpec.Layout (E := Extension p C.constants.h) P C.constants) :=
  exists_of_universalBlock P C.constants hP hsize C.threshold
    (extension_finrank p C.constants.h (Nat.ne_of_gt C.constants.h_pos)) C.nodes C.block

end Construction

/-- Odd prime characteristic makes the normalization by two legitimate. -/
theorem two_ne_zero {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (2 : ZMod p) ≠ 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨a, ha⟩ := hodd
  have hlt : 2 < p := by omega
  intro hz
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- With numerical parameters fixed, the explicit concrete-matrix rank bound
completes the finite construction. All other block and global properties are
already theorems above. -/
def constructionOfParameters (p k Δ h Q R : ℕ) [Fact p.Prime]
    (hodd : Odd p) (hk : 0 < k) (hΔ : 0 < Δ) (hh : 0 < h)
    (hQ : Q = p ^ h - 1) (hdegree : Δ * k * (p - 1) * R < Q)
    (coeff : ℕ → ZMod p)
    (hrank : ∀ (t : Fin Q) (g : Bool) (i : Fin Δ),
      8 * Δ * Module.finrank (ZMod p) (LinearMap.range
        (LinearMap.id - (MatrixSupport.jointMatrix i t g R coeff).mulVecLin)) ≤
          Fintype.card (Joint t g i)) : Construction p k Δ := by
  let c : LayoutSpec.Constants p k Δ := {
    h := h
    Q := Q
    R := R
    Dstar := 16 * Fintype.card (UniversalType Q Δ) ^ 3 * (1 + Δ * k)
    p_odd := hodd
    k_pos := hk
    delta_pos := hΔ
    h_pos := hh
    Q_eq := hQ
    degree_budget := hdegree
  }
  let nodes : Fin Q ≃ {z : Extension p h // z ≠ 0} :=
    (Equiv.cast (congrArg Fin hQ)).trans (extensionNodes p h (Nat.ne_of_gt hh))
  exact {
    constants := c
    threshold := le_rfl
    nodes := nodes
    block := universalBlockOfRank coeff (fun t => (nodes t).val)
      (Subtype.val_injective.comp nodes.injective) (fun t => (nodes t).property) hrank
  }

/-- Unconditional existence of the complete finite interpolation gadget.
This combines finite-field construction, binomial interpolation, the actual
matrix spectrum and its integer tail bound. No layout or rank assumption remains. -/
theorem exists_construction (p k Δ : ℕ) [Fact p.Prime]
    (hodd : Odd p) (hk : 0 < k) (hΔ : 0 < Δ) : Nonempty (Construction p k Δ) := by
  obtain ⟨h,Q,R,A,hh,hQ,_hR,_hR32,_hAR,htail,hdegree⟩ :=
    LayoutParameters.exists_layout_parameters p k Δ (Fact.out : p.Prime).one_lt hk hΔ
  let coeff : ℕ → ZMod p := BinomialInterpolation.extendCoefficients
    (BinomialInterpolation.parityCoefficients (K := ZMod p) A R)
  refine ⟨constructionOfParameters p k Δ h Q R hodd hk hΔ hh hQ hdegree coeff ?_⟩
  intro t g i
  exact SpectralRank.jointMatrix_parity_rank_bound (two_ne_zero hodd) t g i A R htail

/-- Mathematical existence part of Lemma 3.1, with the quantifier order explicit:
constants are fixed before D, the number of factors, or any bounded pattern.

This theorem asserts the full finite layout properties. A polynomial bit-time
implementation of this construction is a separate, unproved obligation. -/
theorem interpolation_layout_exists (p k Δ : ℕ) [Fact p.Prime]
    (hodd : Odd p) (hk : 0 < k) (hΔ : 0 < Δ) :
    ∃ c : LayoutSpec.Constants p k Δ,
      ∀ (D m : ℕ) (P : Factor.Pattern (Fin D) (Fin m)),
        P.Bounded k Δ → c.Dstar ≤ D →
          Nonempty (LayoutSpec.Layout (E := Extension p c.h) P c) := by
  obtain ⟨C⟩ := exists_construction p k Δ hodd hk hΔ
  refine ⟨C.constants, ?_⟩
  intro D m P hP hsize
  exact C.layout_exists P hP (by simpa only [Fintype.card_fin] using hsize)

section ComputedAssignmentBridge

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {Q Δ k : ℕ}

/-- The actual local-expectation program supplies the type labels for the
packing theorem. No finite-averaging choice of an assignment is used here.
The packing itself is still supplied by its proved finite existence theorem. -/
theorem exists_blocks_for_computedAssignment (P : Factor.Pattern V F)
    (slots : SlotAssignment.SlotMap P Δ) (hP : P.Bounded k Δ)
    (a : Word Q) (tail : List (Word Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (TypeDistribution.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices)
    (hlarge : 16 * Fintype.card (UniversalType Q Δ) ^ 3 * (1 + Δ * k) ≤
      Fintype.card V) :
    let label := TypeDistribution.assignmentType P slots
      (LocalExpectation.computedAssignment P slots a tail vertices indices)
    ∃ b, ∃ _blocks : BlockPacking.CompleteBlocks label b,
      3 * Fintype.card V ≤ 4 * (b * Fintype.card (UniversalType Q Δ)) := by
  dsimp only
  let label := TypeDistribution.assignmentType P slots
    (LocalExpectation.computedAssignment P slots a tail vertices indices)
  have hdev := LocalExpectation.computedAssignment_deviation_le P slots a tail
    haNodup haFull vertices hvNodup hvFull indices hiNodup hiFull hP
  have hdev' : (∑ u : UniversalType Q Δ,
      ((BlockPacking.count label u : ℚ) -
        (Fintype.card V : ℚ) / Fintype.card (UniversalType Q Δ)) ^ 2) ≤
      (Fintype.card (UniversalType Q Δ) : ℚ) * (1 + Δ * k : ℕ) * Fintype.card V := by
    simpa only [LocalExpectation.pairObjective, Variance.typeCount,
      BlockPacking.count_eq_filter_card, Nat.cast_add, Nat.cast_one, label] using hdev
  have hN : 0 < Fintype.card (UniversalType Q Δ) := by
    rw [Types.card_universalType]
    positivity
  obtain ⟨b, blocks, hcover⟩ := BlockPacking.exists_completeBlocks_of_nat_threshold
    label (1 + Δ * k) hN hlarge hdev'
  exact ⟨b, blocks, by simpa only [BlockPacking.CompleteBlocks.card_covered] using hcover⟩

variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [Algebra (ZMod p) E]
variable [FiniteDimensional (ZMod p) E]

omit [Fintype E] [FiniteDimensional (ZMod p) E] in
/-- Replace the abstract assignment-existence step in the layout construction
by the exact output of the executable local conditional-expectation program.
The returned layout's factor words are that program's output, propositionally,
not merely some other assignment with a matching deviation bound.

This does not claim the rest of the layout has an executable representation:
block enumeration and the finite-field/basis data remain separate obligations. -/
theorem exists_layout_with_computed_words (P : Factor.Pattern V F)
    (c : LayoutSpec.Constants p k Δ) (hP : P.Bounded k Δ)
    (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : 16 * Fintype.card (UniversalType c.Q Δ) ^ 3 * (1 + Δ * k) ≤ c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (B : UniversalBlock (ZMod p) E c.Q Δ c.R (fun t => (nodes t).val))
    (slots : SlotAssignment.SlotMap P Δ)
    (a : Word c.Q) (tail : List (Word c.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (TypeDistribution.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices) :
    ∃ L : LayoutSpec.Layout (E := E) P c,
      L.color = fun e => LocalExpectation.computedAssignment
        P slots a tail vertices indices (.inl e) := by
  let omega := LocalExpectation.computedAssignment P slots a tail vertices indices
  let label := TypeDistribution.assignmentType P slots omega
  let sigma := fun e => omega (.inl e)
  have hcompatible : ∀ v (e : SlotAssignment.Incident P v),
      (label v).slot (slots v e) = sigma e.val := by
    intro v e
    exact LocalExpectation.computedAssignment_consistent
      P slots a tail vertices indices v e
  obtain ⟨b, blocks, hcover⟩ := exists_blocks_for_computedAssignment P slots hP
    a tail haNodup haFull vertices hvNodup hvFull indices hiNodup hiFull
    (hthreshold.trans hsize)
  exact ⟨fromBlocks P c hP hsize hE nodes B slots sigma label hcompatible blocks hcover, rfl⟩

/-- The unconditional finite construction also accepts the program's specific
word assignment. Only the explicit executable-input representations are supplied. -/
theorem Construction.layout_exists_computed (C : Construction p k Δ)
    (P : Factor.Pattern V F) (hP : P.Bounded k Δ)
    (hsize : C.constants.Dstar ≤ Fintype.card V)
    (slots : SlotAssignment.SlotMap P Δ)
    (a : Word C.constants.Q) (tail : List (Word C.constants.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (TypeDistribution.SeedIndex V F Δ))
    (hiNodup : indices.Nodup) (hiFull : ∀ i, i ∈ indices) :
    ∃ L : LayoutSpec.Layout (E := Extension p C.constants.h) P C.constants,
      L.color = fun e => LocalExpectation.computedAssignment
        P slots a tail vertices indices (.inl e) :=
  exists_layout_with_computed_words P C.constants hP hsize C.threshold
    (extension_finrank p C.constants.h (Nat.ne_of_gt C.constants.h_pos)) C.nodes C.block
    slots a tail haNodup haFull vertices hvNodup hvFull indices hiNodup hiFull

end ComputedAssignmentBridge

end SubexponentialSAT.Layout

end

end OAI.Algorithms
