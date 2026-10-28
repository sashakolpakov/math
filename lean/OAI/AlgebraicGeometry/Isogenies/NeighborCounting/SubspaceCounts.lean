import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Components

/-! # Subspace Counts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

noncomputable section

/-!
NeighborCounting: finite-subspace counting core and component-specialization bridge.

This file proves the graph/product parametrization and all three counting
formulas without assuming fiber cardinalities. NativeNeighbors now
defines actual quotient-sheaf neighbors and proves their reduction formula
using FrobeniusKernel's native quotient base-change constructors. GenericParameters
computes the generic scheme-map images, proving the enumeration from their
coordinate formulas; KernelProperties proves finite flatness and closed
immersion; PELAdapter places these kernels in the native integral PEL
abelian family. No committed statement stub is imported.

The diagnostic at the end remains deliberately about an unconnected raw
multiset; it is not a counterexample to the manuscript or the new native
construction. The full polarized, marked C0/opposite-block comparison is
not claimed by this counting core or the split-block quotient bridge.

Input accounting: h_HenselianLifting and h_SchematicClosure are explicit in Components, and
h_FrobeniusKernel supplies mixed-term order below. The native helpers also use proved
Homomorphisms Frobenius infrastructure to kill etale-to-multiplicative characters.
They do not infer a quotient equality from commutation alone.
-/

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The distinguished one-dimensional identity-part direction. -/
def identityLine : Submodule F (V × F) :=
  LinearMap.ker (LinearMap.fst F V F)

/-- Generic subspaces with fixed quotient image, disjoint from the identity line. -/
def DisjointLift (U : Submodule F V) :=
  {L : Submodule F (V × F) //
    Disjoint L identityLine ∧ L.map (LinearMap.fst F V F) = U}

/-- Generic subspaces with fixed quotient image, containing the identity line. -/
def ContainingLift (U : Submodule F V) :=
  {L : Submodule F (V × F) //
    identityLine ≤ L ∧ L.map (LinearMap.fst F V F) = U}

def fiberGraph (U : Submodule F V) (f : U →ₗ[F] F) : Submodule F (V × F) :=
  LinearMap.range (U.subtype.prod f)

lemma fiberGraph_disjoint (U : Submodule F V) (f : U →ₗ[F] F) :
    Disjoint (fiberGraph U f) identityLine := by
  apply Submodule.disjoint_def.mpr
  intro z hz hzero
  obtain ⟨u, rfl⟩ := hz
  have hu : (u : V) = 0 := hzero
  have hu' : u = 0 := Subtype.ext hu
  simp [hu']

lemma fiberGraph_image (U : Submodule F V) (f : U →ₗ[F] F) :
    (fiberGraph U f).map (LinearMap.fst F V F) = U := by
  ext v
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
    exact u.property
  · intro hv
    exact ⟨(v, f ⟨v, hv⟩), ⟨⟨v, hv⟩, rfl⟩, rfl⟩

def graphLift (U : Submodule F V) (f : U →ₗ[F] F) : DisjointLift U :=
  ⟨fiberGraph U f, fiberGraph_disjoint U f, fiberGraph_image U f⟩

lemma graphLift_injective (U : Submodule F V) : Function.Injective (graphLift U) := by
  intro f g h
  have heq : fiberGraph U f = fiberGraph U g := congrArg Subtype.val h
  ext u
  have hmem : ((u : V), f u) ∈ fiberGraph U g := heq ▸ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  have hvu : v = u := Subtype.ext (congrArg Prod.fst hv)
  simpa [hvu] using (congrArg Prod.snd hv).symm

def liftProjection (U : Submodule F V) (L : DisjointLift U) : L.val →ₗ[F] U :=
  ((LinearMap.fst F V F).comp L.val.subtype).codRestrict U fun z => by
    change z.val.1 ∈ U
    have hmem : z.val.1 ∈ L.val.map (LinearMap.fst F V F) :=
      ⟨z.val, z.property, rfl⟩
    simpa only [L.property.2] using hmem

lemma liftProjection_bijective (U : Submodule F V) (L : DisjointLift U) :
    Function.Bijective (liftProjection U L) := by
  constructor
  · intro a b h
    have hab : a.val.1 = b.val.1 := congrArg Subtype.val h
    have hz : a.val - b.val ∈ L.val ⊓ identityLine :=
      ⟨L.val.sub_mem a.property b.property, sub_eq_zero.mpr hab⟩
    have hzero : a.val - b.val = 0 :=
      Submodule.disjoint_def.mp L.property.1 _ hz.1 hz.2
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · intro u
    have hu : (u : V) ∈ L.val.map (LinearMap.fst F V F) :=
      L.property.2.symm ▸ u.property
    obtain ⟨z, hz, hzu⟩ := hu
    exact ⟨⟨z, hz⟩, Subtype.ext hzu⟩

lemma graphLift_surjective (U : Submodule F V) : Function.Surjective (graphLift U) := by
  intro L
  let e := LinearEquiv.ofBijective (liftProjection U L) (liftProjection_bijective U L)
  let f : U →ₗ[F] F := ((LinearMap.snd F V F).comp L.val.subtype).comp e.symm.toLinearMap
  refine ⟨f, Subtype.ext ?_⟩
  apply le_antisymm
  · rintro z ⟨u, rfl⟩
    have he : ((e.symm u : L.val) : V × F).1 = (u : V) :=
      congrArg Subtype.val (e.apply_symm_apply u)
    have hz : (U.subtype.prod f) u = (e.symm u : V × F) :=
      Prod.ext he.symm rfl
    rw [hz]
    exact (e.symm u).property
  · intro z hz
    refine ⟨e ⟨z, hz⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change ((e.symm (e ⟨z, hz⟩) : L.val) : V × F).2 = z.2
      rw [e.symm_apply_apply]

/-- Every disjoint lift is a unique graph; the parametrization is proved. -/
def disjointLiftEquiv (U : Submodule F V) : (U →ₗ[F] F) ≃ DisjointLift U :=
  Equiv.ofBijective (graphLift U) ⟨graphLift_injective U, graphLift_surjective U⟩

theorem disjointLift_card (U : Submodule F V) [Module.Finite F U] :
    Nat.card (DisjointLift U) = Nat.card F ^ Module.finrank F U := by
  rw [← Nat.card_congr (disjointLiftEquiv U), Module.natCard_eq_pow_finrank (K := F)]
  simp

lemma containingLift_eq_preimage (U : Submodule F V) (L : ContainingLift U) :
    L.val = U.comap (LinearMap.fst F V F) := by
  apply le_antisymm
  · intro z hz
    show z.1 ∈ U
    rw [← L.property.2]
    exact ⟨z, hz, rfl⟩
  · intro z hz
    have hz' : z.1 ∈ L.val.map (LinearMap.fst F V F) :=
      L.property.2.symm ▸ hz
    obtain ⟨w, hw, hwz⟩ := hz'
    have hdiff : z - w ∈ identityLine := sub_eq_zero.mpr hwz.symm
    have hsum := L.val.add_mem (L.property.1 hdiff) hw
    simpa using hsum

instance containingLift_unique (U : Submodule F V) : Unique (ContainingLift U) where
  default := ⟨U.comap (LinearMap.fst F V F),
    LinearMap.ker_le_comap _,
    Submodule.map_comap_eq_of_surjective (fun v => ⟨(v, 0), rfl⟩) U⟩
  uniq L := Subtype.ext (containingLift_eq_preimage U L)

theorem containingLift_card (U : Submodule F V) : Nat.card (ContainingLift U) = 1 := by
  simp

lemma disjointLift_finrank (U : Submodule F V) (L : DisjointLift U) :
    Module.finrank F L.val = Module.finrank F U :=
  (LinearEquiv.ofBijective (liftProjection U L) (liftProjection_bijective U L)).finrank_eq

def preimageEquiv (U : Submodule F V) :
    U.comap (LinearMap.fst F V F) ≃ₗ[F] U × F where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma containingLift_finrank (U : Submodule F V) [Module.Finite F U]
    (L : ContainingLift U) :
    Module.finrank F L.val = Module.finrank F U + 1 := by
  rw [containingLift_eq_preimage U L, (preimageEquiv U).finrank_eq]
  simp

/-- A one-dimensional identity part meets a subspace in zero or in the entire line. -/
theorem identityLine_dichotomy (L : Submodule F (V × F)) :
    Disjoint L identityLine ∨ identityLine ≤ L := by
  by_cases h : ((0 : V), (1 : F)) ∈ L
  · right
    rintro ⟨v, c⟩ hz
    have hv : v = 0 := hz
    subst v
    simpa using L.smul_mem c h
  · left
    apply Submodule.disjoint_def.mpr
    rintro ⟨v, c⟩ hz hz'
    have hv : v = 0 := hz'
    subst v
    by_cases hc : c = 0
    · exact Prod.ext rfl hc
    · have hmem := L.smul_mem c⁻¹ hz
      have hunit : ((0 : V), (1 : F)) ∈ L := by
        simpa [hc] using hmem
      exact (h hunit).elim

theorem line_cases [Module.Finite F V] (L : Submodule F (V × F))
    (hdim : Module.finrank F L = 1) :
    L = identityLine ∨
      (Disjoint L identityLine ∧ Module.finrank F (L.map (LinearMap.fst F V F)) = 1) := by
  rcases identityLine_dichotomy L with hd | hc
  · right
    exact ⟨hd, (disjointLift_finrank _ ⟨L, hd, rfl⟩).symm.trans hdim⟩
  · left
    have hr : Module.finrank F L =
        Module.finrank F (L.map (LinearMap.fst F V F)) + 1 :=
      containingLift_finrank _ ⟨L, hc, rfl⟩
    have hz : Module.finrank F (L.map (LinearMap.fst F V F)) = 0 := by omega
    have hb : L.map (LinearMap.fst F V F) = ⊥ := Submodule.finrank_eq_zero.mp hz
    have heq := containingLift_eq_preimage _ ⟨L, hc, rfl⟩
    simpa [hb, identityLine] using heq

theorem plane_cases [Module.Finite F V] (hV : Module.finrank F V = 2)
    (L : Submodule F (V × F)) (hdim : Module.finrank F L = 2) :
    (identityLine ≤ L ∧ Module.finrank F (L.map (LinearMap.fst F V F)) = 1) ∨
    (Disjoint L identityLine ∧ L.map (LinearMap.fst F V F) = ⊤) := by
  rcases identityLine_dichotomy L with hd | hc
  · right
    refine ⟨hd, Submodule.eq_top_of_finrank_eq ?_⟩
    exact (disjointLift_finrank _ ⟨L, hd, rfl⟩).symm.trans (hdim.trans hV.symm)
  · left
    have hr : Module.finrank F L =
        Module.finrank F (L.map (LinearMap.fst F V F)) + 1 :=
      containingLift_finrank _ ⟨L, hc, rfl⟩
    exact ⟨hc, by omega⟩

theorem full_kernel_unique [Module.Finite F V] (hV : Module.finrank F V = 2)
    (L : Submodule F (V × F)) (hdim : Module.finrank F L = 3) : L = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa [hV] using hdim

/-- The two nontrivial coefficients of NeighborCounting, before the geometric bridge. -/
theorem line_and_plane_lift_counts
    (q : ℕ) (hcard : Nat.card F = q)
    (U₁ U₂ : Submodule F V) [Module.Finite F U₁] [Module.Finite F U₂]
    (h₁ : Module.finrank F U₁ = 1) (h₂ : Module.finrank F U₂ = 2) :
    Nat.card (DisjointLift U₁) = q ∧
    Nat.card (DisjointLift U₂) = q ^ 2 ∧
    Nat.card (ContainingLift U₁) = 1 ∧
    Nat.card (ContainingLift U₂) = 1 := by
  simp [disjointLift_card, hcard, h₁, h₂]

lemma identityLine_not_le_of_disjoint (L : Submodule F (V × F))
    (h : Disjoint L identityLine) : ¬identityLine ≤ L := by
  intro hc
  have hz : ((0 : V), (1 : F)) = 0 :=
    Submodule.disjoint_def.mp h _ (hc (by rfl)) (by rfl)
  exact one_ne_zero (congrArg Prod.snd hz)

abbrev LiftData (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  Σ U : Submodule F V, DisjointLift U ⊕ ContainingLift U

def liftForget : LiftData F V → Submodule F (V × F)
  | ⟨_, Sum.inl L⟩ => L.val
  | ⟨_, Sum.inr L⟩ => L.val

lemma liftForget_injective : Function.Injective (liftForget (F := F) (V := V)) := by
  rintro ⟨U, L | L⟩ ⟨W, M | M⟩ h
  · have hUW : U = W := L.property.2.symm.trans
      ((congrArg (Submodule.map (LinearMap.fst F V F)) h).trans M.property.2)
    subst W
    exact congrArg (fun N : DisjointLift U => (⟨U, Sum.inl N⟩ : LiftData F V))
      (Subtype.ext h)
  · change L.val = M.val at h
    exact (identityLine_not_le_of_disjoint L.val L.property.1
      (h.symm ▸ M.property.1)).elim
  · change L.val = M.val at h
    exact (identityLine_not_le_of_disjoint M.val M.property.1
      (h ▸ L.property.1)).elim
  · have hUW : U = W := L.property.2.symm.trans
      ((congrArg (Submodule.map (LinearMap.fst F V F)) h).trans M.property.2)
    subst W
    exact congrArg (fun N : ContainingLift U => (⟨U, Sum.inr N⟩ : LiftData F V))
      (Subtype.ext h)

lemma liftForget_surjective : Function.Surjective (liftForget (F := F) (V := V)) := by
  intro L
  rcases identityLine_dichotomy L with hd | hc
  · exact ⟨⟨L.map (LinearMap.fst F V F), Sum.inl ⟨L, hd, rfl⟩⟩, rfl⟩
  · exact ⟨⟨L.map (LinearMap.fst F V F), Sum.inr ⟨L, hc, rfl⟩⟩, rfl⟩

/-- Exhaustive classification, not merely a count of a chosen family of graphs. -/
def allSubspacesEquiv : LiftData F V ≃ Submodule F (V × F) :=
  Equiv.ofBijective liftForget ⟨liftForget_injective, liftForget_surjective⟩

section Finite

variable [Fintype F] [Fintype V]

local instance submoduleFintype : Fintype (Submodule F V) := Fintype.ofFinite _
local instance productSubmoduleFintype : Fintype (Submodule F (V × F)) := Fintype.ofFinite _
local instance disjointLiftFintype (U : Submodule F V) : Fintype (DisjointLift U) := by
  classical
  exact inferInstanceAs (Fintype {L : Submodule F (V × F) //
    Disjoint L identityLine ∧ L.map (LinearMap.fst F V F) = U})
local instance containingLiftFintype (U : Submodule F V) : Fintype (ContainingLift U) :=
  Fintype.ofFinite _
local instance liftDataFintype : Fintype (LiftData F V) :=
  inferInstanceAs (Fintype (Σ U : Submodule F V, DisjointLift U ⊕ ContainingLift U))

variable {A : Type*} [AddCommMonoid A]

/-- The image and connected-part flag define the special subgroup label. -/
def labeledReduction (i : ℕ) (R : Submodule F V → Bool → A) : A := by
  classical
  exact ∑ L : Submodule F (V × F),
    if Module.finrank F L = i then
      R (L.map (LinearMap.fst F V F)) (decide (identityLine ≤ L)) else 0

/-- General multiplicity formula, with no fiber cardinalities assumed. -/
theorem labeledReduction_eq (i : ℕ) (R : Submodule F V → Bool → A) :
    labeledReduction i R =
      ∑ U : Submodule F V,
        ((if Module.finrank F U = i then
          (Nat.card F ^ Module.finrank F U) • R U false else 0) +
         (if Module.finrank F U + 1 = i then R U true else 0)) := by
  classical
  unfold labeledReduction
  rw [← (allSubspacesEquiv (F := F) (V := V)).sum_comp]
  change (∑ d : (Σ U : Submodule F V, DisjointLift U ⊕ ContainingLift U),
    if Module.finrank F (liftForget d) = i then
      R ((liftForget d).map (LinearMap.fst F V F))
        (decide (identityLine ≤ liftForget d)) else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro U _
  rw [Fintype.sum_sum_type]
  change
    (∑ L : DisjointLift U,
      if Module.finrank F L.val = i then
        R (L.val.map (LinearMap.fst F V F)) (decide (identityLine ≤ L.val)) else 0) +
    (∑ L : ContainingLift U,
      if Module.finrank F L.val = i then
        R (L.val.map (LinearMap.fst F V F)) (decide (identityLine ≤ L.val)) else 0) = _
  have hd : ∀ L : DisjointLift U,
      (if Module.finrank F L.val = i then
        R (L.val.map (LinearMap.fst F V F)) (decide (identityLine ≤ L.val)) else 0) =
      (if Module.finrank F U = i then R U false else 0) := by
    intro L
    simp only [disjointLift_finrank U L, L.property.2,
      decide_eq_false (identityLine_not_le_of_disjoint _ L.property.1)]
  have hc : ∀ L : ContainingLift U,
      (if Module.finrank F L.val = i then
        R (L.val.map (LinearMap.fst F V F)) (decide (identityLine ≤ L.val)) else 0) =
      (if Module.finrank F U + 1 = i then R U true else 0) := by
    intro L
    simp only [containingLift_finrank U L, L.property.2, decide_eq_true L.property.1]
  simp_rw [hd, hc]
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, disjointLift_card, containingLift_card, one_nsmul]
  split_ifs <;> simp

theorem labeledReduction_one (R : Submodule F V → Bool → A) :
    labeledReduction 1 R = R ⊥ true +
      Nat.card F • ∑ U : Submodule F V,
        if Module.finrank F U = 1 then R U false else 0 := by
  classical
  rw [labeledReduction_eq, Finset.sum_add_distrib]
  have hleft :
      (∑ U : Submodule F V, if Module.finrank F U = 1 then
        Nat.card F ^ Module.finrank F U • R U false else 0) =
      Nat.card F • ∑ U : Submodule F V,
        if Module.finrank F U = 1 then R U false else 0 := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro U _
    by_cases h : Module.finrank F U = 1 <;> simp [h]
  have hright :
      (∑ U : Submodule F V, if Module.finrank F U + 1 = 1 then R U true else 0) =
      R ⊥ true := by
    simp [Submodule.finrank_eq_zero]
  rw [hleft, hright, add_comm]

omit [Fintype F] in
lemma quotient_full_rank_iff (hV : Module.finrank F V = 2) (U : Submodule F V) :
    Module.finrank F U = 2 ↔ U = ⊤ := by
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans hV.symm)
  · rintro rfl
    simpa using hV

theorem labeledReduction_two (hV : Module.finrank F V = 2)
    (R : Submodule F V → Bool → A) :
    labeledReduction 2 R =
      (∑ U : Submodule F V, if Module.finrank F U = 1 then R U true else 0) +
      (Nat.card F ^ 2) • R ⊤ false := by
  classical
  rw [labeledReduction_eq, Finset.sum_add_distrib]
  have hleft :
      (∑ U : Submodule F V, if Module.finrank F U = 2 then
        Nat.card F ^ Module.finrank F U • R U false else 0) =
      Nat.card F ^ 2 • R ⊤ false := by
    simp [quotient_full_rank_iff hV, hV]
  have hright :
      (∑ U : Submodule F V, if Module.finrank F U + 1 = 2 then R U true else 0) =
      ∑ U : Submodule F V, if Module.finrank F U = 1 then R U true else 0 := by
    apply Finset.sum_congr rfl
    intro U _
    have h : Module.finrank F U + 1 = 2 ↔ Module.finrank F U = 1 := by omega
    simp only [h]
  rw [hleft, hright, add_comm]

theorem labeledReduction_three (hV : Module.finrank F V = 2)
    (R : Submodule F V → Bool → A) : labeledReduction 3 R = R ⊤ true := by
  classical
  rw [labeledReduction_eq, Finset.sum_add_distrib]
  have hleft :
      (∑ U : Submodule F V, if Module.finrank F U = 3 then
        Nat.card F ^ Module.finrank F U • R U false else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro U _
    have hle : Module.finrank F U ≤ 2 := U.finrank_le.trans_eq hV
    simp [show Module.finrank F U ≠ 3 by omega]
  have hright :
      (∑ U : Submodule F V, if Module.finrank F U + 1 = 3 then R U true else 0) =
      R ⊤ true := by
    have h : ∀ U : Submodule F V,
        Module.finrank F U + 1 = 3 ↔ U = ⊤ := by
      intro U
      rw [← quotient_full_rank_iff hV]
      omega
    simp [h]
  rw [hleft, hright, zero_add]

end Finite

/-- The commutation part of FrobeniusKernel puts both mixed terms in the target's order. -/
theorem mixed_term_order_of_FrobeniusKernel
    {P : Type*} (X Z : P → P) (Y : P → Multiset P)
    (h_FrobeniusKernel :
      (∀ x, (Y x).map X = Y (X x)) ∧
      (∀ x, X (Z x) = Z (X x))) (x : P) :
    (Y x).map X = Y (X x) ∧
      ({X (Z x)} : Multiset P) = {Z (X x)} := by
  exact ⟨h_FrobeniusKernel.1 x, congrArg (fun p => ({p} : Multiset P)) (h_FrobeniusKernel.2 x)⟩

/-- An interface counterexample: even all operator commutation identities and
the correct number of etale lines leave a separately supplied raw multiset
unconstrained. This does not refute the manuscript's geometric construction. -/
theorem raw_neighbors_not_determined_by_operator_identities (q : ℕ) :
    ∃ (X Z : Unit → Unit) (Y : Unit → Multiset Unit)
      (raw : Unit → ℕ → Multiset Unit),
      (∀ x, (Y x).map X = Y (X x)) ∧
      (∀ x, X (Z x) = Z (X x)) ∧
      (∀ x, (Y x).card = q + 1) ∧
      raw () 1 ≠ ({X ()} : Multiset Unit) + q • Y () := by
  refine ⟨id, id, fun _ => Multiset.replicate (q + 1) (), fun _ _ => 0,
    ?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl
  · intro x
    exact Multiset.card_replicate _ _
  · intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_zero, Multiset.card_add, Multiset.card_singleton,
      Multiset.card_nsmul, Multiset.card_replicate] at hc
    omega

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
