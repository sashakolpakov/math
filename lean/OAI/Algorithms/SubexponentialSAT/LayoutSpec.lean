import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Factor
import OAI.Algorithms.SubexponentialSAT.CosetInvariance
import OAI.Algorithms.SubexponentialSAT.CosetCardinality

namespace OAI.Algorithms

/-!
# The exact interpolation-layout interface

This module states the finite mathematical output of Lemma 3.1.  It does not
assert existence of a layout, construct its universal block, or claim a running
time.  Constants are independent of the coordinate and factor index types.

Rows are indexed by **incidences** `(e,v)`, not just by coordinates `v`.
The subspaces are over `ZMod p`; row coefficients and interpolation nodes are
over a possibly larger finite extension field.
-/

namespace SubexponentialSAT.LayoutSpec

open scoped BigOperators

/-- The fixed numerical parameters in Lemma 3.1, before the input size varies.
Primality is a typeclass hypothesis on layouts; oddness and the positive
combinatorial bounds are recorded here. -/
structure Constants (p k Δ : ℕ) where
  h : ℕ
  Q : ℕ
  R : ℕ
  Dstar : ℕ
  p_odd : Odd p
  k_pos : 0 < k
  delta_pos : 0 < Δ
  h_pos : 0 < h
  Q_eq : Q = p ^ h - 1
  degree_budget : Δ * k * (p - 1) * R < Q

namespace Constants

theorem Q_pos {p k Δ : ℕ} (c : Constants p k Δ) : 0 < c.Q :=
  lt_of_le_of_lt (Nat.zero_le _) c.degree_budget

end Constants

/-- A surjective residue map lifts a polynomial without increasing its degree,
while permitting a prescribed lift of its constant coefficient. -/
theorem exists_polynomial_lift {A B : Type*} [CommRing A] [CommRing B]
    (ρ : A →+* B) (hρ : Function.Surjective ρ) (f : Polynomial B)
    (a : A) (ha : ρ a = f.eval 0) :
    ∃ q : Polynomial A, q.map ρ = f ∧ q.eval 0 = a ∧ q.natDegree ≤ f.natDegree := by
  have hf : f ∈ Polynomial.lifts ρ :=
    (Polynomial.mem_lifts f).mpr (Polynomial.map_surjective ρ hρ f)
  obtain ⟨q, hq, hd⟩ := Polynomial.exists_degree_eq_of_mem_lifts hf
  have heval : ρ (q.eval 0) = f.eval 0 := by
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, hq, map_zero]
  refine ⟨q + Polynomial.C (a - q.eval 0), ?_, ?_, ?_⟩
  · simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, hq, map_sub, heval, ha,
      sub_self, add_zero]
  · rw [Polynomial.eval_add, Polynomial.eval_C, add_comm, sub_add_cancel]
  · exact Polynomial.natDegree_add_le_of_degree_le
      (le_of_eq (Polynomial.natDegree_eq_of_degree_eq hd)) (by simp)

section Layout

variable {p k Δ : ℕ} [Fact p.Prime]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F]
variable [Field E] [Algebra (ZMod p) E]

/-- The finite output of the layout lemma for a bounded factor pattern.
`dimension_lower` is `dim K >= D/4` with denominators cleared; natural-number
division would incorrectly weaken that requirement when `4` does not divide D.
The nonzero-node equivalence records both distinctness and completeness. -/
structure Layout (P : Factor.Pattern V F) (c : Constants p k Δ) where
  bounded : P.Bounded k Δ
  size_ge : c.Dstar ≤ Fintype.card V
  extension_degree : Module.finrank (ZMod p) E = c.h
  nodes : Fin c.Q ≃ {z : E // z ≠ 0}
  support : Fin c.Q → Bool → Finset V
  support_disjoint : ∀ t, Disjoint (support t false) (support t true)
  K : Fin c.Q → Bool → Submodule (ZMod p) (V → ZMod p)
  supported : ∀ t g r, r ∈ K t g → ∀ v, v ∉ support t g → r v = 0
  dimension_lower : ∀ t g, Fintype.card V ≤ 4 * Module.finrank (ZMod p) (K t g)
  color : F → Fin c.Q → Bool
  row : (e : F) → {v // v ∈ P.scope e} → V → Polynomial E
  row_zero : ∀ e v w, (row e v w).eval 0 = if w = v.val then 1 else 0
  row_degree : ∀ e v w, (row e v w).natDegree ≤ c.R
  annihilation : ∀ t e v r, r ∈ K t (color e t) →
    ∑ w, (row e v w).eval (nodes t).val * algebraMap (ZMod p) E (r w) = 0

namespace Layout

variable {P : Factor.Pattern V F} {c : Constants p k Δ}
variable (L : Layout (E := E) P c)

/-- Adding zero to the node enumeration enumerates the entire extension field. -/
noncomputable def fieldEquiv : Option (Fin c.Q) ≃ E := by
  classical
  exact (Equiv.optionCongr L.nodes).trans (Equiv.optionSubtypeNe 0)

/-- The output specification itself implies finiteness of the extension field;
an additional finite-field hypothesis is not silently required. -/
@[instance_reducible] noncomputable def fieldFintype : Fintype E :=
  Fintype.ofEquiv (Option (Fin c.Q)) L.fieldEquiv

include L in
theorem natCard_field : Nat.card E = c.Q + 1 := by
  rw [← Nat.card_congr L.fieldEquiv]
  simp

include L in
theorem natCard_field_eq_pow : Nat.card E = p ^ c.h := by
  rw [L.natCard_field, c.Q_eq]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : 0 < p ^ c.h := Nat.pow_pos hp
  omega

include L in
/-- The prescribed positive extension degree also implies finite dimension. -/
theorem fieldFiniteDimensional : FiniteDimensional (ZMod p) E :=
  FiniteDimensional.of_finrank_pos (L.extension_degree.symm ▸ c.h_pos)

/-- The node as an extension-field element. -/
def node (t : Fin c.Q) : E := (L.nodes t).val

@[simp] theorem node_ne_zero (t : Fin c.Q) : L.node t ≠ 0 :=
  (L.nodes t).property

theorem node_injective : Function.Injective L.node := by
  intro s t h
  apply L.nodes.injective
  exact Subtype.ext h

theorem exists_node {z : E} (hz : z ≠ 0) : ∃ t, L.node t = z := by
  obtain ⟨t, ht⟩ := L.nodes.surjective ⟨z, hz⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- A row evaluation is a genuine linear map over the base field. -/
def rowMap (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) :
    (V → ZMod p) →ₗ[ZMod p] E :=
  CosetInvariance.finiteRow (fun w => (L.row e v w).eval (L.node t))

@[simp] theorem rowMap_apply (t : Fin c.Q) (e : F)
    (v : {v // v ∈ P.scope e}) (x : V → ZMod p) :
    L.rowMap t e v x =
      ∑ w, (L.row e v w).eval (L.node t) * algebraMap (ZMod p) E (x w) := rfl

theorem K_le_ker_rowMap (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) :
    L.K t (L.color e t) ≤ LinearMap.ker (L.rowMap t e v) := by
  intro r hr
  exact L.annihilation t e v r hr

/-- The row is constant on every coset of its factor's selected subspace. -/
theorem rowMap_eq_of_sub_mem (t : Fin c.Q) (e : F)
    (v : {v // v ∈ P.scope e}) {x y : V → ZMod p}
    (hxy : y - x ∈ L.K t (L.color e t)) :
    L.rowMap t e v y = L.rowMap t e v x :=
  CosetInvariance.linear_map_eq_of_sub_mem _ _ (L.K_le_ker_rowMap t e v) hxy

/-- Disjoint coordinate supports imply disjoint subspaces over the base field. -/
theorem K_disjoint (t : Fin c.Q) : Disjoint (L.K t false) (L.K t true) := by
  apply disjoint_iff.mpr
  apply le_antisymm
  · intro r hr
    change r = 0
    funext v
    by_cases hv : v ∈ L.support t false
    · exact L.supported t true r hr.2 v
        (fun hv' => Finset.disjoint_left.mp (L.support_disjoint t) hv hv')
    · exact L.supported t false r hr.1 v hv
  · exact bot_le

/-- The selected subspace written using only its supported coordinates. -/
abbrev localK (t : Fin c.Q) (g : Bool) :
    Submodule (ZMod p) (L.support t g → ZMod p) :=
  CosetCardinality.restrictedSubspace (L.support t g) (L.K t g)

theorem finrank_localK (t : Fin c.Q) (g : Bool) :
    Module.finrank (ZMod p) (L.localK t g) = Module.finrank (ZMod p) (L.K t g) :=
  CosetCardinality.finrank_restrictedSubspace _ _ (L.supported t g)

/-- The outer choices: complementary coordinates and a coset on each side. -/
abbrev Outer (t : Fin c.Q) :=
  CosetCardinality.CoordinateOuterData (L.support t false) (L.support t true)
    (L.localK t false) (L.localK t true)

abbrev Left (t : Fin c.Q) (o : L.Outer t) :=
  CosetCardinality.CosetFiber (L.localK t false) o.2.1

abbrev Right (t : Fin c.Q) (o : L.Outer t) :=
  CosetCardinality.CosetFiber (L.localK t true) o.2.2

/-- The actual bijection partitioning all assignments into outer data and two
local cosets. No assignment is omitted or counted twice. -/
def coordinateOuterFiberEquiv (t : Fin c.Q) :
    (V → ZMod p) ≃ Σ o : L.Outer t, L.Left t o × L.Right t o :=
  CosetCardinality.coordinateOuterFiberEquiv _ _ (L.support_disjoint t) _ _

/-- Reassemble an assignment from its outer data and two inner points. -/
def reconstruct (t : Fin c.Q) (o : L.Outer t) (x0 : L.Left t o)
    (x1 : L.Right t o) : V → ZMod p :=
  (L.coordinateOuterFiberEquiv t).symm ⟨o, x0, x1⟩

theorem reconstruct_left_sub_mem (t : Fin c.Q) (o : L.Outer t)
    (x0 y0 : L.Left t o) (x1 : L.Right t o) :
    L.reconstruct t o x0 x1 - L.reconstruct t o y0 x1 ∈ L.K t false :=
  CosetCardinality.coordinateReconstruct_left_sub_mem _ _ (L.support_disjoint t)
    _ _ (L.supported t false) o x0 y0 x1

theorem reconstruct_right_sub_mem (t : Fin c.Q) (o : L.Outer t)
    (x0 : L.Left t o) (x1 y1 : L.Right t o) :
    L.reconstruct t o x0 x1 - L.reconstruct t o x0 y1 ∈ L.K t true :=
  CosetCardinality.coordinateReconstruct_right_sub_mem _ _ (L.support_disjoint t)
    _ _ (L.supported t true) o x0 x1 y1

theorem dimensions_sum_le (t : Fin c.Q) :
    Module.finrank (ZMod p) (L.K t false) + Module.finrank (ZMod p) (L.K t true)
      ≤ Fintype.card V := by
  simpa only [L.finrank_localK] using
    CosetCardinality.coordinate_dimensions_le _ _ (L.support_disjoint t)
      (L.localK t false) (L.localK t true)

/-- Exact number of outer choices for the layout's own subspaces. -/
theorem card_outer (t : Fin c.Q) :
    Nat.card (L.Outer t) = p ^ (Fintype.card V - Module.finrank (ZMod p) (L.K t false)
      - Module.finrank (ZMod p) (L.K t true)) := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using
    CosetCardinality.card_supported_outer _ _ (L.support_disjoint t)
      _ _ (L.supported t false) (L.supported t true)

/-- The actual enumeration count, as distinct from a bit-operation cost. -/
theorem iteration_bound (t : Fin c.Q) :
    Nat.card (L.Outer t) * (Nat.card (L.localK t false) + Nat.card (L.localK t true))
      ≤ 2 * p ^ (3 * Fintype.card V / 4) := by
  have h0 : Fintype.card V ≤ 4 * Module.finrank (ZMod p) (L.localK t false) := by
    rw [L.finrank_localK]
    exact L.dimension_lower t false
  have h1 : Fintype.card V ≤ 4 * Module.finrank (ZMod p) (L.localK t true) := by
    rw [L.finrank_localK]
    exact L.dimension_lower t true
  simpa only [ZMod.card] using
    CosetCardinality.coordinate_iteration_bound _ _ (L.support_disjoint t)
      (L.localK t false) (L.localK t true) h0 h1

end Layout

section Lifts

variable {P : Factor.Pattern V F} {c : Constants p k Δ}
variable {Λ : Type*} [CommRing Λ]

/-- Coefficient and node lifts needed in Section 4.  The residue map need not
have a ring-homomorphic section.  Its row lifts retain their exact selector
constant coefficient and their degree. `ofSurjective` below constructs these
lifts from a surjective residue map. -/
structure LiftedLayout (L : Layout (E := E) P c) (Λ : Type*) [CommRing Λ] where
  residue : Λ →+* E
  theta : Fin c.Q → Λ
  residue_theta : ∀ t, residue (theta t) = L.node t
  row : (e : F) → {v // v ∈ P.scope e} → V → Polynomial Λ
  residue_row : ∀ e v w, (row e v w).map residue = L.row e v w
  row_zero : ∀ e v w, (row e v w).eval 0 = if w = v.val then 1 else 0
  row_degree : ∀ e v w, (row e v w).natDegree ≤ c.R

namespace LiftedLayout

variable {L : Layout (E := E) P c} (A : LiftedLayout L Λ)

/-- A surjective residue homomorphism suffices to construct all node and row
lifts, including the exact zero-value and degree requirements. This is a finite
existence construction; no algorithmic cost for choosing preimages is claimed. -/
noncomputable def ofSurjective (L : Layout (E := E) P c)
    (ρ : Λ →+* E) (hρ : Function.Surjective ρ) : LiftedLayout L Λ := by
  classical
  have hr : ∀ (e : F) (v : {v // v ∈ P.scope e}) (w : V),
      ∃ q : Polynomial Λ, q.map ρ = L.row e v w ∧
        q.eval 0 = (if w = v.val then 1 else 0) ∧
          q.natDegree ≤ (L.row e v w).natDegree := by
    intro e v w
    apply exists_polynomial_lift ρ hρ
    rw [L.row_zero]
    split_ifs <;> simp
  choose row hmap hzero hdegree using hr
  refine
    { residue := ρ
      theta := fun t => Classical.choose (hρ (L.node t))
      residue_theta := fun t => Classical.choose_spec (hρ (L.node t))
      row := row
      residue_row := hmap
      row_zero := hzero
      row_degree := ?_ }
  intro e v w
  exact (hdegree e v w).trans (L.row_degree e v w)

theorem residue_row_eval (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e})
    (w : V) :
    A.residue ((A.row e v w).eval (A.theta t)) =
      (L.row e v w).eval (L.node t) := by
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map,
    A.residue_row, A.residue_theta]

/-- Actual lifted row evaluation, with arbitrary coordinate representatives.
Only the residue condition is used; carries between representatives are allowed. -/
def liftedRow (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) :
    CosetInvariance.LiftedRow A.residue (L.rowMap t e v) where
  value x := ∑ w, (A.row e v w).eval (A.theta t) * coordinateLift (x w)
  residue_value x := by
    simp only [map_sum, map_mul, hLift, A.residue_row_eval, Layout.rowMap_apply]

/-- Chosen residue representatives are exactly constant on the selected cosets. -/
theorem beta_eq_of_sub_mem (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e})
    {x y : V → ZMod p} (hxy : y - x ∈ L.K t (L.color e t)) :
    (A.liftedRow coordinateLift hLift t e v).beta s y =
      (A.liftedRow coordinateLift hLift t e v).beta s x :=
  CosetInvariance.LiftedRow.beta_invariant _ s _ (L.K_le_ker_rowMap t e v) hxy

/-- A color-zero beta ignores the left inner point once outer data are fixed. -/
theorem beta_reconstruct_left (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) (hcolor : L.color e t = false)
    (o : L.Outer t) (x0 y0 : L.Left t o) (x1 : L.Right t o) :
    (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o x0 x1) =
      (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o y0 x1) := by
  apply A.beta_eq_of_sub_mem coordinateLift hLift s t e v
  rw [hcolor]
  exact L.reconstruct_left_sub_mem t o x0 y0 x1

/-- A color-one beta ignores the right inner point once outer data are fixed. -/
theorem beta_reconstruct_right (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) (hcolor : L.color e t = true)
    (o : L.Outer t) (x0 : L.Left t o) (x1 y1 : L.Right t o) :
    (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o x0 x1) =
      (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o x0 y1) := by
  apply A.beta_eq_of_sub_mem coordinateLift hLift s t e v
  rw [hcolor]
  exact L.reconstruct_right_sub_mem t o x0 x1 y1

end LiftedLayout
end Lifts
end Layout

end SubexponentialSAT.LayoutSpec

end OAI.Algorithms
