import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.LayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpDirectSums
import OAI.Algorithms.SubexponentialSAT.SubexpCosetCount
import OAI.Algorithms.SubexponentialSAT.SubexpInvariance

namespace OAI.Algorithms

/-!
# Semantic interface for the multicolor interpolation layout

This is the output specification of Lemma 3.2 in `subexponential-sat.txt`.
It does not assert the existence of these layouts or a running-time bound.
The numerical parameters may grow with the input, and quantitative construction
costs are separate from this finite algebraic interface.

A factor of color `g` annihilates the subspaces of every **other** color.
Rows remain incidence-specific. All subspaces and dimensions are over `ZMod p`;
only interpolation coefficients and points use the extension field.
-/

namespace SubexponentialSAT.SubexpLayoutSpec

open scoped BigOperators

/-- Semantic numerical parameters. The formula for `R` and the binomial-tail
and block-packing hypotheses belong to the construction, not to this output
specification. `tau` is rational to retain exact quantitative inequalities. -/
structure Parameters (p k Δ r : ℕ) (tau : ℚ) extends LayoutSpec.Constants p k Δ where
  r_ge_two : 2 ≤ r
  tau_pos : 0 < tau
  tau_le_half : tau ≤ 1 / 2

section Layout

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F]
variable [Field E] [Algebra (ZMod p) E]

/-- The multicolor layout on a bounded factor pattern. Rational dimension
inequalities and the integer support inequality avoid any rounding weakening. -/
structure Layout (P : Factor.Pattern V F) (c : Parameters p k Δ r tau) where
  bounded : P.Bounded k Δ
  size_ge : c.Dstar ≤ Fintype.card V
  extension_degree : Module.finrank (ZMod p) E = c.h
  nodes : Fin c.Q ≃ {z : E // z ≠ 0}
  support : Fin c.Q → Fin r → Finset V
  support_disjoint : ∀ t, Pairwise (fun g h => Disjoint (support t g) (support t h))
  support_upper : ∀ t g, r * (support t g).card ≤ Fintype.card V
  K : Fin c.Q → Fin r → Submodule (ZMod p) (V → ZMod p)
  supported : ∀ t g x, x ∈ K t g → ∀ v, v ∉ support t g → x v = 0
  dimension_lower : ∀ t g,
    (1 - tau) ^ 2 * (Fintype.card V : ℚ) ≤
      (r : ℚ) * (Module.finrank (ZMod p) (K t g) : ℚ)
  color : F → Fin c.Q → Fin r
  row : (e : F) → {v // v ∈ P.scope e} → V → Polynomial E
  row_zero : ∀ e v w, (row e v w).eval 0 = if w = v.val then 1 else 0
  row_degree : ∀ e v w, (row e v w).natDegree ≤ c.R
  annihilation : ∀ t e v g x, g ≠ color e t → x ∈ K t g →
    ∑ w, (row e v w).eval (nodes t).val * algebraMap (ZMod p) E (x w) = 0

namespace Layout

variable {P : Factor.Pattern V F} {c : Parameters p k Δ r tau}
variable (L : Layout (E := E) P c)

/-- Adding zero to the node enumeration enumerates the extension field. -/
noncomputable def fieldEquiv : Option (Fin c.Q) ≃ E := by
  classical
  exact (Equiv.optionCongr L.nodes).trans (Equiv.optionSubtypeNe 0)

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
theorem fieldFiniteDimensional : FiniteDimensional (ZMod p) E :=
  FiniteDimensional.of_finrank_pos (L.extension_degree.symm ▸ c.h_pos)

def node (t : Fin c.Q) : E := (L.nodes t).val

@[simp] theorem node_ne_zero (t : Fin c.Q) : L.node t ≠ 0 :=
  (L.nodes t).property

theorem node_injective : Function.Injective L.node := by
  intro s t h
  exact L.nodes.injective (Subtype.ext h)

theorem exists_node {z : E} (hz : z ≠ 0) : ∃ t, L.node t = z := by
  obtain ⟨t, ht⟩ := L.nodes.surjective ⟨z, hz⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- Every row evaluation is linear over the base field. -/
def rowMap (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) :
    (V → ZMod p) →ₗ[ZMod p] E :=
  CosetInvariance.finiteRow (fun w => (L.row e v w).eval (L.node t))

@[simp] theorem rowMap_apply (t : Fin c.Q) (e : F)
    (v : {v // v ∈ P.scope e}) (x : V → ZMod p) :
    L.rowMap t e v x =
      ∑ w, (L.row e v w).eval (L.node t) * algebraMap (ZMod p) E (x w) := rfl

theorem K_le_ker_rowMap (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e})
    (g : Fin r) (hg : g ≠ L.color e t) :
    L.K t g ≤ LinearMap.ker (L.rowMap t e v) := by
  intro x hx
  exact L.annihilation t e v g x hg hx

theorem rowMap_eq_of_sub_mem (t : Fin c.Q) (e : F)
    (v : {v // v ∈ P.scope e}) (g : Fin r) (hg : g ≠ L.color e t)
    {x y : V → ZMod p} (hxy : y - x ∈ L.K t g) :
    L.rowMap t e v y = L.rowMap t e v x :=
  CosetInvariance.linear_map_eq_of_sub_mem _ _ (L.K_le_ker_rowMap t e v g hg) hxy

theorem K_disjoint (t : Fin c.Q) : Pairwise (fun g h => Disjoint (L.K t g) (L.K t h)) := by
  intro g h hgh
  apply disjoint_iff.mpr
  apply le_antisymm
  · intro x hx
    change x = 0
    funext v
    by_cases hv : v ∈ L.support t g
    · exact L.supported t h x hx.2 v
        (fun hv' => Finset.disjoint_left.mp (L.support_disjoint t hgh) hv hv')
    · exact L.supported t g x hx.1 v hv
  · exact bot_le

/-- The same subspace expressed only on its support coordinates. -/
abbrev localK (t : Fin c.Q) (g : Fin r) :
    Submodule (ZMod p) (L.support t g → ZMod p) :=
  CosetCardinality.restrictedSubspace (L.support t g) (L.K t g)

theorem finrank_localK (t : Fin c.Q) (g : Fin r) :
    Module.finrank (ZMod p) (L.localK t g) = Module.finrank (ZMod p) (L.K t g) :=
  CosetCardinality.finrank_restrictedSubspace _ _ (L.supported t g)

/-- Subspace dimension cannot exceed the number of supporting coordinates. -/
theorem dimension_le_support (t : Fin c.Q) (g : Fin r) :
    Module.finrank (ZMod p) (L.K t g) ≤ (L.support t g).card := by
  rw [← L.finrank_localK]
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    Submodule.finrank_le (L.localK t g)

theorem dimension_upper (t : Fin c.Q) (g : Fin r) :
    r * Module.finrank (ZMod p) (L.K t g) ≤ Fintype.card V :=
  (Nat.mul_le_mul_left r (L.dimension_le_support t g)).trans (L.support_upper t g)

theorem dimensions_sum_le (t : Fin c.Q) :
    (∑ g, Module.finrank (ZMod p) (L.K t g)) ≤ Fintype.card V :=
  SubexpDirectSums.sum_finrank_le_card (L.K t) (L.support t)
    (L.support_disjoint t) (L.supported t)

/-- Summing the individual lower bounds retains the full `(1-tau)^2 D`. -/
theorem dimensions_sum_lower (t : Fin c.Q) :
    (1 - tau) ^ 2 * (Fintype.card V : ℚ) ≤
      ∑ g, (Module.finrank (ZMod p) (L.K t g) : ℚ) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun g _ => L.dimension_lower t g)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hr : (0 : ℚ) < r := Nat.cast_pos.mpr (by have := c.r_ge_two; omega)
  nlinarith [hsum]

/-- Complement coordinates outside all color supports. -/
abbrev Outside (t : Fin c.Q) :=
  ↥((Finset.univ.biUnion (L.support t))ᶜ) → ZMod p

/-- Complement coordinates and one quotient class per color. -/
abbrev Outer (t : Fin c.Q) :=
  SubexpCosetCount.OuterData (Vstar := L.Outside t) (L.localK t)

/-- An actual point of the specified color's coset. -/
abbrev Inner (t : Fin c.Q) (o : L.Outer t) (g : Fin r) :=
  CosetCardinality.CosetFiber (L.localK t g) (o.2 g)

/-- All actual assignments, partitioned into outer choices and the dependent
product of their color-coset points. -/
noncomputable def coordinateOuterFiberEquiv (t : Fin c.Q) :
    (V → ZMod p) ≃ Σ o : L.Outer t, ∀ g, L.Inner t o g :=
  (SubexpDirectSums.coordinateSplitEquiv (L.support t)
    (L.support_disjoint t)).toEquiv.trans (SubexpCosetCount.familyCosetEquiv (L.localK t))

noncomputable def reconstruct (t : Fin c.Q) (o : L.Outer t)
    (x : ∀ g, L.Inner t o g) : V → ZMod p :=
  (L.coordinateOuterFiberEquiv t).symm ⟨o, x⟩

theorem reconstruct_eq (t : Fin c.Q) (o : L.Outer t) (x : ∀ g, L.Inner t o g) :
    L.reconstruct t o x =
      SubexpDirectSums.coordinateAssemble (L.support t) (o.1, fun g => (x g).val) := rfl

/-- Reconstruction has exactly the complement and color coordinates supplied
to it; this is the interface for factorizing the actual moment weights. -/
theorem reconstruct_components (t : Fin c.Q) (o : L.Outer t)
    (x : ∀ g, L.Inner t o g) :
    (fun i : ↥((Finset.univ.biUnion (L.support t))ᶜ) => L.reconstruct t o x i.val) = o.1 ∧
      ∀ g, (fun i : L.support t g => L.reconstruct t o x i.val) = (x g).val := by
  constructor
  · funext i
    rw [L.reconstruct_eq]
    exact SubexpDirectSums.coordinateAssemble_outside _ _ i.val i.property
  · intro g
    funext i
    rw [L.reconstruct_eq]
    exact SubexpDirectSums.coordinateAssemble_on_color _ (L.support_disjoint t)
      _ g i.val i.property

theorem card_outer (t : Fin c.Q) :
    Nat.card (L.Outer t) =
      p ^ (Fintype.card V - ∑ g, Module.finrank (ZMod p) (L.K t g)) := by
  have hd := SubexpCosetCount.ambientDimension_eq_card_coordinates
    (SubexpDirectSums.coordinateSplitEquiv (K := ZMod p) (L.support t) (L.support_disjoint t))
  simpa only [hd, L.finrank_localK, ZMod.card] using
    SubexpCosetCount.card_outer (Vstar := L.Outside t) (L.localK t)

/-- One outer choice and one term from one of its individual inner sums. -/
abbrev Iterations (t : Fin c.Q) :=
  SubexpCosetCount.IterationData (Vstar := L.Outside t) (L.localK t)

theorem card_iterations (t : Fin c.Q) :
    Nat.card (L.Iterations t) = SubexpCosetCount.iterationCount p (Fintype.card V)
      (fun g => Module.finrank (ZMod p) (L.K t g)) := by
  have hd := SubexpCosetCount.ambientDimension_eq_card_coordinates
    (SubexpDirectSums.coordinateSplitEquiv (K := ZMod p) (L.support t) (L.support_disjoint t))
  simpa only [hd, L.finrank_localK, ZMod.card] using
    SubexpCosetCount.card_iteration (Vstar := L.Outside t) (L.localK t)

/-- The exact iteration type satisfies (4.7). This is a cardinality theorem,
not a claim about the bit cost of creating or traversing its elements. -/
theorem iteration_bound (t : Fin c.Q) :
    (Nat.card (L.Iterations t) : ℝ) ≤ (r : ℝ) * (p : ℝ) ^
      (SubexpCosetCount.alpha r (tau : ℝ) * (Fintype.card V : ℝ)) := by
  rw [L.card_iterations]
  apply SubexpCosetCount.iterationCount_le_real
  · exact (Fact.out : p.Prime).one_lt.le
  · exact L.dimensions_sum_le t
  · exact_mod_cast L.dimensions_sum_lower t
  · intro g
    have hr : (0 : ℝ) < r := Nat.cast_pos.mpr (by have := c.r_ge_two; omega)
    apply (le_div_iff₀ hr).mpr
    have hd : (r : ℝ) * (Module.finrank (ZMod p) (L.K t g) : ℝ) ≤ Fintype.card V := by
      exact_mod_cast L.dimension_upper t g
    simpa only [mul_comm] using hd

end Layout

section Enumeration

variable {P : Factor.Pattern V F} {c : Parameters p k Δ r tau}

/-- Explicit finite-array data consumed by a separated evaluator. The stored
functions return actual vectors. `assignmentEquiv` certifies complete, unique
enumeration; its inverse must have the displayed additive form.

This is a consumer contract, not an asserted construction. In particular, no
choice-based basis selection is represented as an executable-cost proof. -/
structure EnumerationData (L : Layout (E := E) P c) (t : Fin c.Q) where
  outerCount : ℕ
  innerCount : Fin r → ℕ
  outerBase : Fin outerCount → V → ZMod p
  incrementEquiv : ∀ g, Fin (innerCount g) ≃ L.K t g
  assignmentEquiv : (V → ZMod p) ≃ (Fin outerCount × ∀ g, Fin (innerCount g))
  reconstruction : ∀ o x, assignmentEquiv.symm (o, x) =
    outerBase o + ∑ g, (incrementEquiv g (x g)).val

namespace EnumerationData

variable {L : Layout (E := E) P c} {t : Fin c.Q} (D : EnumerationData L t)

/-- The actual within-coset vector at one array index. -/
def increment (g : Fin r) (j : Fin (D.innerCount g)) : V → ZMod p :=
  (D.incrementEquiv g j).val

theorem increment_mem (g : Fin r) (j : Fin (D.innerCount g)) :
    D.increment g j ∈ L.K t g := (D.incrementEquiv g j).property

/-- An index for the zero increment, without assuming a particular array order. -/
def zeroIndex (g : Fin r) : Fin (D.innerCount g) := (D.incrementEquiv g).symm 0

@[simp] theorem increment_zeroIndex (g : Fin r) : D.increment g (D.zeroIndex g) = 0 := by
  exact congrArg Subtype.val ((D.incrementEquiv g).apply_symm_apply 0)

theorem reconstruct_eq (o : Fin D.outerCount) (x : ∀ g, Fin (D.innerCount g)) :
    D.assignmentEquiv.symm (o, x) = D.outerBase o + ∑ g, D.increment g (x g) :=
  D.reconstruction o x

/-- Inner array lengths are derived from the supplied equivalences. -/
theorem innerCount_eq (g : Fin r) :
    D.innerCount g = p ^ Module.finrank (ZMod p) (L.K t g) := by
  calc
    D.innerCount g = Nat.card (Fin (D.innerCount g)) := by simp
    _ = Nat.card (L.K t g) := Nat.card_congr (D.incrementEquiv g)
    _ = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (L.K t g) :=
      CosetCardinality.card_submodule (L.K t g)
    _ = _ := by simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- The exact outer length follows from unique enumeration and the dimensions;
it is not a cost assertion stored as a field. -/
theorem outerCount_eq :
    D.outerCount = p ^ (Fintype.card V - ∑ g, Module.finrank (ZMod p) (L.K t g)) := by
  have hcard := Fintype.card_congr D.assignmentEquiv
  simp only [Fintype.card_fun, Fintype.card_pi, Fintype.card_prod,
    Fintype.card_fin, ZMod.card] at hcard
  simp_rw [D.innerCount_eq] at hcard
  rw [Finset.prod_pow_eq_pow_sum] at hcard
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply mul_right_cancel₀
    (ne_of_gt (Nat.pow_pos hp) : p ^ (∑ g, Module.finrank (ZMod p) (L.K t g)) ≠ 0)
  calc
    D.outerCount * p ^ (∑ g, Module.finrank (ZMod p) (L.K t g)) = p ^ Fintype.card V :=
      hcard.symm
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel (L.dimensions_sum_le t)]

/-- The exact number of individual inner terms scanned across all outer data. -/
def iterationCount : ℕ := D.outerCount * ∑ g, D.innerCount g

theorem iterationCount_eq : D.iterationCount =
    SubexpCosetCount.iterationCount p (Fintype.card V)
      (fun g => Module.finrank (ZMod p) (L.K t g)) := by
  simp only [iterationCount, D.outerCount_eq, D.innerCount_eq,
    SubexpCosetCount.iterationCount]

theorem iterationCount_bound : (D.iterationCount : ℝ) ≤
    (r : ℝ) * (p : ℝ) ^
      (SubexpCosetCount.alpha r (tau : ℝ) * (Fintype.card V : ℝ)) := by
  rw [D.iterationCount_eq, ← L.card_iterations]
  exact L.iteration_bound t

/-- A row can be evaluated at just the basepoint and its own color increment;
the other color increments make zero contribution to its residue. -/
theorem rowMap_base_add_sum (e : F) (v : {v // v ∈ P.scope e})
    (o : Fin D.outerCount) (x : ∀ g, Fin (D.innerCount g)) :
    L.rowMap t e v (D.outerBase o + ∑ g, D.increment g (x g)) =
      L.rowMap t e v (D.outerBase o + D.increment (L.color e t) (x (L.color e t))) := by
  simp only [map_add, map_sum]
  congr 1
  apply Finset.sum_eq_single (L.color e t)
  · intro g _ hg
    exact L.K_le_ker_rowMap t e v g hg (D.increment_mem g (x g))
  · simp

end EnumerationData
end Enumeration

section Lifts

variable {P : Factor.Pattern V F} {c : Parameters p k Δ r tau}
variable {Λ : Type*} [CommRing Λ]

/-- Node and incidence-polynomial lifts for multicolor counting. -/
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

/-- Algebraic construction from a surjective residue map; no executable cost
is claimed for the classical preimage selections in this definition. -/
noncomputable def ofSurjective (L : Layout (E := E) P c)
    (ρ : Λ →+* E) (hρ : Function.Surjective ρ) : LiftedLayout L Λ := by
  classical
  have hr : ∀ (e : F) (v : {v // v ∈ P.scope e}) (w : V),
      ∃ q : Polynomial Λ, q.map ρ = L.row e v w ∧
        q.eval 0 = (if w = v.val then 1 else 0) ∧
          q.natDegree ≤ (L.row e v w).natDegree := by
    intro e v w
    apply LayoutSpec.exists_polynomial_lift ρ hρ
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

def liftedRow (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) :
    CosetInvariance.LiftedRow A.residue (L.rowMap t e v) where
  value x := ∑ w, (A.row e v w).eval (A.theta t) * coordinateLift (x w)
  residue_value x := by
    simp only [map_sum, map_mul, hLift, A.residue_row_eval, Layout.rowMap_apply]

/-- A factor's beta ignores translations in any subspace of another color. -/
theorem beta_eq_of_sub_mem (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e})
    (g : Fin r) (hg : g ≠ L.color e t)
    {x y : V → ZMod p} (hxy : y - x ∈ L.K t g) :
    (A.liftedRow coordinateLift hLift t e v).beta s y =
      (A.liftedRow coordinateLift hLift t e v).beta s x :=
  CosetInvariance.LiftedRow.beta_invariant _ s _ (L.K_le_ker_rowMap t e v g hg) hxy

/-- With all outer data fixed, beta depends on just its factor's own color
component, even when every other component changes within its coset. -/
theorem beta_reconstruct_eq (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (e : F) (v : {v // v ∈ P.scope e}) (o : L.Outer t)
    {x y : ∀ g, L.Inner t o g} (hown : x (L.color e t) = y (L.color e t)) :
    (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o x) =
      (A.liftedRow coordinateLift hLift t e v).beta s (L.reconstruct t o y) := by
  simpa only [L.reconstruct_eq] using
    SubexpInvariance.beta_coordinateAssemble_eq
      (A.liftedRow coordinateLift hLift t e v) s (L.support t) (L.K t)
      (L.supported t) (L.color e t) (fun g hg => L.K_le_ker_rowMap t e v g hg)
      o.1 o.2 hown

/-- The explicit-array evaluator likewise needs only one color increment to
compute a factor's beta value. It never needs the product of all inner arrays. -/
theorem beta_enumeration_eq (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, A.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (D : EnumerationData L t) (e : F) (v : {v // v ∈ P.scope e})
    (o : Fin D.outerCount) (x : ∀ g, Fin (D.innerCount g)) :
    (A.liftedRow coordinateLift hLift t e v).beta s (D.assignmentEquiv.symm (o, x)) =
      (A.liftedRow coordinateLift hLift t e v).beta s
        (D.outerBase o + D.increment (L.color e t) (x (L.color e t))) := by
  rw [D.reconstruct_eq]
  simp only [CosetInvariance.LiftedRow.beta_eq_lift_row]
  exact congrArg s.lift (D.rowMap_base_add_sum e v o x)

end LiftedLayout
end Lifts
end Layout

end SubexponentialSAT.SubexpLayoutSpec

end OAI.Algorithms
