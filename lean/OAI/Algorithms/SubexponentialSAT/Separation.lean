import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CosetInvariance
import OAI.Algorithms.SubexponentialSAT.CosetCardinality
import OAI.Algorithms.SubexponentialSAT.Moments

namespace OAI.Algorithms

/-!
# Separation of the symbolic moment sums

Section 4.5, equation (4.8).  The input arguments of the two group functions
are separated while their values remain in one common commutative semiring.
In particular, the value semiring may be a polynomial or quotient ring;
there is no assertion that its formal variables split into disjoint groups.

All independence and weight hypotheses below concern the summands and are
pointwise.  The sum identity itself is proved by finite distributivity.
-/

namespace SubexponentialSAT.Separation

open scoped BigOperators

section FiniteSums

variable {A X Y O : Type*} [CommSemiring A]

/-- The distributive identity underlying (4.8), with the two functions already
written in terms of the input component on which each depends. -/
theorem separated_sum (s : Finset X) (t : Finset Y) (c : A)
    (w₀ : X → A) (w₁ : Y → A) (B₀ : Y → A) (B₁ : X → A) :
    (∑ x ∈ s, ∑ y ∈ t, c * w₀ x * w₁ y * B₀ y * B₁ x) =
      c * (∑ x ∈ s, w₀ x * B₁ x) * (∑ y ∈ t, w₁ y * B₀ y) := by
  calc
    _ = ∑ x ∈ s, ∑ y ∈ t, (c * (w₀ x * B₁ x)) * (w₁ y * B₀ y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [ mul_comm, mul_left_comm]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- Weighted separation from actual independence on the two finite sets.
Representatives must belong to those sets; only the group functions use
representatives, while every weight retains its actual summation input. -/
theorem weighted_separation (s : Finset X) (t : Finset Y)
    (r₀ : X) (r₁ : Y) (hr₀ : r₀ ∈ s) (hr₁ : r₁ ∈ t)
    (A₀ A₁ : X → Y → A) (w : X → Y → A)
    (c : A) (w₀ : X → A) (w₁ : Y → A)
    (h₀ : ∀ x ∈ s, ∀ x' ∈ s, ∀ y ∈ t, A₀ x y = A₀ x' y)
    (h₁ : ∀ x ∈ s, ∀ y ∈ t, ∀ y' ∈ t, A₁ x y = A₁ x y')
    (hw : ∀ x ∈ s, ∀ y ∈ t, w x y = c * w₀ x * w₁ y) :
    (∑ x ∈ s, ∑ y ∈ t, w x y * A₀ x y * A₁ x y) =
      c * (∑ x ∈ s, w₀ x * A₁ x r₁) * (∑ y ∈ t, w₁ y * A₀ r₀ y) := by
  calc
    _ = ∑ x ∈ s, ∑ y ∈ t, c * w₀ x * w₁ y * A₀ r₀ y * A₁ x r₁ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [hw x hx y hy, h₀ x hx r₀ hr₀ y hy, h₁ x hx y hy r₁ hr₁]
    _ = _ := separated_sum s t c w₀ w₁ (A₀ r₀) (fun x => A₁ x r₁)

/-- The same result for finite types, including finite coset subtypes. -/
theorem weighted_separation_fintype [Fintype X] [Fintype Y]
    (r₀ : X) (r₁ : Y) (A₀ A₁ : X → Y → A) (w : X → Y → A)
    (c : A) (w₀ : X → A) (w₁ : Y → A)
    (h₀ : ∀ x x' y, A₀ x y = A₀ x' y)
    (h₁ : ∀ x y y', A₁ x y = A₁ x y')
    (hw : ∀ x y, w x y = c * w₀ x * w₁ y) :
    (∑ x, ∑ y, w x y * A₀ x y * A₁ x y) =
      c * (∑ x, w₀ x * A₁ x r₁) * (∑ y, w₁ y * A₀ r₀ y) := by
  exact weighted_separation Finset.univ Finset.univ r₀ r₁
    (Finset.mem_univ _) (Finset.mem_univ _) A₀ A₁ w c w₀ w₁
    (fun x _ x' _ y _ => h₀ x x' y)
    (fun x _ y _ y' _ => h₁ x y y') (fun x _ y _ => hw x y)

/-- Scalar weights can be embedded into a polynomial or quotient ring by a
ring homomorphism.  In the moment application this homomorphism is `C`. -/
theorem weighted_separation_map_weights {S : Type*} [CommSemiring S]
    (φ : A →+* S) (s : Finset X) (t : Finset Y)
    (r₀ : X) (r₁ : Y) (hr₀ : r₀ ∈ s) (hr₁ : r₁ ∈ t)
    (A₀ A₁ : X → Y → S) (w : X → Y → A)
    (c : A) (w₀ : X → A) (w₁ : Y → A)
    (h₀ : ∀ x ∈ s, ∀ x' ∈ s, ∀ y ∈ t, A₀ x y = A₀ x' y)
    (h₁ : ∀ x ∈ s, ∀ y ∈ t, ∀ y' ∈ t, A₁ x y = A₁ x y')
    (hw : ∀ x ∈ s, ∀ y ∈ t, w x y = c * w₀ x * w₁ y) :
    (∑ x ∈ s, ∑ y ∈ t, φ (w x y) * A₀ x y * A₁ x y) =
      φ c * (∑ x ∈ s, φ (w₀ x) * A₁ x r₁) *
        (∑ y ∈ t, φ (w₁ y) * A₀ r₀ y) := by
  apply weighted_separation s t r₀ r₁ hr₀ hr₁ A₀ A₁
    (fun x y => φ (w x y)) (φ c) (fun x => φ (w₀ x)) (fun y => φ (w₁ y)) h₀ h₁
  intro x hx y hy
  rw [hw x hx y hy, map_mul, map_mul]

/-- Summing (4.8) over any explicit finite collection of outer data.
The finite inner sets and their representatives may depend on the outer data. -/
theorem weighted_separation_outer (os : Finset O)
    (s : O → Finset X) (t : O → Finset Y) (r₀ : O → X) (r₁ : O → Y)
    (hr₀ : ∀ o ∈ os, r₀ o ∈ s o) (hr₁ : ∀ o ∈ os, r₁ o ∈ t o)
    (A₀ A₁ : O → X → Y → A) (w : O → X → Y → A)
    (c : O → A) (w₀ : O → X → A) (w₁ : O → Y → A)
    (h₀ : ∀ o ∈ os, ∀ x ∈ s o, ∀ x' ∈ s o, ∀ y ∈ t o,
      A₀ o x y = A₀ o x' y)
    (h₁ : ∀ o ∈ os, ∀ x ∈ s o, ∀ y ∈ t o, ∀ y' ∈ t o,
      A₁ o x y = A₁ o x y')
    (hw : ∀ o ∈ os, ∀ x ∈ s o, ∀ y ∈ t o,
      w o x y = c o * w₀ o x * w₁ o y) :
    (∑ o ∈ os, ∑ x ∈ s o, ∑ y ∈ t o, w o x y * A₀ o x y * A₁ o x y) =
      ∑ o ∈ os, c o * (∑ x ∈ s o, w₀ o x * A₁ o x (r₁ o)) *
        (∑ y ∈ t o, w₁ o y * A₀ o (r₀ o) y) := by
  apply Finset.sum_congr rfl
  intro o ho
  exact weighted_separation (s o) (t o) (r₀ o) (r₁ o) (hr₀ o ho) (hr₁ o ho)
    (A₀ o) (A₁ o) (w o) (c o) (w₀ o) (w₁ o) (h₀ o ho) (h₁ o ho) (hw o ho)

end FiniteSums

section FiniteFibers

variable {A Ω O : Type*} {X Y : O → Type*} [CommSemiring A]
  [Fintype Ω] [Fintype O] [∀ o, Fintype (X o)] [∀ o, Fintype (Y o)]

/-- An actual equivalence, rather than an assumed sum identity, reindexes a
finite input space by outer data and two finite fibers. -/
theorem sum_reindex_fibers (e : Ω ≃ Σ o, X o × Y o) (f : Ω → A) :
    (∑ z, f z) = ∑ o, ∑ x : X o, ∑ y : Y o, f (e.symm ⟨o, x, y⟩) := by
  calc
    _ = ∑ z : Σ o, X o × Y o, f (e.symm z) :=
      Fintype.sum_equiv e _ _ (fun z => by rw [e.symm_apply_apply])
    _ = _ := by simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

/-- Full-input version of (4.8), with dependent coset-like fibers. The
equivalence supplies exhaustive, nonduplicating input enumeration. -/
theorem weighted_separation_equiv (e : Ω ≃ Σ o, X o × Y o)
    (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o) (A₀ A₁ w : Ω → A)
    (c : O → A) (w₀ : ∀ o, X o → A) (w₁ : ∀ o, Y o → A)
    (h₀ : ∀ o x x' y,
      A₀ (e.symm ⟨o, x, y⟩) = A₀ (e.symm ⟨o, x', y⟩))
    (h₁ : ∀ o x y y',
      A₁ (e.symm ⟨o, x, y⟩) = A₁ (e.symm ⟨o, x, y'⟩))
    (hw : ∀ o x y, w (e.symm ⟨o, x, y⟩) = c o * w₀ o x * w₁ o y) :
    (∑ z, w z * A₀ z * A₁ z) =
      ∑ o, c o * (∑ x : X o, w₀ o x * A₁ (e.symm ⟨o, x, r₁ o⟩)) *
        (∑ y : Y o, w₁ o y * A₀ (e.symm ⟨o, r₀ o, y⟩)) := by
  rw [sum_reindex_fibers e]
  apply Finset.sum_congr rfl
  intro o ho
  exact weighted_separation_fintype (r₀ o) (r₁ o)
    (fun x y => A₀ (e.symm ⟨o, x, y⟩))
    (fun x y => A₁ (e.symm ⟨o, x, y⟩))
    (fun x y => w (e.symm ⟨o, x, y⟩)) (c o) (w₀ o) (w₁ o)
    (h₀ o) (h₁ o) (hw o)

end FiniteFibers

section CoordinateWeights

variable {A I V : Type*} [CommMonoid A]

/-- A monomial weight computed with arbitrary coordinate labels.  The label
map is an ordinary function: it need not preserve sums or products. -/
def coordinateWeight (s : Finset I) (label : V → A) (a : I → ℕ) (x : I → V) : A :=
  ∏ i ∈ s, label (x i) ^ a i

/-- Splitting an exact coordinate-label monomial across disjoint supports. -/
theorem coordinateWeight_union [DecidableEq I] (s t : Finset I) (hst : Disjoint s t)
    (label : V → A) (a : I → ℕ) (x : I → V) :
    coordinateWeight (s ∪ t) label a x =
      coordinateWeight s label a x * coordinateWeight t label a x := by
  exact Finset.prod_union hst

/-- The three weights in (4.8), with the complement represented by `sstar`.
No homomorphism property of the exact integer-label map is assumed. -/
theorem coordinateWeight_three [DecidableEq I] (sstar s₀ s₁ : Finset I)
    (hstar : Disjoint sstar (s₀ ∪ s₁)) (h₀₁ : Disjoint s₀ s₁)
    (label : V → A) (a : I → ℕ) (x : I → V) :
    coordinateWeight (sstar ∪ (s₀ ∪ s₁)) label a x =
      coordinateWeight sstar label a x * coordinateWeight s₀ label a x *
        coordinateWeight s₁ label a x := by
  rw [coordinateWeight_union _ _ hstar, coordinateWeight_union _ _ h₀₁, mul_assoc]

/-- If the three supports cover all coordinates, their product is the full
monomial weight used in the moment sum. -/
theorem coordinateWeight_partition [DecidableEq I] [Fintype I]
    (sstar s₀ s₁ : Finset I)
    (hstar : Disjoint sstar (s₀ ∪ s₁)) (h₀₁ : Disjoint s₀ s₁)
    (hcover : sstar ∪ (s₀ ∪ s₁) = Finset.univ)
    (label : V → A) (a : I → ℕ) (x : I → V) :
    coordinateWeight Finset.univ label a x =
      coordinateWeight sstar label a x * coordinateWeight s₀ label a x *
        coordinateWeight s₁ label a x := by
  rw [← hcover]
  exact coordinateWeight_three sstar s₀ s₁ hstar h₀₁ label a x

/-- A weight on one block depends only on the input coordinates in that block. -/
theorem coordinateWeight_congr (s : Finset I) (label : V → A) (a : I → ℕ)
    {x y : I → V} (hxy : ∀ i ∈ s, x i = y i) :
    coordinateWeight s label a x = coordinateWeight s label a y := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [hxy i hi]

end CoordinateWeights

section MomentWeights

variable {A I : Type*} [CommSemiring A] [Fintype I] [DecidableEq I]

/-- The actual finite-support moment weight splits over the two supports and
their complement.  The exponents retain their original ambient indices. -/
theorem momentWeight_partition (S₀ S₁ : Finset I) (h : Disjoint S₀ S₁)
    (a : I →₀ ℕ) (v : I → A) :
    Moments.weight a v =
      (∏ i : ↥((S₀ ∪ S₁)ᶜ), v i.val ^ a i.val) *
        (∏ i : S₀, v i.val ^ a i.val) *
        (∏ i : S₁, v i.val ^ a i.val) := by
  rw [Finset.prod_coe_sort ((S₀ ∪ S₁)ᶜ) (fun i => v i ^ a i),
    Finset.prod_coe_sort S₀ (fun i => v i ^ a i),
    Finset.prod_coe_sort S₁ (fun i => v i ^ a i)]
  rw [Moments.weight_eq_prod_univ,
    ← Finset.prod_compl_mul_prod (S₀ ∪ S₁) (fun i => v i ^ a i),
    Finset.prod_union h]
  exact (mul_assoc _ _ _).symm

end MomentWeights

section ReconstructedMomentWeights

open CosetCardinality

variable {A 𝔽 I : Type*} [CommSemiring A] [Field 𝔽] [Fintype I] [DecidableEq I]

/-- The concrete valuation reconstructed from an outer datum and its two
coset points has exactly the product of the three local moment weights.
The label map is arbitrary; no additive property of exact integer labels is
used.  This discharges the weight-factorization premise for the layout's
actual coordinate equivalence. -/
theorem momentWeight_coordinateReconstruct (S₀ S₁ : Finset I)
    (h : Disjoint S₀ S₁)
    (K₀ : Submodule 𝔽 (S₀ → 𝔽)) (K₁ : Submodule 𝔽 (S₁ → 𝔽))
    (o : CoordinateOuterData S₀ S₁ K₀ K₁)
    (x : CosetFiber K₀ o.2.1) (y : CosetFiber K₁ o.2.2)
    (a : I →₀ ℕ) (lift : 𝔽 → A) :
    Moments.weight a
        (fun i => lift (coordinateReconstruct S₀ S₁ h K₀ K₁ o x y i)) =
      (∏ i : ↥((S₀ ∪ S₁)ᶜ), lift (o.1 i) ^ a i.val) *
        (∏ i : S₀, lift (x.val i) ^ a i.val) *
        (∏ i : S₁, lift (y.val i) ^ a i.val) := by
  rw [momentWeight_partition S₀ S₁ h]
  have hc := coordinateReconstruct_components S₀ S₁ h K₀ K₁ o x y
  have hs := congrArg
    (fun v : ↥((S₀ ∪ S₁)ᶜ) → 𝔽 => ∏ i : ↥((S₀ ∪ S₁)ᶜ), lift (v i) ^ a i.val)
    hc.1
  have h₀ := congrArg (fun v : S₀ → 𝔽 => ∏ i : S₀, lift (v i) ^ a i.val) hc.2.1
  have h₁ := congrArg (fun v : S₁ → 𝔽 => ∏ i : S₁, lift (v i) ^ a i.val) hc.2.2
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hs h₀) h₁

end ReconstructedMomentWeights

section RowGroups

variable {R M N E B A J : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]

/-- A group built from chosen lifts of linear row values, with the other input
components in `offset`.  `build` may compose factor polynomials, multiply them,
and take a canonical truncation.  It is one fixed function of the beta values. -/
def rowGroup (rows : J → M →ₗ[R] E) (offset : N → J → E)
    (lift : E → B) (build : (J → B) → A) (x : M) (y : N) : A :=
  build (fun j => lift (rows j x + offset y j))

/-- Linear annihilation gives exact group independence, even for an arbitrary
lift and arbitrary fixed symbolic construction from the lifted parameters. -/
theorem rowGroup_add_invariant (rows : J → M →ₗ[R] E) (offset : N → J → E)
    (lift : E → B) (build : (J → B) → A) (K : Submodule R M)
    (hK : ∀ j, K ≤ LinearMap.ker (rows j)) (x : M) (y : N) (k : K) :
    rowGroup rows offset lift build (x + k) y =
      rowGroup rows offset lift build x y := by
  unfold rowGroup
  apply congrArg build
  funext j
  have hk : rows j (k : M) = 0 := hK j k.property
  rw [map_add, hk, add_zero]

end RowGroups

section LiftedRows

variable {R M E Λ Q J : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [CommRing E] [Module R E] [CommRing Λ]

/-- Build a symbolic group directly from the lifted rows and fixed residue
section of `CosetInvariance`.  Nonlinear coordinate representatives are allowed. -/
def liftedRowGroup (ρ : Λ →+* E) (rows : J → M →ₗ[R] E)
    (lifted : ∀ j, CosetInvariance.LiftedRow ρ (rows j))
    (s : CosetInvariance.ResidueSection ρ) (build : (J → Λ) → Q) (x : M) : Q :=
  build (fun j => (lifted j).beta s x)

/-- Exact beta constancy passes through any fixed symbolic construction,
including polynomial composition, products, and canonical truncation. -/
theorem liftedRowGroup_add_invariant (ρ : Λ →+* E) (rows : J → M →ₗ[R] E)
    (lifted : ∀ j, CosetInvariance.LiftedRow ρ (rows j))
    (s : CosetInvariance.ResidueSection ρ) (build : (J → Λ) → Q)
    (K : Submodule R M) (hK : ∀ j, K ≤ LinearMap.ker (rows j))
    (x : M) (k : K) :
    liftedRowGroup ρ rows lifted s build (x + k) =
      liftedRowGroup ρ rows lifted s build x := by
  apply congrArg build
  funext j
  exact (lifted j).beta_add_invariant s K (hK j) x k.property

/-- Equivalent form for two arbitrary representatives of one fixed coset. -/
theorem liftedRowGroup_eq_of_sub_mem (ρ : Λ →+* E) (rows : J → M →ₗ[R] E)
    (lifted : ∀ j, CosetInvariance.LiftedRow ρ (rows j))
    (s : CosetInvariance.ResidueSection ρ) (build : (J → Λ) → Q)
    (K : Submodule R M) (hK : ∀ j, K ≤ LinearMap.ker (rows j))
    {x y : M} (hxy : y - x ∈ K) :
    liftedRowGroup ρ rows lifted s build y =
      liftedRowGroup ρ rows lifted s build x := by
  apply congrArg build
  funext j
  exact (lifted j).beta_invariant s K (hK j) hxy

end LiftedRows

section Cosets

variable {A R M N : Type*} [CommSemiring A] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Actual submodule-coset sums, enumerated by their submodule elements.
The hypotheses state translation invariance of each symbolic group along
its own submodule and pointwise factorization of the exact weight. -/
theorem coset_weighted_separation (K₀ : Submodule R M) (K₁ : Submodule R N)
    [Fintype K₀] [Fintype K₁] (r₀ : M) (r₁ : N)
    (A₀ A₁ : M → N → A) (w : M → N → A)
    (c : A) (w₀ : M → A) (w₁ : N → A)
    (h₀ : ∀ x y (k : K₀), A₀ (x + k) y = A₀ x y)
    (h₁ : ∀ x y (k : K₁), A₁ x (y + k) = A₁ x y)
    (hw : ∀ x y, w x y = c * w₀ x * w₁ y) :
    (∑ k₀ : K₀, ∑ k₁ : K₁,
      w (r₀ + k₀) (r₁ + k₁) * A₀ (r₀ + k₀) (r₁ + k₁) *
        A₁ (r₀ + k₀) (r₁ + k₁)) =
      c * (∑ k₀ : K₀, w₀ (r₀ + k₀) * A₁ (r₀ + k₀) r₁) *
        (∑ k₁ : K₁, w₁ (r₁ + k₁) * A₀ r₀ (r₁ + k₁)) := by
  calc
    _ = ∑ k₀ : K₀, ∑ k₁ : K₁,
        c * w₀ (r₀ + k₀) * w₁ (r₁ + k₁) * A₀ r₀ (r₁ + k₁) *
          A₁ (r₀ + k₀) r₁ := by
      apply Finset.sum_congr rfl
      intro k₀ hk₀
      apply Finset.sum_congr rfl
      intro k₁ hk₁
      rw [hw, h₀, h₁]
    _ = _ := separated_sum Finset.univ Finset.univ c
      (fun k₀ : K₀ => w₀ (r₀ + k₀)) (fun k₁ : K₁ => w₁ (r₁ + k₁))
      (fun k₁ : K₁ => A₀ r₀ (r₁ + k₁)) (fun k₀ : K₀ => A₁ (r₀ + k₀) r₁)

/-- A direct connection from annihilating linear rows to (4.8).
The group constructors can be actual symbolic polynomial constructions.
Their invariance is proved from the row kernels, rather than supplied as an
assumption about the resulting sums or resulting group values. -/
theorem coset_row_group_separation {E B J₀ J₁ : Type*}
    [AddCommGroup E] [Module R E]
    (K₀ : Submodule R M) (K₁ : Submodule R N)
    [Fintype K₀] [Fintype K₁] (r₀ : M) (r₁ : N)
    (rows₀ : J₀ → M →ₗ[R] E) (rows₁ : J₁ → N →ₗ[R] E)
    (offset₀ : N → J₀ → E) (offset₁ : M → J₁ → E)
    (hK₀ : ∀ j, K₀ ≤ LinearMap.ker (rows₀ j))
    (hK₁ : ∀ j, K₁ ≤ LinearMap.ker (rows₁ j))
    (lift : E → B) (build₀ : (J₀ → B) → A) (build₁ : (J₁ → B) → A)
    (w : M → N → A) (c : A) (w₀ : M → A) (w₁ : N → A)
    (hw : ∀ x y, w x y = c * w₀ x * w₁ y) :
    let A₀ := rowGroup rows₀ offset₀ lift build₀
    let A₁ := fun x y => rowGroup rows₁ offset₁ lift build₁ y x
    (∑ k₀ : K₀, ∑ k₁ : K₁,
      w (r₀ + k₀) (r₁ + k₁) * A₀ (r₀ + k₀) (r₁ + k₁) *
        A₁ (r₀ + k₀) (r₁ + k₁)) =
      c * (∑ k₀ : K₀, w₀ (r₀ + k₀) * A₁ (r₀ + k₀) r₁) *
        (∑ k₁ : K₁, w₁ (r₁ + k₁) * A₀ r₀ (r₁ + k₁)) := by
  exact coset_weighted_separation K₀ K₁ r₀ r₁
    (rowGroup rows₀ offset₀ lift build₀)
    (fun x y => rowGroup rows₁ offset₁ lift build₁ y x) w c w₀ w₁
    (fun x y k => rowGroup_add_invariant rows₀ offset₀ lift build₀ K₀ hK₀ x y k)
    (fun x y k => rowGroup_add_invariant rows₁ offset₁ lift build₁ K₁ hK₁ y x k) hw

end Cosets

section CompleteCosetEnumeration

open CosetCardinality

variable {A 𝔽 Vstar V₀ V₁ : Type*} [CommSemiring A] [Field 𝔽]
  [Fintype Vstar]
  [AddCommGroup V₀] [Module 𝔽 V₀] [Fintype V₀]
  [AddCommGroup V₁] [Module 𝔽 V₁] [Fintype V₁]
  (K₀ : Submodule 𝔽 V₀) (K₁ : Submodule 𝔽 V₁)
  [Fintype (V₀ ⧸ K₀)] [Fintype (V₁ ⧸ K₁)]
  [∀ q, Fintype (CosetFiber K₀ q)] [∀ q, Fintype (CosetFiber K₁ q)]

/-- The outer-data enumeration covers the full split assignment space exactly
once. This is proved using the actual quotient-fiber equivalence. -/
theorem coset_sum_decomposition (f : Vstar × V₀ × V₁ → A) :
    (∑ z, f z) =
      ∑ o : OuterData (Vstar := Vstar) K₀ K₁,
        ∑ x : CosetFiber K₀ o.2.1, ∑ y : CosetFiber K₁ o.2.2,
          f (o.1, x.val, y.val) :=
  sum_reindex_fibers (outerFiberEquiv (Vstar := Vstar) K₀ K₁) f

/-- Full assignment-to-separated-coset identity. The group assumptions are
pointwise invariance under differences in the specified submodules; the
actual quotient partition and the separated finite summation are both proved. -/
theorem coset_full_weighted_separation
    (r₀ : ∀ q, CosetFiber K₀ q) (r₁ : ∀ q, CosetFiber K₁ q)
    (A₀ A₁ w : Vstar × V₀ × V₁ → A)
    (c : Vstar → A) (w₀ : V₀ → A) (w₁ : V₁ → A)
    (h₀ : ∀ o x x' y, x' - x ∈ K₀ → A₀ (o, x, y) = A₀ (o, x', y))
    (h₁ : ∀ o x y y', y' - y ∈ K₁ → A₁ (o, x, y) = A₁ (o, x, y'))
    (hw : ∀ o x y, w (o, x, y) = c o * w₀ x * w₁ y) :
    (∑ z, w z * A₀ z * A₁ z) =
      ∑ o : OuterData (Vstar := Vstar) K₀ K₁,
        c o.1 *
          (∑ x : CosetFiber K₀ o.2.1,
            w₀ x.val * A₁ (o.1, x.val, (r₁ o.2.2).val)) *
          (∑ y : CosetFiber K₁ o.2.2,
            w₁ y.val * A₀ (o.1, (r₀ o.2.1).val, y.val)) := by
  refine weighted_separation_equiv (outerFiberEquiv (Vstar := Vstar) K₀ K₁)
    (fun o => r₀ o.2.1) (fun o => r₁ o.2.2) A₀ A₁ w (fun o => c o.1)
    (fun _ x => w₀ x.val) (fun _ y => w₁ y.val) ?_ ?_ ?_
  · intro o x x' y
    exact h₀ o.1 x.val x'.val y.val
      ((Submodule.Quotient.eq K₀).1 (x'.property.trans x.property.symm))
  · intro o x y y'
    exact h₁ o.1 x.val y.val y'.val
      ((Submodule.Quotient.eq K₁).1 (y'.property.trans y.property.symm))
  · intro o x y
    exact hw o.1 x.val y.val

end CompleteCosetEnumeration

end SubexponentialSAT.Separation

end OAI.Algorithms
