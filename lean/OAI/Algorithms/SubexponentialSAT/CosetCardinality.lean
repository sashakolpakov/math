import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Cardinalities for the separated coset enumeration

The outer data are a vector on the complementary coordinates and one quotient
class on each of two coordinate blocks. The inner data are actual vectors in
those quotient classes. These theorems establish their exact cardinalities and
the algebraic identity in equation (4.9). They do not assert a bit-complexity
bound for enumerating a basis, a quotient, or the symbolic ring.
-/

namespace SubexponentialSAT.CosetCardinality

open Module

section Modules

variable {𝔽 V W : Type*} [Field 𝔽]
  [AddCommGroup V] [Module 𝔽 V] [AddCommGroup W] [Module 𝔽 W]

/-- Linear equivalences preserve the cardinality of the underlying set. -/
theorem card_of_linearEquiv (e : V ≃ₗ[𝔽] W) : Nat.card V = Nat.card W :=
  Nat.card_congr e.toEquiv

/-- A finite-dimensional space has a linear coordinate system with exactly
`finrank` coordinates. The basis choice here carries no algorithmic cost claim. -/
noncomputable def finiteCoordinateEquiv [Module.Finite 𝔽 V] :
    V ≃ₗ[𝔽] (Fin (finrank 𝔽 V) → 𝔽) :=
  (Module.finBasis 𝔽 V).equivFun

/-- The cardinality formula for a finite-dimensional vector space. -/
theorem card_module [Module.Finite 𝔽 V] :
    Nat.card V = Nat.card 𝔽 ^ finrank 𝔽 V := by
  let b := Module.finBasis 𝔽 V
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The size of an inner subspace is the field size to its dimension. -/
theorem card_submodule [Module.Finite 𝔽 V] (K : Submodule 𝔽 V) :
    Nat.card K = Nat.card 𝔽 ^ finrank 𝔽 K :=
  card_module

/-- The number of cosets in a coordinate block. -/
theorem card_quotient [Module.Finite 𝔽 V] (K : Submodule 𝔽 V) :
    Nat.card (V ⧸ K) = Nat.card 𝔽 ^ (finrank 𝔽 V - finrank 𝔽 K) := by
  rw [card_module (𝔽 := 𝔽), Submodule.finrank_quotient]

/-- A coset is represented as the fiber of the actual quotient map. -/
def CosetFiber (K : Submodule 𝔽 V) (q : V ⧸ K) :=
  {x : V // (Submodule.Quotient.mk x : V ⧸ K) = q}

/-- Taking a quotient class together with a point of that class partitions the
ambient vector space exactly, without duplicates or omitted vectors. -/
def quotientFiberEquiv (K : Submodule 𝔽 V) :
    (Σ q : V ⧸ K, CosetFiber K q) ≃ V :=
  Equiv.sigmaFiberEquiv (fun x : V => (Submodule.Quotient.mk x : V ⧸ K))

/-- Translating the subspace by any representative enumerates its coset
bijectively, even when the field elements are later represented by integers. -/
def cosetEquiv (K : Submodule 𝔽 V) (q : V ⧸ K) (r : V)
    (hr : (Submodule.Quotient.mk r : V ⧸ K) = q) : K ≃ CosetFiber K q where
  toFun k := ⟨r + k, by
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero K).2 k.property,
      add_zero, hr]⟩
  invFun x := ⟨x.val - r, (Submodule.Quotient.eq K).1 (x.property.trans hr.symm)⟩
  left_inv k := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp []

/-- Every quotient class has the same cardinality as its subspace. -/
theorem card_coset_eq (K : Submodule 𝔽 V) (q : V ⧸ K) :
    Nat.card (CosetFiber K q) = Nat.card K := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (p := K) q
  exact Nat.card_congr (cosetEquiv K q r hr).symm

/-- Every inner sum over a coset has exactly this many terms. -/
theorem card_coset [Module.Finite 𝔽 V] (K : Submodule 𝔽 V) (q : V ⧸ K) :
    Nat.card (CosetFiber K q) = Nat.card 𝔽 ^ finrank 𝔽 K := by
  rw [card_coset_eq, card_submodule]

/-- Fintype-facing version for finite sums indexed directly by subspace vectors. -/
theorem fintype_card_submodule [Fintype 𝔽] [Fintype V] (K : Submodule 𝔽 V)
    [Fintype K] : Fintype.card K = Fintype.card 𝔽 ^ finrank 𝔽 K := by
  simpa only [Nat.card_eq_fintype_card] using card_submodule K

end Modules

section OuterData

variable {𝔽 Vstar V0 V1 : Type*} [Field 𝔽]
  [AddCommGroup Vstar] [Module 𝔽 Vstar]
  [AddCommGroup V0] [Module 𝔽 V0] [AddCommGroup V1] [Module 𝔽 V1]

/-- The actual type of outer choices used in Section 4.5. -/
abbrev OuterData (K0 : Submodule 𝔽 V0) (K1 : Submodule 𝔽 V1) :=
  Vstar × (V0 ⧸ K0) × (V1 ⧸ K1)

/-- Every split assignment is uniquely an outer datum and a pair of vectors
in its two cosets. This is the full-domain partition behind the enumeration. -/
def outerFiberEquiv (K0 : Submodule 𝔽 V0) (K1 : Submodule 𝔽 V1) :
    (Vstar × V0 × V1) ≃
      Σ o : OuterData (Vstar := Vstar) K0 K1,
        CosetFiber K0 o.2.1 × CosetFiber K1 o.2.2 where
  toFun x := ⟨(x.1, Submodule.Quotient.mk x.2.1, Submodule.Quotient.mk x.2.2),
    ⟨x.2.1, rfl⟩, ⟨x.2.2, rfl⟩⟩
  invFun y := (y.1.1, y.2.1.val, y.2.2.val)
  left_inv _ := rfl
  right_inv y := by
    rcases y with ⟨⟨xs, q0, q1⟩, ⟨x0, h0⟩, ⟨x1, h1⟩⟩
    dsimp at h0 h1
    subst q0
    subst q1
    rfl

/-- Product cardinality gives the number of outer choices. -/
theorem card_outer [Module.Finite 𝔽 Vstar] [Module.Finite 𝔽 V0]
    [Module.Finite 𝔽 V1] (K0 : Submodule 𝔽 V0) (K1 : Submodule 𝔽 V1) :
    Nat.card (OuterData (Vstar := Vstar) K0 K1) = Nat.card 𝔽 ^
      (finrank 𝔽 Vstar + finrank 𝔽 V0 + finrank 𝔽 V1 -
        finrank 𝔽 K0 - finrank 𝔽 K1) := by
  have h0 := K0.finrank_quotient_add_finrank
  have h1 := K1.finrank_quotient_add_finrank
  simp only [OuterData, Nat.card_prod, card_quotient]
  rw [card_module (𝔽 := 𝔽) (V := Vstar)]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- The arithmetic identity behind equation (4.9). The dimension assumption
is essential when subtraction is natural-number subtraction. -/
theorem iteration_identity (p D d0 d1 : ℕ) (h : d0 + d1 ≤ D) :
    p ^ (D - d0 - d1) * (p ^ d0 + p ^ d1) =
      p ^ (D - d1) + p ^ (D - d0) := by
  rw [Nat.mul_add, ← pow_add, ← pow_add]
  congr 1 <;> congr 1 <;> omega

/-- An integer-exponent version of the final inequality in (4.9).
The hypotheses express `d0,d1 ≥ D/4` without rounding ambiguity. -/
theorem iteration_bound (p D d0 d1 : ℕ) (hp : 0 < p)
    (h : d0 + d1 ≤ D) (h0 : D ≤ 4 * d0) (h1 : D ≤ 4 * d1) :
    p ^ (D - d0 - d1) * (p ^ d0 + p ^ d1) ≤ 2 * p ^ (3 * D / 4) := by
  rw [iteration_identity p D d0 d1 h, two_mul]
  exact Nat.add_le_add
    (Nat.pow_le_pow_right hp (by omega : D - d1 ≤ 3 * D / 4))
    (Nat.pow_le_pow_right hp (by omega : D - d0 ≤ 3 * D / 4))

/-- Counting each term in each of the two inner sums for every outer datum.
This is an iteration count, not a Turing-machine runtime theorem. -/
theorem card_outer_times_inner [Module.Finite 𝔽 Vstar] [Module.Finite 𝔽 V0]
    [Module.Finite 𝔽 V1] (K0 : Submodule 𝔽 V0) (K1 : Submodule 𝔽 V1) :
    Nat.card (OuterData (Vstar := Vstar) K0 K1) * (Nat.card K0 + Nat.card K1) =
      Nat.card 𝔽 ^ (finrank 𝔽 Vstar + finrank 𝔽 V0 + finrank 𝔽 V1 - finrank 𝔽 K1) +
      Nat.card 𝔽 ^ (finrank 𝔽 Vstar + finrank 𝔽 V0 + finrank 𝔽 V1 - finrank 𝔽 K0) := by
  rw [card_outer, card_submodule, card_submodule]
  apply iteration_identity
  have h0 := K0.finrank_quotient_add_finrank
  have h1 := K1.finrank_quotient_add_finrank
  omega

end OuterData

section Coordinates

variable {𝔽 ι : Type*} [Field 𝔽] [Fintype ι] [DecidableEq ι]

/-- The disjoint coordinate supports and their complement split every ambient
assignment uniquely. This map is the actual restriction of coordinates. -/
def coordinateSplitEquiv (S0 S1 : Finset ι) (h : Disjoint S0 S1) :
    (ι → 𝔽) ≃ₗ[𝔽] ((↥((S0 ∪ S1)ᶜ) → 𝔽) × (S0 → 𝔽) × (S1 → 𝔽)) where
  toFun x := (fun i => x i.val, fun i => x i.val, fun i => x i.val)
  invFun y i := if h0 : i ∈ S0 then y.2.1 ⟨i, h0⟩
    else if h1 : i ∈ S1 then y.2.2 ⟨i, h1⟩
    else y.1 ⟨i, by simp only [Finset.mem_compl, Finset.mem_union, not_or]; exact ⟨h0, h1⟩⟩
  left_inv x := by
    funext i
    dsimp
    split
    · rfl
    · split <;> rfl
  right_inv y := by
    apply Prod.ext
    · funext i
      have hi : i.val ∉ S0 ∧ i.val ∉ S1 := by
        simpa only [Finset.mem_compl, Finset.mem_union, not_or] using i.property
      dsimp
      simp only [dite_eq_right hi.1, dite_eq_right hi.2]
    · apply Prod.ext
      · funext i
        dsimp
        simp only [dite_eq_left i.property]
      · funext i
        have hi0 : i.val ∉ S0 := fun hi => Finset.disjoint_left.mp h hi i.property
        dsimp
        simp only [dite_eq_right hi0, dite_eq_left i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Three disjoint coordinate blocks account for the full ambient dimension. -/
theorem coordinate_card_partition (S0 S1 : Finset ι) (h : Disjoint S0 S1) :
    Fintype.card ↥((S0 ∪ S1)ᶜ) + Fintype.card ↥S0 + Fintype.card ↥S1 =
      Fintype.card ι := by
  simpa only [Fintype.card_coe, Finset.card_union_of_disjoint h, Nat.add_assoc]
    using Finset.card_compl_add_card (S0 ∪ S1)

/-- Restricting each subspace to its own coordinate support is represented by
the local domains `S0 → 𝔽` and `S1 → 𝔽`. -/
abbrev CoordinateOuterData (S0 S1 : Finset ι)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :=
  OuterData (Vstar := ↥((S0 ∪ S1)ᶜ) → 𝔽) K0 K1

/-- A complete ambient assignment is an outer datum and a point in each of
its two cosets, through explicit coordinate restriction and quotient fibers. -/
def coordinateOuterFiberEquiv (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    (ι → 𝔽) ≃ Σ o : CoordinateOuterData S0 S1 K0 K1,
      CosetFiber K0 o.2.1 × CosetFiber K1 o.2.2 :=
  (coordinateSplitEquiv S0 S1 h).toEquiv.trans (outerFiberEquiv K0 K1)

/-- Reconstruct an ambient assignment from its outer data and two coset points. -/
def coordinateReconstruct (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽))
    (o : CoordinateOuterData S0 S1 K0 K1)
    (x0 : CosetFiber K0 o.2.1) (x1 : CosetFiber K1 o.2.2) : ι → 𝔽 :=
  (coordinateOuterFiberEquiv S0 S1 h K0 K1).symm ⟨o, x0, x1⟩

/-- Reconstructing an assignment gives exactly its three supplied coordinate blocks. -/
theorem coordinateReconstruct_components (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽))
    (o : CoordinateOuterData S0 S1 K0 K1)
    (x0 : CosetFiber K0 o.2.1) (x1 : CosetFiber K1 o.2.2) :
    (fun i : ↥((S0 ∪ S1)ᶜ) => coordinateReconstruct S0 S1 h K0 K1 o x0 x1 i.val) = o.1 ∧
    (fun i : S0 => coordinateReconstruct S0 S1 h K0 K1 o x0 x1 i.val) = x0.val ∧
    (fun i : S1 => coordinateReconstruct S0 S1 h K0 K1 o x0 x1 i.val) = x1.val := by
  have hs := (coordinateSplitEquiv (𝔽 := 𝔽) S0 S1 h).apply_symm_apply
    (o.1, x0.val, x1.val)
  exact ⟨congrArg Prod.fst hs, congrArg (fun z => z.2.1) hs,
    congrArg (fun z => z.2.2) hs⟩

/-- The exact outer count for disjoint coordinate supports, with `D` given by
the cardinality of the original coordinate type. -/
theorem card_coordinate_outer (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    Nat.card (CoordinateOuterData S0 S1 K0 K1) =
      Nat.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K0 - finrank 𝔽 K1) := by
  rw [card_outer]
  simp only [Module.finrank_fintype_fun_eq_card]
  rw [coordinate_card_partition S0 S1 h]

/-- Over a finite field the outer data themselves form a finite type, with
the expected power of the actual field cardinality. -/
theorem fintype_card_coordinate_outer [Fintype 𝔽] (S0 S1 : Finset ι)
    (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    Fintype.card (CoordinateOuterData S0 S1 K0 K1) =
      Fintype.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K0 - finrank 𝔽 K1) := by
  simpa only [Nat.card_eq_fintype_card] using card_coordinate_outer S0 S1 h K0 K1

/-- Disjoint supports bound the sum of the two inner dimensions by the
ambient number of coordinates. -/
theorem coordinate_dimensions_le (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    finrank 𝔽 K0 + finrank 𝔽 K1 ≤ Fintype.card ι := by
  have h0 := K0.finrank_quotient_add_finrank
  have h1 := K1.finrank_quotient_add_finrank
  have hp := coordinate_card_partition S0 S1 h
  simp only [Module.finrank_fintype_fun_eq_card] at h0 h1
  omega

/-- Equation (4.9), before the real-valued `3D/4` estimate: the outer count
times the two inner sizes is the sum of these two powers. -/
theorem coordinate_iteration_count (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    Nat.card (CoordinateOuterData S0 S1 K0 K1) * (Nat.card K0 + Nat.card K1) =
      Nat.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K1) +
      Nat.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K0) := by
  rw [card_outer_times_inner]
  simp only [Module.finrank_fintype_fun_eq_card]
  rw [coordinate_card_partition S0 S1 h]

/-- The iteration formula counts a concrete type: an outer choice, followed
by either an index for the first inner sum or an index for the second. -/
theorem card_coordinate_iteration_type [Fintype 𝔽] (S0 S1 : Finset ι)
    (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽)) :
    Nat.card (CoordinateOuterData S0 S1 K0 K1 × (K0 ⊕ K1)) =
      Fintype.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K1) +
      Fintype.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K0) := by
  rw [Nat.card_prod, Nat.card_sum]
  simpa only [Nat.card_eq_fintype_card] using
    coordinate_iteration_count S0 S1 h K0 K1

/-- The complete integer-cardinality bound in (4.9). The exponent is the
floor of `3D/4`, so this is slightly sharper than its real-exponent version. -/
theorem coordinate_iteration_bound [Fintype 𝔽] (S0 S1 : Finset ι)
    (h : Disjoint S0 S1)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽))
    (h0 : Fintype.card ι ≤ 4 * finrank 𝔽 K0)
    (h1 : Fintype.card ι ≤ 4 * finrank 𝔽 K1) :
    Nat.card (CoordinateOuterData S0 S1 K0 K1) * (Nat.card K0 + Nat.card K1) ≤
      2 * Fintype.card 𝔽 ^ (3 * Fintype.card ι / 4) := by
  rw [card_coordinate_outer S0 S1 h, card_submodule, card_submodule]
  simp only [Nat.card_eq_fintype_card]
  exact iteration_bound _ _ _ _ Fintype.card_pos
    (coordinate_dimensions_le S0 S1 h K0 K1) h0 h1

omit [DecidableEq ι] in
/-- The sizes of the actual two cosets used for any outer choice. -/
theorem coordinate_inner_sizes (S0 S1 : Finset ι)
    (K0 : Submodule 𝔽 (S0 → 𝔽)) (K1 : Submodule 𝔽 (S1 → 𝔽))
    (q0 : (S0 → 𝔽) ⧸ K0) (q1 : (S1 → 𝔽) ⧸ K1) :
    Nat.card (CosetFiber K0 q0) = Nat.card 𝔽 ^ finrank 𝔽 K0 ∧
      Nat.card (CosetFiber K1 q1) = Nat.card 𝔽 ^ finrank 𝔽 K1 :=
  ⟨card_coset K0 q0, card_coset K1 q1⟩

/-- Restriction of an ambient subspace to a selected set of coordinates. -/
def coordinateRestriction (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽)) :
    K →ₗ[𝔽] (S → 𝔽) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
/-- Restriction loses no information for a subspace supported on `S`. -/
theorem coordinateRestriction_injective (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0) :
    Function.Injective (coordinateRestriction S K) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S
  · exact congrFun hxy ⟨i, hi⟩
  · rw [hK x.val x.property i hi, hK y.val y.property i hi]

/-- The same supported subspace, viewed as a subspace of its local coordinates. -/
abbrev restrictedSubspace (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽)) :
    Submodule 𝔽 (S → 𝔽) :=
  LinearMap.range (coordinateRestriction S K)

/-- Ambient and local presentations of a supported subspace are linearly equivalent. -/
noncomputable def restrictionEquiv (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0) :
    K ≃ₗ[𝔽] restrictedSubspace S K :=
  LinearEquiv.ofInjective (coordinateRestriction S K)
    (coordinateRestriction_injective S K hK)

omit [Fintype ι] in
theorem finrank_restrictedSubspace (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0) :
    finrank 𝔽 (restrictedSubspace S K) = finrank 𝔽 K :=
  (restrictionEquiv S K hK).finrank_eq.symm

/-- The outer-count theorem with precisely the ambient-subspace support
hypotheses of the interpolation layout. -/
theorem card_supported_outer (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 K1 : Submodule 𝔽 (ι → 𝔽))
    (h0 : ∀ x ∈ K0, ∀ i, i ∉ S0 → x i = 0)
    (h1 : ∀ x ∈ K1, ∀ i, i ∉ S1 → x i = 0) :
    Nat.card (CoordinateOuterData S0 S1
      (restrictedSubspace S0 K0) (restrictedSubspace S1 K1)) =
      Nat.card 𝔽 ^ (Fintype.card ι - finrank 𝔽 K0 - finrank 𝔽 K1) := by
  rw [card_coordinate_outer S0 S1 h,
    finrank_restrictedSubspace S0 K0 h0, finrank_restrictedSubspace S1 K1 h1]

omit [Fintype ι] in
/-- A supported ambient vector whose restriction lies in the restricted
subspace already lies in the original ambient subspace. -/
theorem mem_of_restriction_mem (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0) (x : ι → 𝔽)
    (hx : ∀ i, i ∉ S → x i = 0)
    (hr : (fun i : S => x i.val) ∈ restrictedSubspace S K) : x ∈ K := by
  obtain ⟨r, hr⟩ := hr
  have heq : x = r.val := by
    funext i
    by_cases hi : i ∈ S
    · exact (congrFun hr ⟨i, hi⟩).symm
    · rw [hx i hi, hK r.val r.property i hi]
  exact heq.symm ▸ r.property

omit [Fintype ι] in
/-- Equal restrictions modulo the local subspace and equality outside its
support imply that the ambient difference belongs to the original subspace. -/
theorem sub_mem_of_local_quotient_eq (S : Finset ι) (K : Submodule 𝔽 (ι → 𝔽))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0) (x y : ι → 𝔽)
    (houtside : ∀ i, i ∉ S → x i = y i)
    (hq : (Submodule.Quotient.mk (fun i : S => x i.val) :
      (S → 𝔽) ⧸ restrictedSubspace S K) =
      Submodule.Quotient.mk (fun i : S => y i.val)) : x - y ∈ K := by
  apply mem_of_restriction_mem S K hK (x - y)
  · intro i hi
    exact sub_eq_zero.mpr (houtside i hi)
  · exact (Submodule.Quotient.eq (restrictedSubspace S K)).mp hq

/-- With outer data and the right point fixed, varying the left point within
its local coset changes the ambient assignment by a vector of the global `K0`. -/
theorem coordinateReconstruct_left_sub_mem (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 K1 : Submodule 𝔽 (ι → 𝔽))
    (hK0 : ∀ x ∈ K0, ∀ i, i ∉ S0 → x i = 0)
    (o : CoordinateOuterData S0 S1 (restrictedSubspace S0 K0) (restrictedSubspace S1 K1))
    (x0 y0 : CosetFiber (restrictedSubspace S0 K0) o.2.1)
    (x1 : CosetFiber (restrictedSubspace S1 K1) o.2.2) :
    coordinateReconstruct S0 S1 h _ _ o x0 x1 -
      coordinateReconstruct S0 S1 h _ _ o y0 x1 ∈ K0 := by
  have hx := coordinateReconstruct_components S0 S1 h _ _ o x0 x1
  have hy := coordinateReconstruct_components S0 S1 h _ _ o y0 x1
  apply sub_mem_of_local_quotient_eq S0 K0 hK0
  · intro i hi0
    by_cases hi1 : i ∈ S1
    · exact congrFun (hx.2.2.trans hy.2.2.symm) ⟨i, hi1⟩
    · exact congrFun (hx.1.trans hy.1.symm)
        ⟨i, by simp only [Finset.mem_compl, Finset.mem_union, not_or]; exact ⟨hi0, hi1⟩⟩
  · rw [hx.2.1, hy.2.1]
    exact x0.property.trans y0.property.symm

/-- The symmetric global-subspace difference statement for the right point. -/
theorem coordinateReconstruct_right_sub_mem (S0 S1 : Finset ι) (h : Disjoint S0 S1)
    (K0 K1 : Submodule 𝔽 (ι → 𝔽))
    (hK1 : ∀ x ∈ K1, ∀ i, i ∉ S1 → x i = 0)
    (o : CoordinateOuterData S0 S1 (restrictedSubspace S0 K0) (restrictedSubspace S1 K1))
    (x0 : CosetFiber (restrictedSubspace S0 K0) o.2.1)
    (x1 y1 : CosetFiber (restrictedSubspace S1 K1) o.2.2) :
    coordinateReconstruct S0 S1 h _ _ o x0 x1 -
      coordinateReconstruct S0 S1 h _ _ o x0 y1 ∈ K1 := by
  have hx := coordinateReconstruct_components S0 S1 h _ _ o x0 x1
  have hy := coordinateReconstruct_components S0 S1 h _ _ o x0 y1
  apply sub_mem_of_local_quotient_eq S1 K1 hK1
  · intro i hi1
    by_cases hi0 : i ∈ S0
    · exact congrFun (hx.2.1.trans hy.2.1.symm) ⟨i, hi0⟩
    · exact congrFun (hx.1.trans hy.1.symm)
        ⟨i, by simp only [Finset.mem_compl, Finset.mem_union, not_or]; exact ⟨hi0, hi1⟩⟩
  · rw [hx.2.2, hy.2.2]
    exact x1.property.trans y1.property.symm

end Coordinates

end SubexponentialSAT.CosetCardinality

end OAI.Algorithms
