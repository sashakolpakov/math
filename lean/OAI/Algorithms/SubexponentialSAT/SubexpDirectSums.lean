import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DirectSums

namespace OAI.Algorithms

/-!
# Arbitrary-color supported direct sums

The coordinate split is an actual linear equivalence: it restricts to each
pairwise-disjoint color support and to their complement. Its inverse is the
sum of the zero-extended pieces. A separate map realizes the direct sum of
any subspaces supported on those sets and proves exact additivity of dimension.
-/

namespace SubexponentialSAT.SubexpDirectSums

open Module
open scoped BigOperators

section CoordinateSplit

variable {K A G : Type*} [Field K] [Fintype A] [DecidableEq A] [Fintype G]

/-- Zero extension from one finite coordinate support. -/
noncomputable def coordinateExtend (S : Finset A) : (S → K) →ₗ[K] (A → K) :=
  DirectSums.extendLinear (Function.Embedding.subtype (fun a => a ∈ S))

omit [Fintype A] [DecidableEq A] in
@[simp] theorem coordinateExtend_apply (S : Finset A) (x : S → K)
    (a : A) (ha : a ∈ S) : coordinateExtend S x a = x ⟨a, ha⟩ := by
  exact DirectSums.extendLinear_apply
    (Function.Embedding.subtype (fun a => a ∈ S)) x (⟨a, ha⟩ : S)

omit [Fintype A] [DecidableEq A] in
theorem coordinateExtend_zero (S : Finset A) (x : S → K)
    (a : A) (ha : a ∉ S) : coordinateExtend S x a = 0 := by
  apply DirectSums.extendLinear_zero_outside
  rintro ⟨b, hb⟩
  exact ha (hb ▸ b.property)

omit [Fintype A] [DecidableEq A] in
/-- Restricting a supported vector and extending it back loses no information. -/
theorem coordinateExtend_restrict (S : Finset A) (x : A → K)
    (hx : ∀ a, a ∉ S → x a = 0) :
    coordinateExtend S (fun a : S => x a.val) = x := by
  funext a
  by_cases ha : a ∈ S
  · exact coordinateExtend_apply _ _ _ ha
  · rw [coordinateExtend_zero _ _ _ ha, hx a ha]

/-- Sum all zero-extended color pieces. -/
noncomputable def colorAssemble (S : G → Finset A) :
    ((g : G) → S g → K) →ₗ[K] (A → K) where
  toFun x := ∑ g, coordinateExtend (S g) (x g)
  map_add' x y := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem colorAssemble_apply (S : G → Finset A)
    (x : (g : G) → S g → K) (a : A) :
    colorAssemble S x a = ∑ g, coordinateExtend (S g) (x g) a := by
  simp only [colorAssemble, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]

omit [Fintype A] [DecidableEq A] in
theorem colorAssemble_on_color (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (x : (g : G) → S g → K) (g : G) (a : A) (ha : a ∈ S g) :
    colorAssemble S x a = x g ⟨a, ha⟩ := by
  classical
  rw [colorAssemble_apply, Finset.sum_eq_single g]
  · exact coordinateExtend_apply _ _ _ ha
  · intro h _ hh
    apply coordinateExtend_zero
    intro hah
    exact Finset.disjoint_left.mp (hS (Ne.symm hh)) ha hah
  · simp

omit [Fintype A] in
theorem colorAssemble_outside (S : G → Finset A)
    (x : (g : G) → S g → K) (a : A)
    (ha : a ∉ Finset.univ.biUnion S) : colorAssemble S x a = 0 := by
  rw [colorAssemble_apply]
  apply Finset.sum_eq_zero
  intro g _
  apply coordinateExtend_zero
  intro hag
  exact ha (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hag⟩)

/-- Reconstruct all coordinates from the complement piece and the color pieces. -/
noncomputable def coordinateAssemble (S : G → Finset A) :
    ((↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K)) →ₗ[K] (A → K) :=
  (coordinateExtend ((Finset.univ.biUnion S)ᶜ)).comp
      (LinearMap.fst K (↥((Finset.univ.biUnion S)ᶜ) → K) ((g : G) → S g → K)) +
    (colorAssemble S).comp
      (LinearMap.snd K (↥((Finset.univ.biUnion S)ᶜ) → K) ((g : G) → S g → K))

theorem coordinateAssemble_eq (S : G → Finset A)
    (x : (↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K)) :
    coordinateAssemble S x =
      coordinateExtend ((Finset.univ.biUnion S)ᶜ) x.1 +
        ∑ g, coordinateExtend (S g) (x.2 g) := rfl

theorem coordinateAssemble_on_color (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (x : (↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K))
    (g : G) (a : A) (ha : a ∈ S g) :
    coordinateAssemble S x a = x.2 g ⟨a, ha⟩ := by
  have hau : a ∈ Finset.univ.biUnion S :=
    Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, ha⟩
  change coordinateExtend ((Finset.univ.biUnion S)ᶜ) x.1 a +
    colorAssemble S x.2 a = _
  rw [coordinateExtend_zero _ _ _ (by simpa using hau),
    colorAssemble_on_color S hS x.2 g a ha, zero_add]

theorem coordinateAssemble_outside (S : G → Finset A)
    (x : (↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K))
    (a : A) (ha : a ∈ (Finset.univ.biUnion S)ᶜ) :
    coordinateAssemble S x a = x.1 ⟨a, ha⟩ := by
  change coordinateExtend ((Finset.univ.biUnion S)ᶜ) x.1 a +
    colorAssemble S x.2 a = _
  rw [coordinateExtend_apply _ _ _ ha,
    colorAssemble_outside S x.2 a (Finset.mem_compl.mp ha), add_zero]

/-- Restriction to disjoint coordinate supports and their complement is a
linear equivalence for every finite number of colors. -/
noncomputable def coordinateSplitEquiv (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h)) :
    (A → K) ≃ₗ[K]
      ((↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K)) where
  toFun x := (fun a => x a.val, fun _ a => x a.val)
  invFun := coordinateAssemble S
  left_inv x := by
    funext a
    by_cases ha : a ∈ Finset.univ.biUnion S
    · obtain ⟨g, _, hag⟩ := Finset.mem_biUnion.mp ha
      exact coordinateAssemble_on_color S hS _ g a hag
    · exact coordinateAssemble_outside S _ a (Finset.mem_compl.mpr ha)
  right_inv x := by
    apply Prod.ext
    · funext a
      exact coordinateAssemble_outside S x a.val a.property
    · funext g a
      exact coordinateAssemble_on_color S hS x g a.val a.property
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateSplitEquiv_apply_outside (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (x : A → K) (a : ↥((Finset.univ.biUnion S)ᶜ)) :
    (coordinateSplitEquiv S hS x).1 a = x a.val := rfl

@[simp] theorem coordinateSplitEquiv_apply_color (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (x : A → K) (g : G) (a : S g) :
    (coordinateSplitEquiv S hS x).2 g a = x a.val := rfl

@[simp] theorem coordinateSplitEquiv_symm_apply (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (x : (↥((Finset.univ.biUnion S)ᶜ) → K) × ((g : G) → S g → K)) :
    (coordinateSplitEquiv S hS).symm x = coordinateAssemble S x := rfl

/-- Exact dimension accounting for the ambient coordinate split. -/
theorem coordinate_card_partition (S : G → Finset A)
    (hS : Pairwise fun g h => Disjoint (S g) (S h)) :
    Fintype.card ↥((Finset.univ.biUnion S)ᶜ) + ∑ g, (S g).card = Fintype.card A := by
  have h := (coordinateSplitEquiv (K := ℚ) S hS).finrank_eq.symm
  simpa [Module.finrank_prod, Module.finrank_pi_fintype] using h

end CoordinateSplit

section SupportedSubspaces

variable {K A G : Type*} [Field K] [Fintype A] [Fintype G]

/-- The actual sum map from a family of ambient subspaces. -/
def subspaceSumLinear (V : G → Submodule K (A → K)) :
    ((g : G) → V g) →ₗ[K] (A → K) where
  toFun x := ∑ g, (x g).val
  map_add' _ _ := by simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype A] in
@[simp] theorem subspaceSumLinear_apply (V : G → Submodule K (A → K))
    (x : (g : G) → V g) (a : A) :
    subspaceSumLinear V x a = ∑ g, (x g).val a := by
  simp only [subspaceSumLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]

omit [Fintype A] in
theorem subspaceSumLinear_on_color (V : G → Submodule K (A → K))
    (S : G → Finset A) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (hV : ∀ g v, v ∈ V g → ∀ a, a ∉ S g → v a = 0)
    (x : (g : G) → V g) (g : G) (a : A) (ha : a ∈ S g) :
    subspaceSumLinear V x a = (x g).val a := by
  classical
  rw [subspaceSumLinear_apply, Finset.sum_eq_single g]
  · intro h _ hh
    apply hV h _ (x h).property a
    intro hah
    exact Finset.disjoint_left.mp (hS (Ne.symm hh)) ha hah
  · simp

omit [Fintype A] in
theorem subspaceSumLinear_injective (V : G → Submodule K (A → K))
    (S : G → Finset A) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (hV : ∀ g v, v ∈ V g → ∀ a, a ∉ S g → v a = 0) :
    Function.Injective (subspaceSumLinear V) := by
  intro x y hxy
  funext g
  apply Subtype.ext
  funext a
  by_cases ha : a ∈ S g
  · have h := congrFun hxy a
    rwa [subspaceSumLinear_on_color V S hS hV x g a ha,
      subspaceSumLinear_on_color V S hS hV y g a ha] at h
  · rw [hV g _ (x g).property a ha, hV g _ (y g).property a ha]

/-- The ambient sum of the color subspaces. -/
def colorSumSubspace (V : G → Submodule K (A → K)) : Submodule K (A → K) :=
  LinearMap.range (subspaceSumLinear V)

/-- Disjoint coordinate support turns the sum into a direct sum. -/
noncomputable def colorSumEquiv (V : G → Submodule K (A → K))
    (S : G → Finset A) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (hV : ∀ g v, v ∈ V g → ∀ a, a ∉ S g → v a = 0) :
    ((g : G) → V g) ≃ₗ[K] colorSumSubspace V :=
  LinearEquiv.ofInjective (subspaceSumLinear V)
    (subspaceSumLinear_injective V S hS hV)

theorem finrank_colorSumSubspace (V : G → Submodule K (A → K))
    (S : G → Finset A) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (hV : ∀ g v, v ∈ V g → ∀ a, a ∉ S g → v a = 0) :
    finrank K (colorSumSubspace V) = ∑ g, finrank K (V g) := by
  rw [← (colorSumEquiv V S hS hV).finrank_eq, Module.finrank_pi_fintype]

theorem sum_finrank_le_card (V : G → Submodule K (A → K))
    (S : G → Finset A) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (hV : ∀ g v, v ∈ V g → ∀ a, a ∉ S g → v a = 0) :
    (∑ g, finrank K (V g)) ≤ Fintype.card A := by
  rw [← finrank_colorSumSubspace V S hS hV]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    Submodule.finrank_le (colorSumSubspace V)

end SupportedSubspaces

/-- Exact size of a local support after placing it in every packed block. -/
theorem card_packedSupportFinset {I U A : Type*} [Fintype I]
    (e : I × U ↪ A) (S : Finset U) :
    (DirectSums.packedSupportFinset e S).card = Fintype.card I * S.card := by
  simp [DirectSums.packedSupportFinset, Finset.card_product]

end SubexponentialSAT.SubexpDirectSums

end OAI.Algorithms
