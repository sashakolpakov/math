import OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Exterior Typed Basis -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorTypedBasis.CM

noncomputable section

/-!
# Exterior type from two subspaces

An exterior signed-type subspace is defined by wedges of vectors in the
two specified subspaces, without choosing a basis. If a signed basis spans
those subspaces, the exterior type is exactly the span of basis monomials
with the specified signed degree.
-/

open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For `p + q` slots, signed degree `p - q` means exactly `p` positive and `q` negative slots. -/
theorem signTotal_eq_sub_iff_counts (p q : ℕ) (ε : Fin (p + q) → Bool) :
    (∑ i, SignSwitch.CM.signValue (ε i)) = (p : ℤ) - q ↔
      Fintype.card {i // ε i = true} = p ∧ Fintype.card {i // ε i = false} = q := by
  have hs := SignSwitch.CM.signSum_eq_counts (fun i (_ : Unit) => ε i) ()
  have hc := SignSwitch.CM.signCount_true_add_false (fun i (_ : Unit) => ε i) ()
  simp only [SignSwitch.CM.signSum, SignSwitch.CM.signCount] at hs
  simp only [SignSwitch.CM.signCount, Fintype.card_fin] at hc
  constructor <;> intro h <;> omega

/-- The span of wedges of pure vectors whose signed degrees sum to `w`. -/
def exteriorSignedSpan (S : Bool → Submodule K V) (n : ℕ) (w : ℤ) :
    Submodule K (⋀[K]^n V) :=
  Submodule.span K {x | ∃ (ε : Fin n → Bool) (v : Fin n → V),
    (∑ i, SignSwitch.CM.signValue (ε i)) = w ∧ (∀ i, v i ∈ S (ε i)) ∧ exteriorPower.ιMulti K n v = x}

variable {ι : Type*} [LinearOrder ι] (n : ℕ) (b : Module.Basis ι K V)

/-- Enumerating an ordered subset gives its usual finite sum. -/
theorem sum_orderedExteriorIndex (f : ι → ℤ) (s : Set.powersetCard ι n) :
    (∑ i, f (Set.powersetCard.ofFinEmbEquiv.symm s i)) = ∑ j ∈ s.val, f j := by
  have hs : Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding = s.val := by
    simpa only [Set.powersetCard.ofFinEmbEquiv_apply, Set.powersetCard.val_ofFinEmb] using
      congrArg Subtype.val (Set.powersetCard.ofFinEmbEquiv.apply_symm_apply s)
  rw [← hs, Finset.sum_map]
  rfl

/-- An injective tuple of basis vectors has zero exterior coordinates off its image subset. -/
theorem exteriorTuple_coordinate_zero (r : Fin n ↪ ι) (t : Set.powersetCard ι n)
    (ht : t ≠ Set.powersetCard.ofFinEmb n ι r) :
    (b.exteriorPower n).repr (exteriorPower.ιMulti K n (fun i => b (r i))) t = 0 := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  obtain ⟨a, hat, han⟩ :=
    (Set.powersetCard.exists_mem_notMem_iff_ne t (Set.powersetCard.ofFinEmb n ι r)).mp ht
  obtain ⟨j, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t a).mpr hat
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  have hi : r i ∈ Set.powersetCard.ofFinEmb n ι r :=
    (Set.powersetCard.mem_ofFinEmb_iff_mem_range n ι r _).mpr ⟨i, rfl⟩
  have hneq : Set.powersetCard.ofFinEmbEquiv.symm t j ≠ r i := fun he => han (he ▸ hi)
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne hneq]

/-- A wedge of distinct basis vectors is on the exterior-basis line of their subset. -/
theorem exteriorTuple_eq_smul (r : Fin n ↪ ι) :
    exteriorPower.ιMulti K n (fun i => b (r i)) =
      (b.exteriorPower n).repr (exteriorPower.ιMulti K n (fun i => b (r i)))
        (Set.powersetCard.ofFinEmb n ι r) • b.exteriorPower n (Set.powersetCard.ofFinEmb n ι r) := by
  apply (b.exteriorPower n).ext_elem
  intro t
  by_cases ht : t = Set.powersetCard.ofFinEmb n ι r
  · subst t
    simp
  · rw [exteriorTuple_coordinate_zero n b r t ht]
    simp [Ne.symm ht]

variable (s : ι → Bool) (w : ℤ)

/-- The signed degree of an exterior-basis monomial. -/
def exteriorBasisSignSum (t : Set.powersetCard ι n) : ℤ := ∑ j ∈ t.val, SignSwitch.CM.signValue (s j)

/-- The basis description to be compared with the intrinsic pure-wedge definition. -/
def exteriorSignedBasisSpan : Submodule K (⋀[K]^n V) :=
  Submodule.span K ((b.exteriorPower n) '' {t | exteriorBasisSignSum n s t = w})

/-- Every ordered or unordered basis tuple of the right signed degree lies in the diagonal span. -/
theorem exteriorTuple_mem_signedBasisSpan (r : Fin n → ι)
    (hr : (∑ i, SignSwitch.CM.signValue (s (r i))) = w) :
    exteriorPower.ιMulti K n (fun i => b (r i)) ∈ exteriorSignedBasisSpan n b s w := by
  by_cases hinj : Function.Injective r
  · let t := Set.powersetCard.ofFinEmb n ι ⟨r, hinj⟩
    have ht : exteriorBasisSignSum n s t = w := by
      simpa only [exteriorBasisSignSum, t, Set.powersetCard.val_ofFinEmb,
        Finset.sum_map, Function.Embedding.coeFn_mk] using hr
    have heq := exteriorTuple_eq_smul n b ⟨r, hinj⟩
    simp only [Function.Embedding.coeFn_mk] at heq
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)
  · have hz : exteriorPower.ιMulti K n (fun i => b (r i)) = 0 :=
      (exteriorPower.ιMulti K n).map_eq_zero_of_not_injective _
        (fun hi => hinj (Function.Injective.of_comp hi))
    rw [hz]
    exact Submodule.zero_mem _

variable [Fintype ι] (S : Bool → Submodule K V)
variable (hS : ∀ e, S e = Submodule.span K (b '' {j | s j = e}))

include hS in
/-- Pure-wedge exterior type is exactly diagonal type in any compatible signed basis. -/
theorem exteriorSignedSpan_eq_basisSpan :
    exteriorSignedSpan S n w = exteriorSignedBasisSpan n b s w := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨ε, v, hε, hv, rfl⟩
    let f := (exteriorPower.ιMulti K n (M := V)).toMultilinearMap
    have he : exteriorPower.ιMulti K n v =
        ∑ r : Fin n → ι, exteriorPower.ιMulti K n (fun i => b.repr (v i) (r i) • b (r i)) := by
      have hm := f.map_sum (fun i j => b.repr (v i) j • b j)
      simpa only [Module.Basis.sum_repr, f, AlternatingMap.coe_multilinearMap] using hm
    rw [he]
    apply Submodule.sum_mem
    intro r _
    rw [AlternatingMap.map_smul_univ]
    by_cases hc : (∏ i, b.repr (v i) (r i)) = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply exteriorTuple_mem_signedBasisSpan n b s w r
      have hr : ∀ i, s (r i) = ε i := by
        intro i
        have hi := hv i
        rw [hS] at hi
        have hcoef : b.repr (v i) (r i) ≠ 0 :=
          (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
        exact b.mem_span_image.mp hi (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hcoef))
      simpa only [hr] using hε
  · apply Submodule.span_le.mpr
    rintro x ⟨t, ht, rfl⟩
    apply Submodule.subset_span
    refine ⟨(fun i => s (Set.powersetCard.ofFinEmbEquiv.symm t i)),
      (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm t i)), ?_, ?_, ?_⟩
    · change (∑ i, SignSwitch.CM.signValue (s (Set.powersetCard.ofFinEmbEquiv.symm t i))) = w
      rw [sum_orderedExteriorIndex n (fun j => SignSwitch.CM.signValue (s j)) t]
      exact ht
    · intro i
      rw [hS]
      exact Submodule.subset_span ⟨_, rfl, rfl⟩
    · rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorTypedBasis.CM
