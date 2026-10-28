import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarBinomial
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem prod_choice {ι : Type*} [DecidableEq ι] (s A : Finset ι) (hA : A ⊆ s)
    (p q : ι → K) :
    (∏ l ∈ s, if l ∈ A then q l else p l) =
      (∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l := by
  rw [Finset.prod_ite]
  have hf : s.filter (fun l => l ∈ A) = A := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hA h)
  have hg : s.filter (fun l => l ∉ A) = s \ A := by
    ext l
    simp
  rw [hf, hg]

theorem linear_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p q : ι → K) :
    (∏ l ∈ s, (C (p l) + C (q l) * X)) =
      ∑ A ∈ s.powerset,
        C ((∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l) * X ^ A.card := by
  rw [show (∏ l ∈ s, (C (p l) + C (q l) * X)) =
      ∏ l ∈ s, (C (q l) * X + C (p l)) by
    apply Finset.prod_congr rfl
    intro l hl
    ring]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, ← map_prod, map_mul]
  ring

theorem coeff_linear_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p q : ι → K) (j : ℕ) :
    (∏ l ∈ s, (C (p l) + C (q l) * X)).coeff j =
      ∑ A ∈ s.powersetCard j,
        (∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l := by
  rw [linear_product_expansion, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp [Finset.powersetCard_eq_filter, eq_comm]

theorem partialKernel_fullSwap (i : Fin Δ) (t : Fin Q)
    (A : Finset (Fin Q)) (hA : A ⊆ MatrixSupport.activePositions t)
    (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i A
        (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) y =
      (background i u y * plain i u y t) *
        ((∏ l ∈ A, (flipped i u y l - plain i u y l)) *
          ∏ l ∈ MatrixSupport.activePositions t \ A, flipped i u y l) := by
  classical
  have ht : t ∉ A := by
    intro ht
    simpa [MatrixSupport.activePositions] using hA ht
  have split (f : Fin Q → K) :
      (∏ l, f l) = f t * ∏ l ∈ MatrixSupport.activePositions t, f l :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ t)).symm
  rw [partialKernel, background_swap, split]
  have he : factor (K := K) i A
      (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) y t =
        plain i u y t := by
    simp [factor, ht, MatrixSupport.activePositions]
  rw [he, ← mul_assoc]
  congr 1
  calc
    _ = ∏ l ∈ MatrixSupport.activePositions t,
          if l ∈ A then flipped i u y l - plain i u y l else flipped i u y l := by
      apply Finset.prod_congr rfl
      intro l hl
      simp only [factor, plain_swap, flipped_swap, hl, ite_true]
    _ = _ := prod_choice (MatrixSupport.activePositions t) A hA _ _

noncomputable def kernelPolynomial (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) : K[X] :=
  C (background i u y * plain i u y t) *
    ∏ l ∈ MatrixSupport.activePositions t,
      (C (flipped i u y l) + C (flipped i u y l - plain i u y l) * X)

/-- The factor 2^j is precisely canceled by using normalized coefficients. -/
theorem coeff_kernelPolynomial (h2 : (2 : K) ≠ 0) (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (j : ℕ) :
    (kernelPolynomial (K := K) i t u y).coeff j =
      (2 : K) ^ j * MatrixSupport.elementaryProjector i t j
        (MatrixSupport.delta y) (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) := by
  classical
  rw [kernelPolynomial, coeff_C_mul, coeff_linear_product,
    MatrixSupport.elementaryProjector, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hs := (Finset.mem_powersetCard.mp hA).1
  have hc := (Finset.mem_powersetCard.mp hA).2
  rw [MatrixSupport.projectorProduct, Finset.length_toList, hc,
    ← mul_assoc ((2 : K) ^ j) ((2 : K)⁻¹ ^ j) _]
  have hcancel : (2 : K) ^ j * (2 : K)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
  rw [hcancel, one_mul, differenceProduct_eq_partialKernel i A.toList A.nodup_toList,
    Finset.toList_toFinset, partialKernel_fullSwap i t A hs]

/-- This is equality with the existing operator's entry, not an assumed
specification for a replacement matrix. -/
theorem matrixEntry_eq_weighted_coeff (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (R : ℕ) (a : ℕ → K) (u y : UniversalType r Q Δ) :
    MatrixSupport.matrixEntry i t R (fun j => a j * (2 : K) ^ j) u y =
      ∑ j ∈ Finset.range R, a j * (kernelPolynomial i t u y).coeff j := by
  unfold MatrixSupport.matrixEntry
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_kernelPolynomial h2]
  ring

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

def Compatible (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Prop :=
  SpectatorsAgree i u y ∧ pair i u t = pair i y t ∧
    ∀ l, l ≠ t → pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l

instance compatibleDecidable (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    Decidable (Compatible i t u y) := by
  unfold Compatible SpectatorsAgree
  infer_instance

def unchanged (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  (MatrixSupport.activePositions t).filter fun l =>
    u.head l ≠ u.slot i l ∧ pair i u l = pair i y l

def transposed (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  (MatrixSupport.activePositions t).filter fun l =>
    u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l

theorem unchanged_subset (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    unchanged i t u y ⊆ MatrixSupport.activePositions t := Finset.filter_subset _ _

theorem transposed_subset (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    transposed i t u y ⊆ MatrixSupport.activePositions t := Finset.filter_subset _ _

theorem unchanged_transposed_disjoint (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) : Disjoint (unchanged i t u y) (transposed i t u y) := by
  apply Finset.disjoint_left.mpr
  intro l ha hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact ha'.1 (congrArg Prod.fst (ha'.2.trans hb'.2.symm))

theorem local_factor_of_compatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : Compatible i t u y)
    (l : Fin Q) (hl : l ∈ MatrixSupport.activePositions t) :
    (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X) =
      (if l ∈ unchanged i t u y then -X else 1) *
        (if l ∈ transposed i t u y then 1 + X else 1) := by
  have hlt : l ≠ t := (Finset.mem_erase.mp hl).1
  have hp := hc.2.2 l hlt
  by_cases hf : u.head l = u.slot i l
  · have he : (u.slot i l, u.head l) = pair i u l := by simp [pair, hf]
    have hs : pair i u l = pair i y l := hp.elim id (fun h => he.symm.trans h)
    have ht : (u.slot i l, u.head l) = pair i y l := he.trans hs
    simp only [plain, flipped, hs, ht, ite_true, sub_self,
      map_one, map_zero, zero_mul, add_zero]
    simp [unchanged, transposed, hf]
  · by_cases hs : pair i u l = pair i y l
    · have ht : (u.slot i l, u.head l) ≠ pair i y l := by
        intro ht
        exact hf (congrArg Prod.fst (hs.trans ht.symm))
      simp [plain, flipped, hs, ht, unchanged, transposed, hf, hl]
    · have ht : (u.slot i l, u.head l) = pair i y l := hp.resolve_left hs
      simp [plain, flipped, hs, ht, unchanged, transposed, hf, hl]

theorem prod_indicator {ι : Type*} [DecidableEq ι] (s A : Finset ι) (hA : A ⊆ s)
    (z : K[X]) : (∏ l ∈ s, if l ∈ A then z else 1) = z ^ A.card := by
  rw [Finset.prod_ite]
  have hf : s.filter (fun l => l ∈ A) = A := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hA h)
  rw [hf]
  simp

theorem kernelPolynomial_of_compatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : Compatible i t u y) :
    kernelPolynomial (K := K) i t u y =
      (-X) ^ (unchanged i t u y).card * (1 + X) ^ (transposed i t u y).card := by
  classical
  have hb : background (K := K) i u y * plain i u y t = 1 := by
    simp [background, plain, hc.1, hc.2.1]
  rw [kernelPolynomial, hb, map_one, one_mul]
  have hprod :
      (∏ l ∈ MatrixSupport.activePositions t,
        (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X)) =
      ∏ l ∈ MatrixSupport.activePositions t,
        (if l ∈ unchanged i t u y then -X else 1) *
          (if l ∈ transposed i t u y then 1 + X else 1) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact local_factor_of_compatible i t u y hc l hl
  rw [hprod, Finset.prod_mul_distrib,
    prod_indicator _ _ (unchanged_subset i t u y),
    prod_indicator _ _ (transposed_subset i t u y)]

theorem kernelPolynomial_of_incompatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : ¬ Compatible i t u y) :
    kernelPolynomial (K := K) i t u y = 0 := by
  classical
  by_cases hs : SpectatorsAgree i u y
  · by_cases ht : pair i u t = pair i y t
    · have hbad : ¬ ∀ l, l ≠ t →
          pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l :=
        fun h => hc ⟨hs, ht, h⟩
      push Not at hbad
      obtain ⟨l, hlt, hsame, hswap⟩ := hbad
      have hl : l ∈ MatrixSupport.activePositions t := by
        simp [MatrixSupport.activePositions, hlt]
      have hz :
          (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X) = 0 := by
        simp [plain, flipped, hsame, hswap]
      rw [kernelPolynomial, Finset.prod_eq_zero hl hz, mul_zero]
    · simp [kernelPolynomial, plain, ht]
  · simp [kernelPolynomial, background, hs]

theorem kernelPolynomial_eq (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) :
    kernelPolynomial (K := K) i t u y =
      if Compatible i t u y then
        (-X) ^ (unchanged i t u y).card * (1 + X) ^ (transposed i t u y).card
      else 0 := by
  classical
  by_cases hc : Compatible i t u y
  · simpa only [hc, ite_true] using kernelPolynomial_of_compatible (K := K) i t u y hc
  · simpa only [hc, ite_false] using kernelPolynomial_of_incompatible (K := K) i t u y hc

/-- The physical counter may test all Q coordinates without masking t. -/
def AllCompatible (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  SpectatorsAgree i u y ∧
    ∀ l, pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l

instance allCompatibleDecidable (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (AllCompatible i u y) := by
  unfold AllCompatible SpectatorsAgree
  infer_instance

def allUnchanged (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter fun l => u.head l ≠ u.slot i l ∧ pair i u l = pair i y l

def allTransposed (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter fun l => u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l

theorem joint_anchor_nonfixed (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u : Joint t g i) : u.val.head t ≠ u.val.slot i t := by
  intro h
  exact u.property.2 (h.symm.trans u.property.1)

theorem joint_anchor_not_transposed (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) : (u.val.slot i t, u.val.head t) ≠ pair i y.val t := by
  intro h
  exact u.property.2 ((congrArg Prod.fst h).trans y.property.1)

theorem allCompatible_iff_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) :
    AllCompatible i u.val y.val ↔ Compatible i t u.val y.val := by
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨hs, (hp t).resolve_right (joint_anchor_not_transposed i t g u y),
      fun l _ => hp l⟩
  · rintro ⟨hs, ht, hp⟩
    refine ⟨hs, fun l => ?_⟩
    by_cases h : l = t
    · subst l
      exact Or.inl ht
    · exact hp l h

theorem allUnchanged_eq_insert_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) (hc : Compatible i t u.val y.val) :
    allUnchanged i u.val y.val = insert t (unchanged i t u.val y.val) := by
  ext l
  by_cases h : l = t
  · subst l
    simp [allUnchanged, joint_anchor_nonfixed i t g u, hc.2.1]
  · simp [allUnchanged, unchanged, MatrixSupport.activePositions, h]

theorem allTransposed_eq_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) :
    allTransposed i u.val y.val = transposed i t u.val y.val := by
  ext l
  by_cases h : l = t
  · subst l
    simp [allTransposed, transposed, MatrixSupport.activePositions,
      joint_anchor_not_transposed i t g u y]
  · simp [allTransposed, transposed, MatrixSupport.activePositions, h]

/-- Remove one token from the physical all-coordinate unchanged counter. -/
theorem allUnchanged_card_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) (hc : AllCompatible i u.val y.val) :
    (allUnchanged i u.val y.val).card = (unchanged i t u.val y.val).card + 1 := by
  have ht : t ∉ unchanged i t u.val y.val := by
    simp [unchanged, MatrixSupport.activePositions]
  rw [allUnchanged_eq_insert_joint i t g u y ((allCompatible_iff_joint i t g u y).mp hc),
    Finset.card_insert_of_notMem ht]

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem same_not_swap_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (pair i u l = pair i y l ∧ (u.slot i l, u.head l) ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ pair i u l = pair i y l) := by
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨?_, hs⟩
    intro hf
    apply ht
    have he : (u.slot i l, u.head l) = pair i u l := by simp [pair, hf]
    exact he.trans hs
  · rintro ⟨hf, hs⟩
    refine ⟨hs, ?_⟩
    intro ht
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

theorem swap_not_same_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    ((u.slot i l, u.head l) = pair i y l ∧ pair i u l ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l) := by
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨?_, ht⟩
    intro hf
    apply hs
    have he : pair i u l = (u.slot i l, u.head l) := by simp [pair, hf]
    exact he.trans ht
  · rintro ⟨hf, ht⟩
    refine ⟨ht, ?_⟩
    intro hs
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

/-- Exact scalar entry, including incompatible rows and columns and the
case where the mandatory number of differences exceeds the cutoff R. -/
theorem matrixEntry_normalized (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (R : ℕ) (a : ℕ → K) (u y : UniversalType r Q Δ) :
    MatrixSupport.matrixEntry i t R (fun j => a j * (2 : K) ^ j) u y =
      if Compatible i t u y then
        (-1 : K) ^ (unchanged i t u y).card *
          ∑ k ∈ Finset.range (R - (unchanged i t u y).card),
            a ((unchanged i t u y).card + k) * ((transposed i t u y).card.choose k : K)
      else 0 := by
  classical
  rw [matrixEntry_eq_weighted_coeff h2]
  by_cases hc : Compatible i t u y
  · rw [ite_eq_left hc]
    simp_rw [kernelPolynomial_of_compatible i t u y hc]
    exact ScalarBinomial.weighted_prefix a _ _ _
  · simp only [ite_eq_right hc, kernelPolynomial_of_incompatible i t u y hc,
      Polynomial.coeff_zero, mul_zero, Finset.sum_const_zero]

/-- The dynamic-programming matrix used by the implementation has these
same scalar entries; no equality to an independently chosen basis is used. -/
theorem jointMatrixDP_normalized (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (R : ℕ) (a : ℕ → K)
    (u y : Joint t g i) :
    ElementaryMatrix.jointMatrixDP i t g R (fun j => a j * (2 : K) ^ j) u y =
      if Compatible i t u.val y.val then
        (-1 : K) ^ (unchanged i t u.val y.val).card *
          ∑ k ∈ Finset.range (R - (unchanged i t u.val y.val).card),
            a ((unchanged i t u.val y.val).card + k) *
              ((transposed i t u.val y.val).card.choose k : K)
      else 0 := by
  classical
  rw [ElementaryMatrix.jointMatrixDP_eq]
  exact matrixEntry_normalized h2 i t R a u.val y.val

/-- The physical all-coordinate counter needs only one decrement: jointness
makes the anchor an unchanged, nonfixed pair whenever compatibility holds. -/
theorem jointMatrixDP_all_normalized (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (R : ℕ) (a : ℕ → K)
    (u y : Joint t g i) :
    ElementaryMatrix.jointMatrixDP i t g R (fun j => a j * (2 : K) ^ j) u y =
      if AllCompatible i u.val y.val then
        (-1 : K) ^ ((allUnchanged i u.val y.val).card - 1) *
          ∑ k ∈ Finset.range (R - ((allUnchanged i u.val y.val).card - 1)),
            a ((allUnchanged i u.val y.val).card - 1 + k) *
              ((allTransposed i u.val y.val).card.choose k : K)
      else 0 := by
  classical
  rw [jointMatrixDP_normalized h2]
  by_cases hc : AllCompatible i u.val y.val
  · have hc' := (allCompatible_iff_joint i t g u y).mp hc
    simp only [ite_eq_left hc, ite_eq_left hc', allUnchanged_card_joint i t g u y hc,
      allTransposed_eq_joint i t g u y, Nat.add_sub_cancel]
  · have hc' : ¬ Compatible i t u.val y.val :=
      fun h => hc ((allCompatible_iff_joint i t g u y).mpr h)
    simp only [ite_eq_right hc, ite_eq_right hc']

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
