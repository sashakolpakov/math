import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! # Bidegree Independence -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.BidegreeIndependence

noncomputable section

/-!
Independence of two or three neighboring bidegrees of actual differential forms.

The unit `1 + I` separates the particular characters that arise by applying the
two components of the exterior derivative once or twice. We prove that
separation explicitly and apply elementary linear algebra to the actual scalar
pullback of covectors and the actual inverse-scalar action on manifold forms.
The common form degree is arbitrary, so changing the indexing of an exterior
derivative does not introduce a further degree-transport hypothesis here.
-/

open scoped _root_.Manifold ContDiff

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Two eigenvectors with different eigenvalues cannot have a nontrivial zero sum. -/
theorem eigenvector_pair_eq_zero (L : V →ₗ[ℂ] V) {a b : ℂ} (hab : a ≠ b)
    {A B : V} (hA : L A = a • A) (hB : L B = b • B) (hsum : A + B = 0) :
    A = 0 ∧ B = 0 := by
  have hL : a • A + b • B = 0 := by
    simpa only [map_add, hA, hB, map_zero] using congrArg L hsum
  have hmul : (a - b) • A = 0 := by
    calc
      (a - b) • A = (a • A + b • B) - b • (A + B) := by module
      _ = 0 := by rw [hL, hsum, smul_zero, sub_zero]
  have hAzero : A = 0 := (smul_eq_zero_iff_right (sub_ne_zero.mpr hab)).mp hmul
  exact ⟨hAzero, by simpa only [hAzero, zero_add] using hsum⟩

/-- Three eigenvectors with pairwise different eigenvalues are independent. -/
theorem eigenvector_triple_eq_zero (L : V →ₗ[ℂ] V) {a b c : ℂ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {A B C : V}
    (hA : L A = a • A) (hB : L B = b • B) (hC : L C = c • C)
    (hsum : A + B + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have hL : a • A + b • B + c • C = 0 := by
    simpa only [map_add, hA, hB, hC, map_zero] using congrArg L hsum
  have hsum' : (b - a) • B + (c - a) • C = 0 := by
    calc
      (b - a) • B + (c - a) • C =
          (a • A + b • B + c • C) - a • (A + B + C) := by module
      _ = 0 := by rw [hL, hsum, smul_zero, sub_zero]
  have hB' : L ((b - a) • B) = b • ((b - a) • B) := by
    rw [map_smul, hB]
    exact smul_comm _ _ _
  have hC' : L ((c - a) • C) = c • ((c - a) • C) := by
    rw [map_smul, hC]
    exact smul_comm _ _ _
  obtain ⟨hBzero', hCzero'⟩ := eigenvector_pair_eq_zero L hbc hB' hC' hsum'
  have hBzero : B = 0 :=
    (smul_eq_zero_iff_right (sub_ne_zero.mpr hab.symm)).mp hBzero'
  have hCzero : C = 0 :=
    (smul_eq_zero_iff_right (sub_ne_zero.mpr hac.symm)).mp hCzero'
  exact ⟨by simpa only [hBzero, hCzero, add_zero] using hsum, hBzero, hCzero⟩

end LinearAlgebra

/-- A concrete unit that separates the neighboring characters used below. -/
def bidegreeSeparationUnit : ℂˣ :=
  Units.mk0 (1 + Complex.I) (by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre)

@[simp]
theorem bidegreeSeparationUnit_coe :
    (bidegreeSeparationUnit : ℂ) = 1 + Complex.I := rfl

/-- Every bidegree character takes a nonzero value on every complex unit. -/
theorem bidegreeCharacter_nonzero (p q : ℕ) (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Units.ne_zero z))
    (pow_ne_zero _ (star_ne_zero.mpr (Units.ne_zero z)))

/-- Addition of bidegrees multiplies their scalar-pullback characters. -/
theorem bidegreeCharacter_add_indices (p q r s : ℕ) (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + r) (q + s) z =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter r s z := by
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_add]
  ring

/-- The five low-degree character values needed for one or two derivatives. -/
theorem bidegreeSeparationUnit_characters :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 bidegreeSeparationUnit = 1 + Complex.I ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 bidegreeSeparationUnit = 1 - Complex.I ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 2 0 bidegreeSeparationUnit = 2 * Complex.I ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 bidegreeSeparationUnit = 2 ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 2 bidegreeSeparationUnit = -2 * Complex.I := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, bidegreeSeparationUnit, Complex.star_def,
      pow_two, add_mul, mul_add] <;> ring

/-- The two characters obtained after one derivative are different at `1 + I`. -/
theorem bidegreeCharacter_neighbor_pair_ne (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q bidegreeSeparationUnit ≠
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) bidegreeSeparationUnit := by
  have hA := bidegreeCharacter_add_indices p q 1 0 bidegreeSeparationUnit
  have hB := bidegreeCharacter_add_indices p q 0 1 bidegreeSeparationUnit
  simp only [Nat.add_zero, bidegreeSeparationUnit_characters.1] at hA
  simp only [Nat.add_zero, bidegreeSeparationUnit_characters.2.1] at hB
  rw [hA, hB]
  intro h
  have him := congrArg Complex.im
    (mul_left_cancel₀ (bidegreeCharacter_nonzero p q bidegreeSeparationUnit) h)
  norm_num at him

/-- The three characters obtained after two derivatives are pairwise different. -/
theorem bidegreeCharacter_neighbor_triple_ne (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q bidegreeSeparationUnit ≠
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) bidegreeSeparationUnit ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q bidegreeSeparationUnit ≠
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) bidegreeSeparationUnit ∧
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) bidegreeSeparationUnit ≠
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) bidegreeSeparationUnit := by
  have hA := bidegreeCharacter_add_indices p q 2 0 bidegreeSeparationUnit
  have hB := bidegreeCharacter_add_indices p q 1 1 bidegreeSeparationUnit
  have hC := bidegreeCharacter_add_indices p q 0 2 bidegreeSeparationUnit
  simp only [Nat.add_zero, bidegreeSeparationUnit_characters.2.2.1] at hA
  simp only [bidegreeSeparationUnit_characters.2.2.2.1] at hB
  simp only [Nat.add_zero, bidegreeSeparationUnit_characters.2.2.2.2] at hC
  rw [hA, hB, hC]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hre := congrArg Complex.re
      (mul_left_cancel₀ (bidegreeCharacter_nonzero p q bidegreeSeparationUnit) h)
    norm_num at hre
  · intro h
    have him := congrArg Complex.im
      (mul_left_cancel₀ (bidegreeCharacter_nonzero p q bidegreeSeparationUnit) h)
    norm_num at him
  · intro h
    have hre := congrArg Complex.re
      (mul_left_cancel₀ (bidegreeCharacter_nonzero p q bidegreeSeparationUnit) h)
    norm_num at hre

section Covectors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n p q : ℕ}

/-- Independence of neighboring bidegrees for genuine alternating covectors. -/
theorem formValue_neighbor_pair_eq_zero (A B : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hA : ∀ (z : ℂˣ) (v : Fin n → E),
      A (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q z * A v)
    (hB : ∀ (z : ℂˣ) (v : Fin n → E),
      B (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z * B v)
    (hsum : A + B = 0) : A = 0 ∧ B = 0 := by
  apply eigenvector_pair_eq_zero (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n (bidegreeSeparationUnit : ℂ))
    (bidegreeCharacter_neighbor_pair_ne p q) (hsum := hsum)
  · ext v
    exact hA bidegreeSeparationUnit v
  · ext v
    exact hB bidegreeSeparationUnit v

/-- The three neighboring types from two derivatives are independent as covectors. -/
theorem formValue_neighbor_triple_eq_zero (A B C : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hA : ∀ (z : ℂˣ) (v : Fin n → E),
      A (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q z * A v)
    (hB : ∀ (z : ℂˣ) (v : Fin n → E),
      B (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) z * B v)
    (hC : ∀ (z : ℂˣ) (v : Fin n → E),
      C (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) z * C v)
    (hsum : A + B + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  obtain ⟨hab, hac, hbc⟩ := bidegreeCharacter_neighbor_triple_ne p q
  apply eigenvector_triple_eq_zero (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n (bidegreeSeparationUnit : ℂ))
    hab hac hbc (hsum := hsum)
  · ext v
    exact hA bidegreeSeparationUnit v
  · ext v
    exact hB bidegreeSeparationUnit v
  · ext v
    exact hC bidegreeSeparationUnit v

/-- Pointwise covector independence gives independence of actual raw forms. -/
theorem rawForm_neighbor_pair_eq_zero (A B : Analysis.DifferentialForms.Manifold.Basic.RawForm E n)
    (hA : ∀ (x : E) (z : ℂˣ) (v : Fin n → E),
      A x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q z * A x v)
    (hB : ∀ (x : E) (z : ℂˣ) (v : Fin n → E),
      B x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z * B x v)
    (hsum : A + B = 0) : A = 0 ∧ B = 0 := by
  have hx (x : E) := formValue_neighbor_pair_eq_zero (A x) (B x) (hA x) (hB x)
    (congrFun hsum x)
  exact ⟨funext (fun x => (hx x).1), funext (fun x => (hx x).2)⟩

/-- The three neighboring derivative types are independent as raw forms. -/
theorem rawForm_neighbor_triple_eq_zero (A B C : Analysis.DifferentialForms.Manifold.Basic.RawForm E n)
    (hA : ∀ (x : E) (z : ℂˣ) (v : Fin n → E),
      A x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q z * A x v)
    (hB : ∀ (x : E) (z : ℂˣ) (v : Fin n → E),
      B x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) z * B x v)
    (hC : ∀ (x : E) (z : ℂˣ) (v : Fin n → E),
      C x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) z * C x v)
    (hsum : A + B + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have hx (x : E) := formValue_neighbor_triple_eq_zero (A x) (B x) (C x)
    (hA x) (hB x) (hC x) (congrFun hsum x)
  exact ⟨funext (fun x => (hx x).1), funext (fun x => (hx x).2.1),
    funext (fun x => (hx x).2.2)⟩

end Covectors

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n p q : ℕ}

/-- Independence of neighboring types for the actual inverse-scalar section action. -/
theorem rawManifoldForm_neighbor_pair_eq_zero (A B : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (hA : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z A =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q z⁻¹ • A)
    (hB : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z B =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z⁻¹ • B)
    (hsum : A + B = 0) : A = 0 ∧ B = 0 := by
  apply eigenvector_pair_eq_zero (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction bidegreeSeparationUnit⁻¹)
    (bidegreeCharacter_neighbor_pair_ne p q) (hsum := hsum)
  · simpa only [inv_inv] using hA bidegreeSeparationUnit⁻¹
  · simpa only [inv_inv] using hB bidegreeSeparationUnit⁻¹

/-- Three neighboring manifold-form types cannot cancel each other. -/
theorem rawManifoldForm_neighbor_triple_eq_zero (A B C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (hA : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z A =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q z⁻¹ • A)
    (hB : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z B =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) z⁻¹ • B)
    (hC : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z C =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) z⁻¹ • C)
    (hsum : A + B + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  obtain ⟨hab, hac, hbc⟩ := bidegreeCharacter_neighbor_triple_ne p q
  apply eigenvector_triple_eq_zero (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction bidegreeSeparationUnit⁻¹)
    hab hac hbc (hsum := hsum)
  · simpa only [inv_inv] using hA bidegreeSeparationUnit⁻¹
  · simpa only [inv_inv] using hB bidegreeSeparationUnit⁻¹
  · simpa only [inv_inv] using hC bidegreeSeparationUnit⁻¹

/-- A decomposition into the two neighboring manifold-form types is unique. -/
theorem rawManifoldForm_neighbor_pair_unique (A B A' B' : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (hA : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z A =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q z⁻¹ • A)
    (hB : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z B =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z⁻¹ • B)
    (hA' : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z A' =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q z⁻¹ • A')
    (hB' : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z B' =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z⁻¹ • B')
    (hsum : A + B = A' + B') : A = A' ∧ B = B' := by
  have hdiff : (A - A') + (B - B') = 0 := by
    calc
      (A - A') + (B - B') = (A + B) - (A' + B') := by abel
      _ = 0 := sub_eq_zero.mpr hsum
  obtain ⟨hAzero, hBzero⟩ := rawManifoldForm_neighbor_pair_eq_zero (p := p) (q := q)
    (A - A') (B - B')
    (fun z => by rw [map_sub, hA z, hA' z, smul_sub])
    (fun z => by rw [map_sub, hB z, hB' z, smul_sub]) hdiff
  exact ⟨sub_eq_zero.mp hAzero, sub_eq_zero.mp hBzero⟩

end

end OAI.AlgebraicTopology.DeRham.Comparison.BidegreeIndependence
