import OAI.NumberTheory.ArithmeticGroups.Trace
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization

/-! # Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel

noncomputable section

open scoped Classical

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

def integerCoordinates : (Fin 3 → NumberField.RingOfIntegers E) →ₗ[ℤ] Data.CongruenceLevel.VE E where
  toFun x i := x i
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

def standardLattice : Submodule ℤ (Data.CongruenceLevel.VE E) := LinearMap.range (integerCoordinates (E := E))

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
lemma mem_standardLattice (x : Data.CongruenceLevel.VE E) :
    x ∈ standardLattice (E := E) ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact (a i).property
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩

omit [NumberField.IsCMField E] in
theorem standardLattice_full_stable : Data.CongruenceLevel.FullStableLattice (standardLattice (E := E)) := by
  refine ⟨Submodule.fg_range _, ?_, ?_⟩
  · apply top_unique
    intro x _
    have hs (i : Fin 3) (a : E) : Pi.single i a ∈
        Submodule.span ℚ (standardLattice (E := E) : Set (Data.CongruenceLevel.VE E)) := by
      obtain ⟨n, hn, hi⟩ := AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization.exists_positive_integral_multiple E a
      have hin : Pi.single i (n • a) ∈ standardLattice (E := E) := by
        apply (mem_standardLattice _).mpr
        intro j
        by_cases hij : i = j
        · subst j; simpa using hi
        · simpa only [Pi.single_eq_of_ne (Ne.symm hij)] using (isIntegral_zero : IsIntegral ℤ (0 : E))
      have h := (Submodule.span ℚ (standardLattice (E := E) : Set (Data.CongruenceLevel.VE E))).smul_mem
        ((n : ℚ)⁻¹) (Submodule.subset_span hin)
      convert h using 1
      ext j
      by_cases hij : i = j
      · subst j
        simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul]
        have hne : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
        simp [Algebra.smul_def, hne]
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij)]
        change (0 : E) = ((n : ℚ)⁻¹) • (0 : E)
        simp only [Algebra.smul_def, mul_zero]
    have hx : x = ∑ i : Fin 3, Pi.single i (x i) := by
      ext j
      simp
    rw [hx]
    exact Submodule.sum_mem _ (fun i _ => hs i (x i))
  · intro a x hx
    apply (mem_standardLattice _).mpr
    intro i
    exact a.property.mul ((mem_standardLattice x).mp hx i)

omit [NumberField.IsCMField E] in
/-- Clear both coefficients δ and δb using a single positive integer. -/
lemma exists_integral_trace_coefficients (b δ : E) :
    ∃ m : ℕ, 0 < m ∧
      IsIntegral ℤ (m • δ) ∧ IsIntegral ℤ (m • (δ * b)) := by
  obtain ⟨m₁, hm₁, h₁⟩ := AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization.exists_positive_integral_multiple E δ
  obtain ⟨m₂, hm₂, h₂⟩ := AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization.exists_positive_integral_multiple E (δ * b)
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_, ?_⟩
  · rw [mul_comm m₁ m₂, mul_smul]
    exact h₁.nsmul m₂
  · rw [mul_smul]
    exact h₂.nsmul m₁

theorem trace_integral_on_standardLattice
    (b δ : E) (m : ℕ)
    (hδ : IsIntegral ℤ (m • δ))
    (hδb : IsIntegral ℤ (m • (δ * b)))
    (x y : Data.CongruenceLevel.VE E) (hx : x ∈ standardLattice (E := E)) (hy : y ∈ standardLattice (E := E)) :
    ∃ n : ℤ, (m : ℚ) * Trace.CongruenceLevel.rationalTrace b δ x y = (n : ℚ) := by
  have hi : IsIntegral ℤ (m • (δ * Data.CongruenceLevel.hermitian b x y)) := by
    have he : m • (δ * Data.CongruenceLevel.hermitian b x y) =
        ∑ i : Fin 3, (m • (δ * (if i = 2 then b else 1))) * x i *
          NumberField.IsCMField.complexConj E (y i) := by
      simp only [Data.CongruenceLevel.hermitian, Finset.mul_sum, Finset.smul_sum, nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    apply IsIntegral.sum
    intro i _
    have hc : IsIntegral ℤ (m • (δ * (if i = 2 then b else 1))) := by
      split_ifs
      · exact hδb
      · simpa using hδ
    exact (hc.mul ((mem_standardLattice x).mp hx i)).mul
      (map_isIntegral_int (NumberField.IsCMField.complexConj E).toRingHom
        ((mem_standardLattice y).mp hy i))
  have ht : IsIntegral ℤ (Algebra.trace ℚ E (m • (δ * Data.CongruenceLevel.hermitian b x y))) :=
    Algebra.isIntegral_trace hi
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  refine ⟨n, ?_⟩
  calc
    (m : ℚ) * Trace.CongruenceLevel.rationalTrace b δ x y =
        Algebra.trace ℚ E (m • (δ * Data.CongruenceLevel.hermitian b x y)) := by
      rw [map_nsmul]
      rfl
    _ = (n : ℚ) := hn.symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel
