import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Integral Modulus -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralModulus

noncomputable section

/-! Integral invertible matrices preserve integral vectors, and an
integral scalar unit has Haar modulus one. -/

open _root_.MeasureTheory _root_.Matrix
open scoped Classical Pointwise NNReal

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

section Algebra
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I] (S : Subring R)

omit [DecidableEq I] in
theorem integral_mulVec {A : Matrix I I R} (hA : ∀ i j, A i j ∈ S)
    {x : I → R} (hx : ∀ i, x i ∈ S) (i : I) : (A *ᵥ x) i ∈ S :=
  S.sum_mem fun j _ => S.mul_mem (hA i j) (hx j)

theorem integral_determinant {A : Matrix I I R} (hA : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  let B : Matrix I I S := fun i j => ⟨A i j, hA i j⟩
  have h := RingHom.map_det S.subtype B
  exact h ▸ B.det.property

omit [Fintype I] in
theorem integral_sub_one {A : Matrix I I R} (hA : ∀ i j, A i j ∈ S) :
    ∀ i j, (A - 1) i j ∈ S := by
  intro i j
  apply S.sub_mem (hA i j)
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem integral_unit_inverse_vec (A : (Matrix I I R)ˣ)
    (hA : ∀ i j, A.val i j ∈ S) (hi : ∀ i j, A.inv i j ∈ S) (x : I → R) :
    (∀ i, (A.val *ᵥ x) i ∈ S) ↔ ∀ i, x i ∈ S := by
  constructor
  · intro hx
    have he : A.inv *ᵥ (A.val *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, A.inv_val, Matrix.one_mulVec]
    intro i
    rw [← he]
    exact integral_mulVec S hi hx i
  · intro hx
    exact integral_mulVec S hA hx

end Algebra

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k]

theorem localModulus_integral_unit (S : Subring k)
    (hSo : IsOpen (S : Set k)) (hSc : IsCompact (S : Set k))
    (a : kˣ) (ha : a.val ∈ S) (hi : a.inv ∈ S) : Weil.Local.FunctionsMetaplectic.Construction.localModulus k a = 1 := by
  let μ : Measure k := Measure.addHaar
  have hset : a • (S : Set k) = S := by
    ext x
    change (∃ y ∈ S, a.val * y = x) ↔ x ∈ S
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.mul_mem ha hy
    · intro hx
      refine ⟨a.inv * x, S.mul_mem hi hx, ?_⟩
      rw [← mul_assoc, a.val_inv, one_mul]
  have hz : μ (S : Set k) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ
      (by rw [hSo.interior_eq]; exact ⟨0, S.zero_mem⟩)).ne'
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) hz hSc.measure_ne_top
    (r := 1) (by rw [hset]; simp)
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) h

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralModulus
