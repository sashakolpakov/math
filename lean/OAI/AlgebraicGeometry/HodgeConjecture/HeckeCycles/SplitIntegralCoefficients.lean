import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # Split Integral Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralCoefficients.CM

noncomputable section

/-! Integral coefficients of split unitary matrices, obtained from the
explicit inverse of the two root coordinates. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {k : Type*} [Field k] [CharZero k] {d : k}
  (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
  {I : Type*} [Fintype I] [DecidableEq I] (S : Subring k)

omit [CharZero k] [DecidableEq I] in
theorem matrix_mul {A B : Matrix I I k}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    ∀ i j, (A * B) i j ∈ S := by
  intro i j
  exact S.sum_mem (fun t _ => S.mul_mem (hA i t) (hB t j))

omit [Fintype I] [DecidableEq I] in
theorem join_coefficients (h2 : (2 : k)⁻¹ ∈ S) (h2r : (2 * r)⁻¹ ∈ S)
    (A B : Matrix I I k) (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    ∀ i j, (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A B i j).re ∈ S ∧
      (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A B i j).im ∈ S := by
  intro i j
  change (A i j + B i j) / 2 ∈ S ∧ (A i j - B i j) / (2 * r) ∈ S
  simp only [div_eq_mul_inv]
  exact ⟨S.mul_mem (S.add_mem (hA i j) (hB i j)) h2,
    S.mul_mem (S.sub_mem (hA i j) (hB i j)) h2r⟩

theorem lift_coefficients (h2 : (2 : k)⁻¹ ∈ S) (h2r : (2 * r)⁻¹ ∈ S)
    (H : (Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hH : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H).val i j ∈ S)
    (hHi : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H)⁻¹.val i j ∈ S)
    (A : (Matrix I I k)ˣ) (hA : ∀ i j, A.val i j ∈ S)
    (hAi : ∀ i j, A⁻¹.val i j ∈ S) :
    ∀ i j, ((RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H A).val i j).re ∈ S ∧
      ((RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H A).val i j).im ∈ S := by
  exact join_coefficients r hr hr0 S h2 h2r _ _ hA
    (fun i j => matrix_mul S (matrix_mul S hH hAi) hHi j i)

theorem special_unitary_coefficients (h2 : (2 : k)⁻¹ ∈ S) (h2r : (2 * r)⁻¹ ∈ S)
    (H : (Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hherm : H.val.conjTranspose = H.val)
    (hH : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H).val i j ∈ S)
    (hHi : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H)⁻¹.val i j ∈ S)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val)
    (hg : ∀ i j, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0 (g.val.val i j) ∈ S)
    (hgi : ∀ i j, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0 ((g⁻¹).val.val i j) ∈ S) :
    ∀ i j, (g.val.val i j).re ∈ S ∧ (g.val.val i j).im ∈ S := by
  have he := congrArg Units.val
    (RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear_recovers r hr hr0 H hherm (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g))
  change (RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnitary r hr hr0 H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g))).val =
    g.val.val at he
  rw [← he]
  exact lift_coefficients r hr hr0 S h2 h2r H hH hHi
    (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnitary r hr hr0 H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g)) hg hgi

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralCoefficients.CM
