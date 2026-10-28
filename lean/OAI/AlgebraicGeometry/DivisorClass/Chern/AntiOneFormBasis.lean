import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CoordinateSplit

/-! # Anti One Form Basis -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

noncomputable section

/-! Actual basis coefficients detect a pure antiholomorphic one-form. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def complexCoordinateVector (i : ι) : ι → ℂ := Pi.single i 1

omit [Fintype ι] in
theorem complexCoordinateVector_same (i : ι) : complexCoordinateVector i i = 1 := by
  simp [complexCoordinateVector]

omit [Fintype ι] in
theorem complexCoordinateVector_other {i j : ι} (h : j ≠ i) : complexCoordinateVector i j = 0 := by
  simp [complexCoordinateVector, h]

theorem complexCoordinateVector_decomposition (x : ι → ℂ) :
    (∑ i : ι, x i • complexCoordinateVector i) = x := by
  funext j
  simp [complexCoordinateVector, Pi.single_apply, Finset.sum_apply, smul_eq_mul, mul_ite]

theorem antiOneForm_eq_zero_of_basis_coefficients {U : Opens (ι → ℂ)} (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1)
    (ha : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a)
    (hb : ∀ (x : U) (i : ι), AntiOneFormCoordinates.oneFormLinear (a x) (complexCoordinateVector i) = 0) : a = 0 := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change a x v = 0
  rw [AntiOneFormCoordinates.oneFormLinear_reconstruct, ← complexCoordinateVector_decomposition (v 0), map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [AntiOneFormCoordinates.oneFormLinear_complex_smul (ha x), hb x i, mul_zero]

theorem splitComplexCoordinate_vector_same (i : ι) :
    Complex.CoordinateSplit.splitComplexCoordinate i (complexCoordinateVector i) = (0, 1) := by
  apply Prod.ext
  · funext j
    exact complexCoordinateVector_other j.property
  · exact complexCoordinateVector_same i

theorem splitComplexCoordinate_vector_other (i j : ι) (h : j ≠ i) :
    Complex.CoordinateSplit.splitComplexCoordinate i (complexCoordinateVector j) =
      ((fun k : {k : ι // k ≠ i} => complexCoordinateVector j k), 0) := by
  apply Prod.ext
  · rfl
  · exact complexCoordinateVector_other (Ne.symm h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis
