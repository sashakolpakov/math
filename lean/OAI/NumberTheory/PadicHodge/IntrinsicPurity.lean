import OAI.NumberTheory.PadicHodge.GeometricComparisonAdapter
import OAI.NumberTheory.PadicHodge.Arithmetic

/-! # Intrinsic Purity -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicPurity.CM.ExtremeSlopesAdapter

noncomputable section

/-! Assembly bridges for CMExtraction. GeometricComparison's native comparison numbers combine
with FrobeniusSlope's determinant formula and GaloisValuation's extreme signs. The original
complex grading/projector hypotheses are retained explicitly. -/

open scoped TensorProduct

/-- The normalized Newton function has the slope formula at the whole summand. -/
theorem normalized_newton_of_constant_slope
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ_[q] V] [IsScalarTower ℚ_[q] L V]
    (φ : V ≃ₗ[L] V) (r : ℚ)
    (hslopes : ∀ x, Module.End.HasEigenvalue
      (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) x →
        Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q x = (r : WithTop ℚ)) :
    Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q L φ ⊤ = (Module.finrank L V : ℚ) * r := by
  have hd : (Module.finrank ℚ_[q] L : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos : 0 < Module.finrank ℚ_[q] L))
  simp only [Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton, Submodule.restrictScalars_top]
  have hn := Newton.CM.ExtremeSlopesAdapter.rational_newton_of_constant_slope q L φ r hslopes
  simp only [Filtration.CM.ExtremeSlopesAdapter.summandNewton, ↓reduceIte]
  rw [hn]
  field_simp

/-- Cancel the positive coefficient degree in the two independently derived
formulas: GeometricComparison's Hodge comparison and FrobeniusSlope's Frobenius determinant. -/
theorem hodge_number_of_compared_newton
    (degree dim hodge : ℕ) (hdegree : 0 < degree) (newton slope : ℚ)
    (hcomparison : newton = (degree : ℚ) * (hodge : ℚ))
    (hNewton : newton = (degree : ℚ) * (dim : ℚ) * slope) :
    (hodge : ℚ) = (dim : ℚ) * slope := by
  have hd : (degree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdegree.ne'
  apply (mul_left_cancel₀ hd)
  calc
    (degree : ℚ) * (hodge : ℚ) = newton := hcomparison.symm
    _ = (degree : ℚ) * ((dim : ℚ) * slope) := by rw [hNewton, mul_assoc]

/-- Given the actual graded complex projector onto the compared summand,
the two derived numerical identities yield the existing ExtremeSlopes pure-type result. -/
theorem pure_type_of_compared_newton
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B S : Submodule ℂ W) (h_HodgeDecomposition : IsCompl A B)
    (P : Module.End ℂ W) (hRange : LinearMap.range P = S)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B)
    (hne : S ≠ ⊥)
    (degree : ℕ) (hdegree : 0 < degree) (newton slope : ℚ)
    (hcomparison : newton = (degree : ℚ) * (Module.finrank ℂ ↥(S ⊓ A) : ℚ))
    (hNewton : newton = (degree : ℚ) * (Module.finrank ℂ S : ℚ) * slope)
    (hextreme : slope = 0 ∨ slope = 1) :
    (slope = 1 ↔ S ≤ A) ∧ (slope = 0 ↔ S ≤ B) := by
  have hn := hodge_number_of_compared_newton degree (Module.finrank ℂ S)
    (Module.finrank ℂ ↥(S ⊓ A)) hdegree newton slope hcomparison hNewton
  have h := ExtremeSlopes.CM.Construction.pure_type_of_extreme_number A B h_HodgeDecomposition P hA hB
    (by rwa [hRange]) slope hextreme (by rwa [hRange])
  simpa only [hRange] using h

/-- Terminal adapter for the actual GeometricComparison witness. The dimension and
comparison hypotheses are the proved fields of `NativeSummandComparison`;
the slopes come from full FrobeniusSlope, and extremality from full GaloisValuation. Only the
original complex grading and projector hypotheses are retained. -/
theorem pure_type_of_native_summand
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ_[q] V] [IsScalarTower ℚ_[q] L V]
    (φ : V ≃ₗ[L] V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B S : Submodule ℂ W) (h_HodgeDecomposition : IsCompl A B)
    (P : Module.End ℂ W) (hRange : LinearMap.range P = S)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B)
    (hne : S ≠ ⊥)
    (hDim : Module.finrank L V = Module.finrank ℂ S)
    (hcomparison :
      (Padic.valuation (p := q) (LinearMap.det (φ.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
        (Module.finrank ℚ_[q] L : ℚ) * (Module.finrank ℂ ↥(S ⊓ A) : ℚ))
    (slope : ℚ)
    (hslopes : ∀ x, Module.End.HasEigenvalue
      (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) x →
        Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q x = (slope : WithTop ℚ))
    (hextreme : slope = 0 ∨ slope = 1) :
    (slope = 1 ↔ S ≤ A) ∧ (slope = 0 ↔ S ≤ B) := by
  have hNewton := Newton.CM.ExtremeSlopesAdapter.rational_newton_of_constant_slope q L φ slope hslopes
  rw [hDim] at hNewton
  exact pure_type_of_compared_newton A B S h_HodgeDecomposition P hRange hA hB hne
    (Module.finrank ℚ_[q] L) Module.finrank_pos _ slope hcomparison hNewton hextreme

/-- The GaloisValuation sign rule makes the slope formula extreme, for every parameter
extension satisfying that rule. -/
theorem extreme_slope_of_sign
    (b : Bool) (initial value : ℚ) (h_initial : initial = -3 / 2 ∨ initial = 3 / 2)
    (h_sign : value = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue b : ℚ) * initial) :
    (1 / 2 - value / 3 : ℚ) = 0 ∨ (1 / 2 - value / 3 : ℚ) = 1 := by
  rw [h_sign]
  rcases h_initial with hi | hi <;> cases b <;> norm_num [AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue, hi]

end

end OAI.NumberTheory.PadicHodge.IntrinsicPurity.CM.ExtremeSlopesAdapter
