import OAI.AlgebraicGeometry.FormalGeometry.Completion.Spectral

/-! # Regular Spectrum Transfer -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSpectrumTransfer.Construction

noncomputable section

/-! The regular characteristic polynomial transfers its complex root
bounds to every opposite-algebra representation. -/

theorem algebraic_and_conjugates_of_regular_spectrum
    {D : Type*} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W]
    [Algebra ℚ (Module.End L W)] [IsScalarTower ℚ L (Module.End L W)]
    (ρ : Dᵐᵒᵖ →ₐ[ℚ] Module.End L W) (π : D) (q : ℝ)
    (hbound : ∀ z : ℂ, Module.End.HasEigenvalue ((Algebra.lmul ℚ D π).baseChange ℂ) z →
      ‖z‖ = Real.sqrt q)
    (α : L) (hα : (ρ (MulOpposite.op π)).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧ ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = Real.sqrt q := by
  let P := (Algebra.lmul ℚ D π).charpoly
  have hP : P ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
  have hF : Polynomial.aeval (ρ (MulOpposite.op π)) (P.map (algebraMap ℚ L)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_op_apply]
    rw [Algebra.aeval_self_charpoly_lmul, MulOpposite.op_zero, map_zero]
  have hr := Spectral.Construction.eigenvalue_isRoot_of_annihilating_polynomial _ _ hF α hα
  have hαP : Polynomial.aeval α P = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hr
  refine ⟨⟨P, hP, hαP⟩, ?_⟩
  intro z hz
  have hzP : Polynomial.aeval z P = 0 := by
    obtain ⟨R, hR⟩ := minpoly.dvd ℚ α hαP
    rw [hR, map_mul, hz, zero_mul]
  apply hbound z
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly ((Algebra.lmul ℚ D π).baseChange ℂ) z).mpr
  simpa only [LinearMap.charpoly_baseChange, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hzP

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSpectrumTransfer.Construction
