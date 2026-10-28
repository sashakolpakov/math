import OAI.NumberTheory.ArithmeticGroups.Lattices.AutomorphismAdjointDerivations

/-! # Preserving Curve Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.PreservingCurveTangent.Construction

noncomputable section

/-! A differentiable curve of bracket-preserving operators through the
identity has a bracket derivation as its tangent vector. -/

theorem bilinear_preserving_curve_tangent
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (f : ℝ → L →L[ℝ] L) (A : L →L[ℝ] L)
    (hf : HasDerivAt f A 0) (h0 : f 0 = 1)
    (hB : ∀ t x y, f t (B x y) = B (f t x) (f t y)) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 := by
  apply (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B A).mpr
  intro x y
  have hx := hf.clm_apply (hasDerivAt_const (0 : ℝ) x)
  have hy := hf.clm_apply (hasDerivAt_const (0 : ℝ) y)
  have hright := (B.hasFDerivAt.comp_hasDerivAt 0 hx).clm_apply hy
  have hleft := hf.clm_apply (hasDerivAt_const (0 : ℝ) (B x y))
  have heq : (fun t => f t (B x y)) = fun t => B (f t x) (f t y) := funext (fun t => hB t x y)
  rw [heq] at hleft
  have he := hleft.unique hright
  simpa only [Function.comp_apply, h0, one_apply_eq_self, map_zero, add_zero] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.PreservingCurveTangent.Construction
