import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal

/-! # Lie Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieTangent.Construction

noncomputable section

/-! Continuous adjoint operators and the exact tangent kernel of the
real Minkowski Lie-automorphism equations. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

attribute [local instance] LieRing.ofAssociativeRing

local instance lieMixedSpan_normed_uniform_for_tangent
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_tangent
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

def lieMixedContinuousBracket
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G :=
  Lie.AutomorphismTransversal.Construction.finiteContinuousBilinear (AdjointOperator.Construction.lieMixedAdjointLinear G hG)

theorem lieMixedContinuousBracket_apply
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A B : Lie.MixedLattice.Construction.lieMixedSpan G) :
    lieMixedContinuousBracket G hG A B = LieBracket.Construction.lieMixedBracket G hG A B := rfl

theorem lieMixedContinuousBracket_injective
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    Function.Injective (lieMixedContinuousBracket G hG) := by
  apply (injective_iff_map_eq_zero (lieMixedContinuousBracket G hG)).mpr
  intro A hA
  have hz : AdjointOperator.Construction.lieMixedAdjoint G hG A = 0 := by
    apply LinearMap.ext
    intro B
    exact DFunLike.congr_fun hA B
  apply (KillingForm.Construction.lieMixedKillingForm_nondegenerate G hG hsemi).1 A
  intro B
  change LinearMap.trace ℝ (Lie.MixedLattice.Construction.lieMixedSpan G) (AdjointOperator.Construction.lieMixedAdjoint G hG A * AdjointOperator.Construction.lieMixedAdjoint G hG B) = 0
  rw [hz, zero_mul, map_zero]

theorem lieMixedContinuousBracket_derivation_kernel
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LinearMap.ker (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (lieMixedContinuousBracket G hG)).toLinearMap =
      LinearMap.range (lieMixedContinuousBracket G hG).toLinearMap := by
  ext T
  constructor
  · intro hT
    have hD : T.toLinearMap ∈
        LinearMap.ker (Lie.DerivationDefect.Construction.lieDerivationDefect ℝ (Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG)) := by
      apply LinearMap.ext
      intro A
      apply LinearMap.ext
      intro B
      exact DFunLike.congr_fun (DFunLike.congr_fun hT A) B
    rw [Lie.DerivationDefect.Construction.lieMixed_derivationDefect_ker G hG hsemi] at hD
    obtain ⟨A, hA⟩ := hD
    refine ⟨A, ?_⟩
    apply ContinuousLinearMap.ext
    intro B
    exact DFunLike.congr_fun hA B
  · rintro ⟨A, rfl⟩
    apply ContinuousLinearMap.ext
    intro B
    apply ContinuousLinearMap.ext
    intro C
    exact DFunLike.congr_fun (DFunLike.congr_fun
      (Lie.DerivationDefect.Construction.lieDerivationDefect_ad (R := ℝ) (L := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG) A) B) C

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieTangent.Construction
