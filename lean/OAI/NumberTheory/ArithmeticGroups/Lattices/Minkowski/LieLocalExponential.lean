import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieTangent

/-! # Lie Local Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential.Construction

noncomputable section

/-! Every sufficiently small real Minkowski Lie automorphism is the
exponential of an intrinsic adjoint operator. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise _root_.Topology
open NormedSpace Filter

theorem hasStrictFDerivAt_exp_linear_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (a : E →L[ℝ] A) :
    HasStrictFDerivAt (fun x => exp (a x)) a 0 := by
  have he : HasStrictFDerivAt exp (1 : A →L[ℝ] A) (a 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    (HasStrictFDerivAt.comp (0 : E) (f := a) (g := exp) he a.hasStrictFDerivAt)

local instance lieMixedSpan_normed_uniform_for_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

local instance lieMixedOperator_topologicalRing_for_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    IsTopologicalRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (inferInstance : NonUnitalSeminormedRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G))

theorem lieMixed_near_identity_is_exponential
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∀ᶠ T in 𝓝 (1 : Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G),
      (∀ A B, T (LieBracket.Construction.lieMixedBracket G hG A B) =
        LieBracket.Construction.lieMixedBracket G hG (T A) (T B)) →
      ∃ A : Lie.MixedLattice.Construction.lieMixedSpan G, exp (LieTangent.Construction.lieMixedContinuousBracket G hG A) = T := by
  let : CompleteSpace (Lie.MixedLattice.Construction.lieMixedSpan G) := FiniteDimensional.complete ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)
  let B := LieTangent.Construction.lieMixedContinuousBracket G hG
  have hD (A X Y : Lie.MixedLattice.Construction.lieMixedSpan G) : B A (B X Y) = B (B A X) Y + B X (B A Y) :=
    leibniz_lie (L₁ := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG)
      (L₂ := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG) (M := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG) A X Y
  exact Bilinear.StabilizerLocalImage.Construction.bilinear_stabilizer_local_image B (fun A => exp (B A)) B
    (by rw [map_zero, exp_zero])
    (hasStrictFDerivAt_exp_linear_zero (E := Lie.MixedLattice.Construction.lieMixedSpan G)
      (A := Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) B)
    (LieTangent.Construction.lieMixedContinuousBracket_injective G hG hsemi)
    (LieTangent.Construction.lieMixedContinuousBracket_derivation_kernel G hG hsemi).symm
    (fun A => Bilinear.DerivationExponential.Construction.exp_continuousLinearMap_injective (B A))
    (fun A X Y => Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (B A) (hD A) X Y)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential.Construction
