import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators
import OAI.RepresentationTheory.Theta.Generators
import OAI.RepresentationTheory.Theta.Convergence

/-! # Substitution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Substitution.CM

noncomputable section

/-! Rational matrix substitution preserves the actual theta sum by
an explicit bijective relabeling of rational points. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def raw (A : (Matrix I I ℚ)ˣ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F x := F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem diagonal_apply (A : (Matrix I I ℚ)ˣ) (x : I → ℚ) :
    (A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A x) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) A.val.transpose x i).symm

theorem theta_invariant (A : (Matrix I I ℚ)ˣ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (∑' x : I → ℚ, raw A F (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F := by
  calc
    _ = ∑' x : I → ℚ, F.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A x)) := by
      apply tsum_congr
      intro x
      change F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x) = _
      rw [diagonal_apply]
    _ = _ := (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A).tsum_eq (fun x => F.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x))

omit [DecidableEq I] in
theorem phase_fst (A : Matrix I I ℚ) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (fun i => ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).1) =
      A.map (algebraMap ℚ ℝ) *ᵥ (fun i => (x i).1) := by
  funext i
  change (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i) = _
  rw [RingHom.map_mulVec]
  rfl

omit [DecidableEq I] in
theorem phase_snd (A : Matrix I I ℚ) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (fun i => ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).2) =
      A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ (fun i => (x i).2) := by
  funext i
  change (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i) = _
  rw [RingHom.map_mulVec]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Substitution.CM
