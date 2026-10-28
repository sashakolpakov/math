import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviComparison

/-! # Linear -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Linear.CM

noncomputable section

/-! The rational Levi lift has exactly the prescribed coordinate
substitution. Its scalar is fixed by the nonzero theta functional and
bijective rational relabeling. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviOperators.CM
variable (n : ℕ)

theorem action_scalar (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (A : (Matrix (Fin n) (Fin n) ℚ)ˣ)
    (hγ : γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose) :
    ∃ c : ℂ, ∀ (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ),
      (Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) F).val x =
        c * F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x) := by
  have hp : (Constructed.ConstructedAdelicGroup.CM.projection n (Split.CM.split n γ)).val =
      Adelic.ScalarComparison.CM.pairMatrix n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) := by
    rw [Split.CM.split_covers, LeviComparison.CM.pair_matrix]
    exact congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ => M.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) hγ
  obtain ⟨c, _, hc⟩ := Adelic.ScalarComparison.CM.scalar n (Split.CM.split n γ) (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) hp
  refine ⟨c * LeviComparison.CM.scalar n A, ?_⟩
  intro F x
  have h := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) => f.val x) (hc F)
  change (Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) F).val x =
    c * (Adelic.ScalarComparison.CM.pairOperator n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) F).val x at h
  rw [LeviComparison.CM.operator_apply, ← mul_assoc] at h
  exact h

theorem rational_linear (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (A : (Matrix (Fin n) (Fin n) ℚ)ˣ)
    (hγ : γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) F).val x =
      F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x) := by
  obtain ⟨c, hc⟩ := action_scalar n γ A hγ
  let Φ := Theta.Nonzero.CM.test (Fin n)
  have hsum : RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) Φ) =
      c * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ := by
    calc
      _ = ∑' y : Fin n → ℚ, c * Substitution.CM.raw A Φ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal y) :=
        tsum_congr (fun y => hc Φ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal y))
      _ = _ := by rw [tsum_mul_left, Substitution.CM.theta_invariant]
  rw [Split.CM.theta_invariant] at hsum
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ (Theta.Nonzero.CM.theta_ne_zero (Fin n))
    change c * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ = 1 * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ
    rw [one_mul]
    exact hsum.symm
  rw [hc, hc1, one_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Linear.CM
