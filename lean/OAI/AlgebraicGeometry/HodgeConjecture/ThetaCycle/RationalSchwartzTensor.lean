import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicLocalFactorization
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzCoordinates

/-! # Rational Schwartz Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzTensor.CM

noncomputable section

/-! ThetaCycle: lift each supplied rational finite Schwartz input to an actual
native restricted tensor, preserving every function value and theta weight. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

def rationalFinitePrime : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace ℚ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩

theorem exists_rational_schwartz_tensor (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) :
    ∃ f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N, RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz ℚ N f = RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N φ :=
  AdelicLocalFactorization.CM.finite_schwartz_evaluation_surjective ℚ N rationalFinitePrime _

def rationalSchwartzTensor (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N :=
  (exists_rational_schwartz_tensor N φ).choose

theorem rational_schwartz_tensor_function (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz ℚ N (rationalSchwartzTensor N φ) = RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N φ :=
  (exists_rational_schwartz_tensor N φ).choose_spec

theorem rational_schwartz_tensor_principal (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) (x : Fin N → ℚ) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction ℚ N (rationalSchwartzTensor N φ)
        (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i)) =
      φ.val (fun i => algebraMap ℚ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf (x i)) := by
  have h := congrArg (fun f : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions ℚ N =>
      f.val (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i))) (rational_schwartz_tensor_function N φ)
  exact h.trans (RationalSchwartzCoordinates.CM.rational_schwartz_to_adelic_principal N φ x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzTensor.CM
