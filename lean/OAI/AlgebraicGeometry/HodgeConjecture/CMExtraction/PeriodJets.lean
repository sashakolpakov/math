import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality
import Mathlib.RingTheory.DualNumber

/-! # Period Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets

noncomputable section

/-! Actual first-order affine period tests: value plus directional derivative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality Filter
open scoped _root_.Topology

/-- The dual-number point records the actual value and complex directional derivative. -/
def firstOrderEvaluation (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) : RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x →ₐ[ℂ] DualNumber ℂ where
  toFun f := (f.val x, fderiv ℂ f.val x u)
  map_zero' := by
    apply TrivSqZeroExt.ext
    · rfl
    change fderiv ℂ (fun _ : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates => (0 : ℂ)) x u = 0
    simp only [fderiv_const_apply, zero_apply]
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    change fderiv ℂ (fun _ : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates => (1 : ℂ)) x u = 0
    simp only [fderiv_const_apply, zero_apply]
  map_add' f g := by
    apply TrivSqZeroExt.ext
    · rfl
    change fderiv ℂ (fun y => f.val y + g.val y) x u =
      fderiv ℂ f.val x u + fderiv ℂ g.val x u
    exact congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates →L[ℂ] ℂ => L u) (fderiv_add f.property g.property)
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · rfl
    change fderiv ℂ (fun y => f.val y * g.val y) x u =
      f.val x * fderiv ℂ g.val x u + fderiv ℂ f.val x u * g.val x
    have h := congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates →L[ℂ] ℂ => L u) (fderiv_mul f.property g.property)
    exact h.trans (by simp only [add_apply, smul_apply, smul_eq_mul]; ring)
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    change fderiv ℂ (fun _ : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates => c) x u = 0
    simp only [fderiv_const_apply, zero_apply]

theorem firstOrderEvaluation_value (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (firstOrderEvaluation x u) = RepresentationTheory.Theta.Geometric.DifferentialNaturality.evaluateAt x := by
  ext f
  rfl

theorem firstOrderEvaluation_derivative (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (f : RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) :
    (firstOrderEvaluation x u f).snd = RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x (KaehlerDifferential.D ℂ (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) f) u := by
  rw [RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential_D]
  rfl

theorem firstOrderEvaluation_germ (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (f g : RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x)
    (h : f.val =ᶠ[𝓝 x] g.val) :
    firstOrderEvaluation x u f = firstOrderEvaluation x u g := by
  apply TrivSqZeroExt.ext
  · exact h.eq_of_nhds
  exact congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates →L[ℂ] ℂ => L u) h.fderiv_eq

/-- Every prime of the dual numbers contains the infinitesimal direction. -/
theorem dualNumber_prime_contains_epsilon (p : PrimeSpectrum (DualNumber ℂ)) :
    (DualNumber.eps : DualNumber ℂ) ∈ p.asIdeal := by
  have h : (DualNumber.eps : DualNumber ℂ) ^ 2 ∈ p.asIdeal := by
    rw [DualNumber.eps_pow_two]
    exact p.asIdeal.zero_mem
  exact p.isPrime.mem_of_pow_mem 2 h

theorem dualNumber_prime_eq_epsilon (p : PrimeSpectrum (DualNumber ℂ)) :
    p.asIdeal = Ideal.span {(DualNumber.eps : DualNumber ℂ)} := by
  symm
  apply (DualNumber.isMaximal_span_singleton_eps (K := ℂ)).eq_of_le p.isPrime.ne_top
  exact Ideal.span_le.mpr (by
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact dualNumber_prime_contains_epsilon p)

instance dualNumberSpectrum_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  refine ⟨fun p q => ?_⟩
  apply PrimeSpectrum.ext
  exact (dualNumber_prime_eq_epsilon p).trans (dualNumber_prime_eq_epsilon q).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets
