import OAI.NumberTheory.PadicHodge.ScalarExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial

/-! # Summand Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SummandPolynomial.CM

noncomputable section

/-! Polynomial identities and commutation restrict to actual invariant
subspaces and survive coefficient extension. The restricted Frobenius
may be any of the comparison witnesses satisfying its inclusion equation. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM

variable {F V U : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup U] [Module F U]

theorem commute_on_injective_intertwiner
    (j : U →ₗ[F] V) (hj : Function.Injective j)
    (f g : Module.End F V) (f' g' : Module.End F U)
    (hf : ∀ x, j (f' x) = f (j x)) (hg : ∀ x, j (g' x) = g (j x))
    (hc : Commute f g) : Commute f' g' := by
  apply LinearMap.ext
  intro x
  apply hj
  simpa only [Module.End.mul_apply, hf, hg] using congrArg (fun a => a (j x)) hc.eq

theorem polynomial_on_injective_intertwiner
    (q : ℕ) (j : U →ₗ[F] V) (hj : Function.Injective j)
    (f : Module.End F V) (f' : Module.End F U)
    (T : Fin 3 → Module.End F V) (T' : Fin 3 → Module.End F U)
    (hf : ∀ x, j (f' x) = f (j x)) (hT : ∀ i x, j (T' i x) = T i (j x))
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f T = 0) : Ordinary.Polynomial.CM.heckePolynomialValue q f' T' = 0 := by
  apply LinearMap.ext
  intro x
  apply hj
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.zero_apply, map_sub, map_add, map_nsmul, map_zero, hf, hT] using
      congrArg (fun a => a (j x)) hp

theorem polynomial_baseChange (q : ℕ) (L : Type*) [Field L] [Algebra F L]
    (f : Module.End F V) (T : Fin 3 → Module.End F V)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (f.baseChange L) (fun i => (T i).baseChange L) = 0 := by
  change Ordinary.Polynomial.CM.heckePolynomialValue q ((Module.End.baseChangeHom F L V) f)
    (fun i => (Module.End.baseChangeHom F L V) (T i)) = 0
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, map_sub, map_add, map_mul, map_pow,
    map_nsmul, map_zero] using congrArg (Module.End.baseChangeHom F L V) hp

variable {I : Type*} (T : I → Module.End F V) (χ : I → F)
  (hcomm : ∀ i j, Commute (T i) (T j))

theorem restrictedHecke_commute (i j : I) :
    Commute (NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke T χ hcomm i) (NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke T χ hcomm j) :=
  commute_on_injective_intertwiner (NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ).subtype
    Subtype.val_injective (T i) (T j) _ _ (fun _ => rfl) (fun _ => rfl) (hcomm i j)

theorem restrictedFrobenius_commute
    (f : Module.End F V)
    (fS : Module.End F (NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ))
    (hincl : ∀ x : NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ, (fS x : V) = f (x : V))
    (hfcomm : ∀ i, Commute f (T i)) (i : I) :
    Commute fS (NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke T χ hcomm i) :=
  commute_on_injective_intertwiner (NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ).subtype
    Subtype.val_injective f (T i) _ _ hincl (fun _ => rfl) (hfcomm i)

theorem restricted_polynomial (q : ℕ)
    (f : Module.End F V)
    (fS : Module.End F (NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ))
    (hincl : ∀ x : NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ, (fS x : V) = f (x : V))
    (idx : Fin 3 → I) (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f (fun i => T (idx i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q fS (fun i => NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke T χ hcomm (idx i)) = 0 :=
  polynomial_on_injective_intertwiner q (NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand T χ).subtype
    Subtype.val_injective f fS _ _ hincl (fun _ _ => rfl) hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SummandPolynomial.CM
