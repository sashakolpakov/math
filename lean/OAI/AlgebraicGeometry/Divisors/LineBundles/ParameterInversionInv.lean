import OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place

/-! # Parameter Inversion Inv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterInversionInv.BundleCycles.ParameterInversion

noncomputable section

/-! Replacing a transcendental parameter by its inverse preserves its
extension degree. The comparison uses the explicit inversion automorphism
of the rational function field and the actual evaluation embeddings. -/

open OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage.BundleCycles.CurveParameter OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace

variable (k : Type) [Field k]

theorem parameter_transcendental : Transcendental k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k) := by
  intro h
  apply Polynomial.transcendental_X k
  exact (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k)))
    (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))).mp h

theorem inverse_parameter_transcendental : Transcendental k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)⁻¹ := by
  intro h
  apply parameter_transcendental k
  simpa only [inv_inv] using h.inv

def parameterHom (L : Type) [Field L] [Algebra k L] (g : L) (hg : Transcendental k g) :
    FractionRing (Polynomial k) →ₐ[k] L :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hg)

theorem parameterHom_parameter (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) : parameterHom k L g hg (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k) = g := by
  rw [parameterHom, IsFractionRing.liftAlgHom_apply, LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter, IsFractionRing.lift_algebraMap]
  exact Polynomial.aeval_X g

theorem hom_ext_parameter {L : Type} [Field L] [Algebra k L]
    (a b : FractionRing (Polynomial k) →ₐ[k] L) (h : a (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k) = b (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)) : a = b := by
  have hp : a.comp (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k))) =
      b.comp (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k))) := by
    apply Polynomial.algHom_ext
    exact h
  have he : a.toRingHom = b.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := Polynomial k)
    intro p
    exact DFunLike.congr_fun hp p
  exact AlgHom.coe_ringHom_injective he

def inversion : FractionRing (Polynomial k) →ₐ[k] FractionRing (Polynomial k) :=
  parameterHom k _ (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)⁻¹ (inverse_parameter_transcendental k)

theorem inversion_parameter : inversion k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k) = (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)⁻¹ :=
  parameterHom_parameter k _ _ _

theorem inversion_involutive : Function.Involutive (inversion k) := by
  have h : (inversion k).comp (inversion k) = AlgHom.id k (FractionRing (Polynomial k)) := by
    apply hom_ext_parameter k
    change inversion k (inversion k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)) = LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k
    rw [inversion_parameter, map_inv₀, inversion_parameter, inv_inv]
  intro x
  exact DFunLike.congr_fun h x

def inversionEquiv : FractionRing (Polynomial k) ≃ₐ[k] FractionRing (Polynomial k) :=
  AlgEquiv.ofBijective (inversion k) (inversion_involutive k).bijective

theorem parameterHom_inv (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) (hgi : Transcendental k g⁻¹) :
    (parameterHom k L g hg).comp (inversion k) = parameterHom k L g⁻¹ hgi := by
  apply hom_ext_parameter k
  change parameterHom k L g hg (inversion k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)) = parameterHom k L g⁻¹ hgi (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k)
  rw [inversion_parameter, map_inv₀, parameterHom_parameter, parameterHom_parameter]

/-- The two actual evaluation algebra structures have equal degree. -/
theorem parameter_finrank_inv (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) (hgi : Transcendental k g⁻¹) :
    @Module.finrank (FractionRing (Polynomial k)) L _ _
      (CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg).toModule =
    @Module.finrank (FractionRing (Polynomial k)) L _ _
      (CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g⁻¹ hgi).toModule := by
  let a := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let b := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g⁻¹ hgi
  have he : (RingHom.id L).comp (parameterHom k L g⁻¹ hgi).toRingHom =
      (parameterHom k L g hg).toRingHom.comp (inversionEquiv k).toRingHom := by
    exact congrArg AlgHom.toRingHom (parameterHom_inv k L g hg hgi).symm
  exact (@Algebra.finrank_eq_of_equiv_equiv (FractionRing (Polynomial k)) L _ _ b
    (FractionRing (Polynomial k)) L _ _ a (inversionEquiv k).toRingEquiv (RingEquiv.refl L) he.symm).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterInversionInv.BundleCycles.ParameterInversion
