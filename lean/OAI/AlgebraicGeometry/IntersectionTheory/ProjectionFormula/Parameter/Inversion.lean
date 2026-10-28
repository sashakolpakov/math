import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place

/-! # Inversion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Inversion

noncomputable section

/-! Replacing a transcendental parameter by its inverse preserves its
extension degree. The comparison uses the explicit inversion automorphism
of the rational function field and the actual evaluation embeddings. -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place

variable (k : Type) [Field k]

theorem parameter_transcendental : Transcendental k (ProjectionFormula.Polynomial.Place.parameter k) := by
  intro h
  apply Polynomial.transcendental_X k
  exact (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k)))
    (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))).mp h

theorem inverse_parameter_transcendental : Transcendental k (ProjectionFormula.Polynomial.Place.parameter k)⁻¹ := by
  intro h
  apply parameter_transcendental k
  simpa only [inv_inv] using h.inv

def parameterHom (L : Type) [Field L] [Algebra k L] (g : L) (hg : Transcendental k g) :
    FractionRing (Polynomial k) →ₐ[k] L :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hg)

theorem parameterHom_parameter (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) : parameterHom k L g hg (ProjectionFormula.Polynomial.Place.parameter k) = g := by
  rw [parameterHom, IsFractionRing.liftAlgHom_apply, ProjectionFormula.Polynomial.Place.parameter, IsFractionRing.lift_algebraMap]
  exact Polynomial.aeval_X g

theorem hom_ext_parameter {L : Type} [Field L] [Algebra k L]
    (a b : FractionRing (Polynomial k) →ₐ[k] L) (h : a (ProjectionFormula.Polynomial.Place.parameter k) = b (ProjectionFormula.Polynomial.Place.parameter k)) : a = b := by
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
  parameterHom k _ (ProjectionFormula.Polynomial.Place.parameter k)⁻¹ (inverse_parameter_transcendental k)

theorem inversion_parameter : inversion k (ProjectionFormula.Polynomial.Place.parameter k) = (ProjectionFormula.Polynomial.Place.parameter k)⁻¹ :=
  parameterHom_parameter k _ _ _

theorem inversion_involutive : Function.Involutive (inversion k) := by
  have h : (inversion k).comp (inversion k) = AlgHom.id k (FractionRing (Polynomial k)) := by
    apply hom_ext_parameter k
    change inversion k (inversion k (ProjectionFormula.Polynomial.Place.parameter k)) = ProjectionFormula.Polynomial.Place.parameter k
    rw [inversion_parameter, map_inv₀, inversion_parameter, inv_inv]
  intro x
  exact DFunLike.congr_fun h x

def inversionEquiv : FractionRing (Polynomial k) ≃ₐ[k] FractionRing (Polynomial k) :=
  AlgEquiv.ofBijective (inversion k) (inversion_involutive k).bijective

theorem parameterHom_inv (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) (hgi : Transcendental k g⁻¹) :
    (parameterHom k L g hg).comp (inversion k) = parameterHom k L g⁻¹ hgi := by
  apply hom_ext_parameter k
  change parameterHom k L g hg (inversion k (ProjectionFormula.Polynomial.Place.parameter k)) = parameterHom k L g⁻¹ hgi (ProjectionFormula.Polynomial.Place.parameter k)
  rw [inversion_parameter, map_inv₀, parameterHom_parameter, parameterHom_parameter]

/-- The two actual evaluation algebra structures have equal degree. -/
theorem parameter_finrank_inv (L : Type) [Field L] [Algebra k L]
    (g : L) (hg : Transcendental k g) (hgi : Transcendental k g⁻¹) :
    @Module.finrank (FractionRing (Polynomial k)) L _ _
      (CurveParameter.fractionAlgebra k L g hg).toModule =
    @Module.finrank (FractionRing (Polynomial k)) L _ _
      (CurveParameter.fractionAlgebra k L g⁻¹ hgi).toModule := by
  let a := CurveParameter.fractionAlgebra k L g hg
  let b := CurveParameter.fractionAlgebra k L g⁻¹ hgi
  have he : (RingHom.id L).comp (parameterHom k L g⁻¹ hgi).toRingHom =
      (parameterHom k L g hg).toRingHom.comp (inversionEquiv k).toRingHom := by
    exact congrArg AlgHom.toRingHom (parameterHom_inv k L g hg hgi).symm
  exact (@Algebra.finrank_eq_of_equiv_equiv (FractionRing (Polynomial k)) L _ _ b
    (FractionRing (Polynomial k)) L _ _ a (inversionEquiv k).toRingEquiv (RingEquiv.refl L) he.symm).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Inversion
