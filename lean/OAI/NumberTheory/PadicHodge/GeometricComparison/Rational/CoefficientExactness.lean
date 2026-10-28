import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ProEtaleCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators

/-! # Coefficient Exactness -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CoefficientExactness.RationalProEtaleCoefficients

noncomputable section

section

/-! Injectivity and uniform denominators for the actual integral-to-rational coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem coefficientInclusion_injective (T : Type*) [TopologicalSpace T] :
    Function.Injective (ProEtaleCoefficients.RationalProEtaleCoefficients.coefficientInclusion ℓ T) := by
  intro s t h
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f : C(T, IntegralComparison.Cohomology.Coeff.{0} ℓ) => (f x).down) h

instance integralInclusion_mono (X : Scheme.{0}) : Mono (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) where
  right_cancellation := by
    intro G f g h
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply coefficientInclusion_injective ℓ U.unop.left
    exact congrArg (fun k : G ⟶ ProEtaleCoefficients.RationalProEtaleCoefficients.additiveSheaf ℓ X => k.hom.app U s) h

theorem sections_denominator (X : Scheme.{0}) (U : X.ProEt) [CompactSpace U.left]
    (s : (ProEtaleCoefficients.RationalProEtaleCoefficients.additiveSheaf ℓ X).obj.obj (op U)) :
    ∃ N : ℕ, ∃ t : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).obj.obj (op U),
      (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X).hom.app (op U) t = (ℓ ^ N) • s := by
  let f : C(U.left, IntegralComparison.Cohomology.Coeff.{0} ℓ) := s
  let f' : C(U.left, ℚ_[ℓ]) := ⟨fun x => (f x).down,
    continuous_uliftDown.comp f.continuous⟩
  obtain ⟨N, g, hg⟩ := ContinuousDenominators.PadicContinuousDenominators.exists_denominator ℓ f'
  refine ⟨N, ULift.up g, ?_⟩
  change ProEtaleCoefficients.RationalProEtaleCoefficients.coefficientInclusion ℓ U.left (ULift.up g) = (ℓ ^ N) • f
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change (g x : ℚ_[ℓ]) = (ℓ ^ N) • (f x).down
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    (show (g x : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) ^ N * (f x).down from (hg x).symm)

end

/-! The actual coefficient inclusion and its cokernel give the cohomology exact sequence used to lift rational classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0})

def coefficientSequence : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{1}) :=
  ShortComplex.mk (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) (cokernel.π (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X))
    (cokernel.condition (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X))

theorem coefficientSequence_shortExact : (coefficientSequence ℓ X).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)))
    (inferInstanceAs (Mono (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)))
    (inferInstanceAs (Epi (cokernel.π (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X))))

theorem cohomology_lift_of_cokernel_zero (n : ℕ) (x : (ProEtaleCoefficients.RationalProEtaleCoefficients.additiveSheaf ℓ X).H n)
    (hx : Sheaf.H.map (cokernel.π (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)) n x = 0) :
    ∃ y : X.EllAdicCohomology ℓ n, Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n y = x :=
  Ext.covariant_sequence_exact₂ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X)
    (coefficientSequence_shortExact ℓ X) x hx

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CoefficientExactness.RationalProEtaleCoefficients
