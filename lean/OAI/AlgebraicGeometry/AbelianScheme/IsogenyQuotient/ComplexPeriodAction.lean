import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction

/-! # Complex Period Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexPeriodAction.Construction

noncomputable section

/-!
The actual HilbertConstruction complex abelian scheme has a rational period–Tate
comparison compatible with its original integral action. The source
action is the concrete number-field action on the native rational periods.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction

theorem rationalTateMap_congr {S : Scheme} {X Y : Over S}
    [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    (T : Over S) (q : ℕ) [Fact q.Prime] (f g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
    (h : f = g) : TateComparison.Rational.rationalTateMap (T := T) (q := q) f = TateComparison.Rational.rationalTateMap (T := T) (q := q) g := by
  cases h
  rfl

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) (q : ℕ) [Fact q.Prime]

def complexPeriodTateComparison :
    ℚ_[q] ⊗[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[ℚ_[q]]
      TateComparison.Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (TateComparison.RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).trans
    (LinearEquiv.baseChange ℤ_[q] ℚ_[q] _ _ (TateComparison.TateProducts.Tate.mapEquiv q (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativePointEquiv A P).toAdditive))

theorem complexPeriodTateComparison_toLinearMap :
    (complexPeriodTateComparison A P q).toLinearMap =
      (TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom).comp
        (TateComparison.RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).toLinearMap := rfl

variable {E : Type} [Field E] [NumberField E]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

omit [NumberField E] in
theorem complexPeriodTateComparison_action (a : NumberField.RingOfIntegers E) :
    (TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a)).comp
      (complexPeriodTateComparison A P q).toLinearMap =
      (complexPeriodTateComparison A P q).toLinearMap.comp
        ((AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a).baseChange ℚ_[q]) := by
  have he : (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ ρ.map a = AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a ≫ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom := by
    simp only [AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hT := rationalTateMap_congr (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q _ _ he
  rw [complexPeriodTateComparison_toLinearMap,
    ← LinearMap.comp_assoc, ← TateComparison.Functor.rationalTateMap_comp, hT, TateComparison.Functor.rationalTateMap_comp,
    LinearMap.comp_assoc, TateComparison.RationalPeriodNaturality.rationalPeriodTate_natural]
  rw [LinearMap.comp_assoc]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexPeriodAction.Construction
