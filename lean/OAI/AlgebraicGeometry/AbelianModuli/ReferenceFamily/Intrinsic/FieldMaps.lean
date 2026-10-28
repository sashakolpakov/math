import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction

/-! # Field Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps.IntrinsicNumberFieldAction

noncomputable section

/-! Actual algebraic endomorphisms commuting with the integral PEL
action induce E-linear maps on the native rational period space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

omit [NumberField E] [Algebra ℚ E] in
theorem rationalAction_eq_lift (a : NumberField.RingOfIntegers E) :
    NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a = IntegralMaps.IntrinsicLinearMaps.rationalLift (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P (ρ.map a)) := rfl

omit [NumberField E] [Algebra ℚ E] in
theorem rationalAction_commute (f : A.scheme ⟶ A.scheme) [IsMonHom f]
    (hf : ∀ a, ρ.map a ≫ f = f ≫ ρ.map a) (a : NumberField.RingOfIntegers E) :
    Commute (NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a) (IntegralMaps.IntrinsicLinearMaps.rationalLift (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f)) := by
  let F := LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f
  let R := LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P (ρ.map a)
  have h : F ≫ R = R ≫ F := (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism_comp A P f (ρ.map a)).symm.trans
    ((congrArg (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P) (hf a).symm).trans
      (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism_comp A P (ρ.map a) f))
  change (IntegralMaps.IntrinsicLinearMaps.rationalLift R).comp (IntegralMaps.IntrinsicLinearMaps.rationalLift F) = (IntegralMaps.IntrinsicLinearMaps.rationalLift F).comp (IntegralMaps.IntrinsicLinearMaps.rationalLift R)
  exact (IntegralMaps.IntrinsicLinearMaps.rationalLift_comp F R).symm.trans
    ((IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ h).trans (IntegralMaps.IntrinsicLinearMaps.rationalLift_comp R F))

/-- E-linearity is a consequence of the actual integral intertwining
equations and the constructed field extension of the action. -/
def fieldLinearMap (f : A.scheme ⟶ A.scheme) [IsMonHom f]
    (hf : ∀ a, ρ.map a ≫ f = f ≫ ρ.map a) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) →ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  refine {
    toFun := IntegralMaps.IntrinsicLinearMaps.rationalLift (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f)
    map_add' := (IntegralMaps.IntrinsicLinearMaps.rationalLift (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f)).map_add
    map_smul' := ?_ }
  intro a v
  exact Integral.ActionExtension.extendIntegralAction_end_commute_apply (NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ)
    (IntegralMaps.IntrinsicLinearMaps.rationalLift (LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f)) (rationalAction_commute A P ρ f hf) a v

/-- A PEL-compatible algebraic group automorphism gives an actual
E-linear automorphism of the native rational period space. -/
def fieldLinearIso (e : A.scheme ≅ A.scheme) [IsMonHom e.hom]
    (he : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ ρ.map a) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let e' := LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphismIso A P e
  let : IsMonHom e'.hom := LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism_isMonHom A P e.hom
  exact LinearEquiv.ofBijective (fieldLinearMap A P ρ e.hom he) (IntegralMaps.IntrinsicLinearMaps.rationalLiftIso e').bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps.IntrinsicNumberFieldAction
