import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs

/-! # Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The Poincare overlap is a proper smooth abelian family over the
dual overlap. Its zero section identifies global functions, giving the
rigidity needed to normalize the overlap line-bundle isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual_square :
    IsPullback (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection) (U.prescribedPoincareOverlapDual π)
      U.prescribedPoincareDual (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) := by
  have hb : U.prescribedPoincareOverlapDual π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection := pullback.lift_snd _ _ _
  have ho : IsPullback (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)
      (U.prescribedPoincareOverlapDual π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
      (U.prescribedPoincareDual ≫ (U.prescribedDualProjection ≫ π)) π := by
    rw [hb, ← Category.assoc]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_bot (U.prescribedPoincareOverlapDual_source π).symm (IsPullback.of_hasPullback _ _)

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual_smooth : Smooth (U.prescribedPoincareOverlapDual π).left := by
  have : Smooth U.prescribedPoincareDual.left := MorphismProperty.of_isPullback
    (U.prescribedPoincare_square.map (Over.forget _)).flip
      (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  exact MorphismProperty.of_isPullback (U.prescribedPoincareOverlapDual_square π |>.map (Over.forget _))
    (inferInstanceAs (Smooth U.prescribedPoincareDual.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual_proper : IsProper (U.prescribedPoincareOverlapDual π).left := by
  have : IsProper U.prescribedPoincareDual.left := MorphismProperty.of_isPullback
    (U.prescribedPoincare_square.map (Over.forget _)).flip
      (inferInstanceAs (IsProper U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  exact MorphismProperty.of_isPullback (U.prescribedPoincareOverlapDual_square π |>.map (Over.forget _))
    (inferInstanceAs (IsProper U.prescribedPoincareDual.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual_connected : GeometricallyConnected (U.prescribedPoincareOverlapDual π).left := by
  have : GeometricallyConnected U.prescribedPoincareDual.left := MorphismProperty.of_isPullback
    (U.prescribedPoincare_square.map (Over.forget _)).flip
      (inferInstanceAs (GeometricallyConnected U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  exact MorphismProperty.of_isPullback (U.prescribedPoincareOverlapDual_square π |>.map (Over.forget _))
    (inferInstanceAs (GeometricallyConnected U.prescribedPoincareDual.left))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapZero_globalFunctions
    [IsReduced X.left] [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] :
    Function.Bijective (U.prescribedPoincareZeroOverlap π).left.appTop := by
  have h : (U.prescribedPoincareZeroOverlap π).left ≫ (U.prescribedPoincareOverlapDual π).left = 𝟙 _ :=
    congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_dual π)
  have : IsIso (U.prescribedPoincareZeroOverlap π).left.appTop :=
    (Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.iso (U.prescribedPoincareOverlapDual π).left
      (U.prescribedPoincareZeroOverlap π).left h).isIso_inv
  exact ConcreteCategory.bijective_of_isIso _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
