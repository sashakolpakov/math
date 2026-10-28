import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs

/-! # Poincare Zero Geometry -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original abelian zero section controls global functions on
the actual dual-by-abelian product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual_smooth : Smooth U.prescribedPoincareDual.left :=
  MorphismProperty.of_isPullback (U.prescribedPoincare_square.map (Over.forget _)).flip
    (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual_proper : IsProper U.prescribedPoincareDual.left :=
  MorphismProperty.of_isPullback (U.prescribedPoincare_square.map (Over.forget _)).flip
    (inferInstanceAs (IsProper U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual_connected : GeometricallyConnected U.prescribedPoincareDual.left :=
  MorphismProperty.of_isPullback (U.prescribedPoincare_square.map (Over.forget _)).flip
    (inferInstanceAs (GeometricallyConnected U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincare_globalFunctions [IsReduced X.left] [IsLocallyNoetherian X.left] :
    Function.Surjective U.prescribedPoincareDual.left.appTop := by
  have : IsIso U.prescribedPoincareDual.left.appTop :=
    Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_appTop U.prescribedPoincareDual.left
      U.prescribedPoincareZero.left (congrArg Over.Hom.left U.prescribedPoincareZero_dual)
  exact (ConcreteCategory.bijective_of_isIso _).surjective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
