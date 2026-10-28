import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleBaseKernel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.ZeroRelation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs

/-! # Overlap Base -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The prescribed abelian-family overlap is a smooth proper family
over the actual PEL relation, with its actual zero section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine) (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

include hk in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedBaseKernelPair : IsKernelPair π (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) :=
  IsPullback.of_map (F := Over.forget _) (Over.OverMorphism.ext hk.w) hk

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase : U.prescribedOverlap π ⟶ IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L :=
  DescentCocycleBaseKernel.DescentCocycle.baseKernelProjection π U.prescribedProjection (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (U.prescribedBaseKernelPair hU π hk)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase_square :
    IsPullback (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection) (U.prescribedOverlapBase hU π hk)
      U.prescribedProjection (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) :=
  DescentCocycleBaseKernel.DescentCocycle.baseKernelProjection_square π U.prescribedProjection (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (U.prescribedBaseKernelPair hU π hk)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZeroOverlap_baseProjection :
    U.prescribedZeroOverlap hU π hk ≫ U.prescribedOverlapBase hU π hk = 𝟙 _ :=
  DescentCocycleBaseKernel.DescentCocycle.baseKernelSection_projection π U.prescribedProjection (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (U.prescribedBaseKernelPair hU π hk) U.prescribedZero U.prescribedZero_projection

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase_smooth : Smooth (U.prescribedOverlapBase hU π hk).left :=
  MorphismProperty.of_isPullback ((U.prescribedOverlapBase_square hU π hk).map (Over.forget _))
    (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase_proper : IsProper (U.prescribedOverlapBase hU π hk).left :=
  MorphismProperty.of_isPullback ((U.prescribedOverlapBase_square hU π hk).map (Over.forget _))
    (inferInstanceAs (IsProper U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase_connected : GeometricallyConnected (U.prescribedOverlapBase hU π hk).left :=
  MorphismProperty.of_isPullback ((U.prescribedOverlapBase_square hU π hk).map (Over.forget _))
    (inferInstanceAs (GeometricallyConnected U.forgetAuxiliary.data.polarized.abelian.scheme.hom))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapBase_globalFunctions [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] :
    Function.Surjective (U.prescribedOverlapBase hU π hk).left.appTop := by
  have : IsIso (U.prescribedOverlapBase hU π hk).left.appTop :=
    Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_appTop (U.prescribedOverlapBase hU π hk).left
      (U.prescribedZeroOverlap hU π hk).left (congrArg Over.Hom.left (U.prescribedZeroOverlap_baseProjection hU π hk))
  exact (ConcreteCategory.bijective_of_isIso _).surjective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
