import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Triple
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Overlap

/-! # Poincare Triple Geometry -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual triple overlap is reduced; its projection to the dual
triple overlap is proper smooth with connected geometric fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_square :
    IsPullback (pullback.fst _ _) (U.prescribedPoincareTripleDual hU π hk)
      (U.prescribedPoincareOverlapDual π) (pullback.fst _ _) :=
  DescentCocycleMapCartesian.DescentCocycle.mapComposition_cartesian π U.prescribedPoincareProjection U.prescribedDualProjection
    U.prescribedPoincareDual rfl (U.prescribedPoincareTarget π hU hk)
    (U.prescribedDualOverlapTarget hU π hk) (U.prescribedPoincareTarget_dual π hU hk)
    (U.prescribedPoincareOverlapDual_square π)

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTriple_reduced : IsReduced (U.prescribedPoincareTriple hU π hk).left := by
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  have hs : IsPullback src.left (DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection).left
      (U.prescribedPoincareProjection ≫ π).left π.left :=
    (IsPullback.of_hasPullback _ _).map (Over.forget _)
  have : IsFinite src.left := MorphismProperty.of_isPullback hs.flip (inferInstanceAs (IsFinite π.left))
  have : Etale src.left := MorphismProperty.of_isPullback hs.flip (inferInstanceAs (Etale π.left))
  let k := pullback.fst (U.prescribedPoincareTarget π hU hk) src
  have hc := (IsPullback.of_hasPullback (U.prescribedPoincareTarget π hU hk) src).map (Over.forget _)
  have : IsFinite k.left := MorphismProperty.of_isPullback hc.flip (inferInstanceAs (IsFinite src.left))
  have : Etale k.left := MorphismProperty.of_isPullback hc.flip (inferInstanceAs (Etale src.left))
  exact Finite.EtaleReduced.finite_etale_isReduced k.left

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_smooth : Smooth (U.prescribedPoincareTripleDual hU π hk).left :=
  MorphismProperty.of_isPullback (U.prescribedPoincareTripleDual_square hU π hk |>.map (Over.forget _))
    (inferInstanceAs (Smooth (U.prescribedPoincareOverlapDual π).left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_proper : IsProper (U.prescribedPoincareTripleDual hU π hk).left :=
  MorphismProperty.of_isPullback (U.prescribedPoincareTripleDual_square hU π hk |>.map (Over.forget _))
    (inferInstanceAs (IsProper (U.prescribedPoincareOverlapDual π).left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_connected : GeometricallyConnected (U.prescribedPoincareTripleDual hU π hk).left :=
  MorphismProperty.of_isPullback (U.prescribedPoincareTripleDual_square hU π hk |>.map (Over.forget _))
    (inferInstanceAs (GeometricallyConnected (U.prescribedPoincareOverlapDual π).left))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTriple_globalFunctions (hrigid : U.PrescribedRigid) :
    Function.Surjective (U.prescribedPoincareTripleDual hU π hk).left.appTop := by
  have : IsIso (U.prescribedPoincareTripleDual hU π hk).left.appTop :=
    Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_appTop
      (U.prescribedPoincareTripleDual hU π hk).left (U.prescribedPoincareTripleZero hU π hk hrigid).left
      (congrArg Over.Hom.left (U.prescribedPoincareTripleZero_dual hU π hk hrigid))
  exact (ConcreteCategory.bijective_of_isIso _).surjective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
