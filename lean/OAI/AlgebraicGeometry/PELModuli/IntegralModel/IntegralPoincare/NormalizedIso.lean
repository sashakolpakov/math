import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.OverlapFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Overlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ClassInvariance
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness

/-! # Normalized Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct the unique Poincare overlap isomorphism preserving the
actual zero frames. Existence comes from the actual PEL class equation;
uniqueness comes from the proved global-function comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.existsUnique_prescribedPoincareNormalizedIso :
    ∃! e : (U.prescribedPoincareLine.pullback
        (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left).sheaf ≅
      (U.prescribedPoincareLine.pullback (U.prescribedPoincareTarget π hU hk).left).sheaf,
      (Scheme.Modules.pullback (U.prescribedPoincareZeroOverlap π).left).map e.hom ≫
        (U.prescribedPoincareTargetFrame π hU hk hrigid).hom = (U.prescribedPoincareSourceFrame π).hom := by
  let LS := U.prescribedPoincareLine.pullback (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
  let LT := U.prescribedPoincareLine.pullback (U.prescribedPoincareTarget π hU hk).left
  let d := (U.prescribedPoincareOverlapDual π).left
  let z := (U.prescribedPoincareZeroOverlap π).left
  have hz : z ≫ d = 𝟙 _ := congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_dual π)
  have : IsIso d.appTop := Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_appTop d z hz
  have hΓ : Function.Surjective d.appTop := (ConcreteCategory.bijective_of_isIso d.appTop).surjective
  have hLS : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle LS.sheaf := LS.locallyTrivial
  obtain ⟨e⟩ : Nonempty (LS.sheaf ≅ LT.sheaf) :=
    Quotient.exact (U.prescribedPoincare_class_invariant hU π hk hrigid).symm
  exact Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.existsUnique_normalizedIso d z hz hΓ hLS
    (U.prescribedPoincareSourceFrame π) (U.prescribedPoincareTargetFrame π hU hk hrigid) e

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso :
    (U.prescribedPoincareLine.pullback (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left).sheaf ≅
      (U.prescribedPoincareLine.pullback (U.prescribedPoincareTarget π hU hk).left).sheaf :=
  Classical.choose (U.existsUnique_prescribedPoincareNormalizedIso hU π hk hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_normalized :
    (Scheme.Modules.pullback (U.prescribedPoincareZeroOverlap π).left).map
        (U.prescribedPoincareNormalizedIso hU π hk hrigid).hom ≫
      (U.prescribedPoincareTargetFrame π hU hk hrigid).hom = (U.prescribedPoincareSourceFrame π).hom :=
  (Classical.choose_spec (U.existsUnique_prescribedPoincareNormalizedIso hU π hk hrigid)).1

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_unique
    (e : (U.prescribedPoincareLine.pullback
        (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left).sheaf ≅
      (U.prescribedPoincareLine.pullback (U.prescribedPoincareTarget π hU hk).left).sheaf)
    (he : (Scheme.Modules.pullback (U.prescribedPoincareZeroOverlap π).left).map e.hom ≫
      (U.prescribedPoincareTargetFrame π hU hk hrigid).hom = (U.prescribedPoincareSourceFrame π).hom) :
    e = U.prescribedPoincareNormalizedIso hU π hk hrigid :=
  (Classical.choose_spec (U.existsUnique_prescribedPoincareNormalizedIso hU π hk hrigid)).2 e he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
