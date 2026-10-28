import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OrbitEffectiveDescent

/-! # Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed dual-family overlap is a normalized internal
equivalence relation over the same arithmetic parameter quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualFamilyRelation (hrigid : U.PrescribedRigid) :
    CategoryTheory.EquivalenceRelation (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left
      (U.prescribedDualOverlapTarget hU π hk).left :=
  AbelianModuli.ReferenceFamily.RepresentedRelations.over_equivalenceRelation_left
    (DescentCocycleChange.DescentCocycle.equivalenceRelation π U.prescribedDualProjection (U.prescribedDualOverlapTarget hU π hk)
      (U.prescribedDualOverlapTarget_base hU π hk) (U.prescribedDualOverlapTarget_normalized hU π hk hrigid)
      (U.prescribedDualOverlapTarget_cocycle hU π hk hrigid))

omit [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualFamily_source_square :
    IsPullback (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection).left
      (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left π.left
      (U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom ≫ π.left) :=
  ((IsPullback.of_hasPullback (U.prescribedDualProjection ≫ π) π).map (Over.forget _)).flip

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
