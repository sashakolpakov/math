import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OrbitEffectiveDescent

/-! # Scheme Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed universal family's descent relation and its
effective scheme descent once its affine orbit neighborhoods are supplied.
The relation, quotient, and Cartesian recovery are all constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedFamilyRelation (hrigid : U.PrescribedRigid) :
    CategoryTheory.EquivalenceRelation (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
      (U.prescribedOverlapTarget hU π hk).left :=
  AbelianModuli.ReferenceFamily.RepresentedRelations.over_equivalenceRelation_left
    (DescentCocycleChange.DescentCocycle.equivalenceRelation π U.prescribedProjection (U.prescribedOverlapTarget hU π hk)
      (U.prescribedOverlapTarget_base hU π hk) (U.prescribedOverlapTarget_normalized hU π hk hrigid)
      (U.prescribedOverlapTarget_cocycle hU π hk hrigid))

omit [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedFamily_source_square :
    IsPullback (DescentCocycleChange.DescentCocycle.base π U.prescribedProjection).left
      (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left π.left
      (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ π.left) :=
  ((IsPullback.of_hasPullback (U.prescribedProjection ≫ π) π).map (Over.forget _)).flip

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_family_scheme_descends [Surjective π.left]
    (hrigid : U.PrescribedRigid)
    (hOrbit : ∀ x : U.prescribedTotalSpace.left, ∃ V : U.prescribedTotalSpace.left.Opens,
      IsAffineOpen V ∧ ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related
        (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
        (U.prescribedOverlapTarget hU π hk).left x y → y ∈ V) :
    ∃ (A : Over Q.left) (q : U.prescribedTotalSpace.left ⟶ A.left),
      IsPullback U.forgetAuxiliary.data.polarized.abelian.scheme.hom q π.left A.hom ∧
      Smooth A.hom ∧ IsProper A.hom ∧ GeometricallyConnected A.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
        (U.prescribedOverlapTarget hU π hk).left :=
  Affine.OrbitEffectiveDescent.effective_smooth_proper_descent_from_affine_orbits π.left
    U.forgetAuxiliary.data.polarized.abelian.scheme.hom
    (DescentCocycleChange.DescentCocycle.base π U.prescribedProjection).left
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
    (U.prescribedOverlapTarget hU π hk).left (U.prescribedFamily_source_square π)
    (congrArg Over.Hom.left (U.prescribedOverlapTarget_base hU π hk))
    (U.prescribedFamilyRelation hU π hk hrigid) hOrbit

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
