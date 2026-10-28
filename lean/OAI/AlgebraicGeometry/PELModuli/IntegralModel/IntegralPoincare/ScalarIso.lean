import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ClassInvariance
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line

/-! # Scalar Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The scalar-changed Poincare line has an actual isomorphism between
its two restrictions to the literal prescribed product relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareLine {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback b).obj U.prescribedPoincareSpace).left :=
  U.prescribedPoincareLine.pullback (pullback.fst U.prescribedPoincareSpace.hom b)

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincare_class_invariant (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((U.scalarPoincareLine b).pullback
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((U.scalarPoincareLine b).pullback
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left) :=
  Scalar.Line.lineBundle_scalar_relation_class b (U.prescribedPoincareTarget π hU hk)
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection) U.prescribedPoincareLine
    (U.prescribedPoincare_class_invariant hU π hk hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincare_overlap_iso (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) :
    Nonempty (((U.scalarPoincareLine b).pullback
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left).sheaf ≅
      ((U.scalarPoincareLine b).pullback
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left).sheaf) :=
  Quotient.exact (U.scalarPoincare_class_invariant hU π hk hrigid b).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
