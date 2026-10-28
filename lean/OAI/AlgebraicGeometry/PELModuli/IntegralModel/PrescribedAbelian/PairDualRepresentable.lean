import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairHomogeneousPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalUniversalClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardRepresentationDescent

/-! # Pair Dual Representable -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended dual represents the homogeneous Picard sheaf
of the actual descended abelian scheme, with the descended Poincare
line as its universal class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid) [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareRepresented :
    B.abelian.homogeneousPicardSheaf.obj.IsRepresentedBy
      (PairPoincareClass.pairPoincareClass B.abelian B.dual (B.poincareLine hrigid) (B.poincareLine_homogeneous hrigid)) := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact PairPicardRepresentationDescent.pairPicard_isRepresentedBy B.abelian B.dual ((Over.pullback b).map π).left
    (B.poincareLine hrigid) (B.poincareLine_homogeneous hrigid) (B.localPoincare_homogeneous hrigid)
    B.localDualRepresentable (B.localPoincare_universalClass hrigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualRepresentable : B.abelian.homogeneousPicardSheaf.obj.RepresentableBy B.dual.scheme :=
  (B.poincareRepresented hrigid).representableBy

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualRepresentable_apply {T : Over ((Over.pullback b).obj Q).left} (f : T ⟶ B.dual.scheme) :
    (B.dualRepresentable hrigid).homEquiv f =
      B.abelian.homogeneousPicardSheaf.obj.map f.op
        (PairPoincareClass.pairPoincareClass B.abelian B.dual (B.poincareLine hrigid) (B.poincareLine_homogeneous hrigid)) :=
  (B.poincareRepresented hrigid).representableBy_homEquiv_apply f

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualRepresentable_universalClass :
    (B.dualRepresentable hrigid).homEquiv (𝟙 B.dual.scheme) =
      PairPoincareClass.pairPoincareClass B.abelian B.dual (B.poincareLine hrigid) (B.poincareLine_homogeneous hrigid) := by
  rw [B.dualRepresentable_apply, op_id, Functor.map_id_apply]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
