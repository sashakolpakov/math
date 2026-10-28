import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairHomogeneousDescent

/-! # Pair Homogeneous Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended Poincare line is homogeneous on the arithmetic
quotient. Its homogeneity is proved through the prescribed fppf cover. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLine_homogeneous :
    B.abelian.IsHomogeneousPicardClass B.dual.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B.poincareLine hrigid)) := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact PairHomogeneousDescent.pairLine_homogeneous_of_baseChange B.abelian B.dual ((Over.pullback b).map π).left
    (B.poincareLine hrigid) (B.localPoincare_homogeneous hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
