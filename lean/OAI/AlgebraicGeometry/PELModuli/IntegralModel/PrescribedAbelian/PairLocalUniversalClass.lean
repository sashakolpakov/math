import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClass

/-! # Pair Local Universal Class -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The recovered local line supplies exactly the universal element
of the actual local dual representation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincare_universalClass :
    B.localDualRepresentable.homEquiv (𝟙 (B.dual.pullback ((Over.pullback b).map π).left).scheme) =
      PairPoincareClass.pairPoincareClass (B.abelian.pullback ((Over.pullback b).map π).left)
        (B.dual.pullback ((Over.pullback b).map π).left) (B.localPoincareLine hrigid)
        (B.localPoincare_homogeneous hrigid) := by
  have hq : (⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.localDualData.poincare, B.localDualData.poincareHomogeneous⟩ :
      (B.abelian.pullback ((Over.pullback b).map π).left).homogeneousPicardPresheaf.obj
        (.op (B.dual.pullback ((Over.pullback b).map π).left).scheme)) =
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B.localPoincareLine hrigid), B.localPoincare_homogeneous hrigid⟩ :=
    Subtype.ext (Quotient.sound ⟨(B.localPoincareIso hrigid).symm⟩)
  exact B.localDualData.universalClass.trans
    (congrArg ((toSheafify (Scheme.fppfTopology.over ((Over.pullback b).obj X).left)
      (B.abelian.pullback ((Over.pullback b).map π).left).homogeneousPicardPresheaf).app
        (.op (B.dual.pullback ((Over.pullback b).map π).left).scheme)) hq)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
