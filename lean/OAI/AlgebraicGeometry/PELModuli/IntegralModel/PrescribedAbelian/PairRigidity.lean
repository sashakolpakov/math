import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizedComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedRigidityDescent

/-! # Pair Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original prescribed rigidity holds for the actual descended
polarized family on every reduced scheme mapping to its parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedRigid_on_schemes (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hrigid : U.PrescribedRigid) (T : Scheme.{0}) [IsReduced T] (f : T ⟶ X.left)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.forgetAuxiliary.data.polarized.pullback f)
      (U.forgetAuxiliary.data.polarized.pullback f)) :
    e.abelian.hom = 𝟙 (U.forgetAuxiliary.data.polarized.abelian.pullback f).scheme := by
  let V : Over (Spec (.of R)) := Over.mk (f ≫ X.hom)
  have : IsReduced V.left := inferInstanceAs (IsReduced T)
  exact hrigid V (Over.homMk f rfl) e

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)
    [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizedRigidity (T : Scheme.{0}) [IsReduced T]
    (f : T ⟶ ((Over.pullback b).obj Q).left)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((B.polarizedData hrigid).pullback f)
      ((B.polarizedData hrigid).pullback f)) :
    e.abelian.hom = 𝟙 (B.abelian.pullback f).scheme := by
  have : IsFinite ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (IsFinite π.left))
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact Reduced.PolarizedRigidityDescent.reduced_polarized_rigidity_of_cover (B.polarizedData hrigid) ((Over.pullback b).map π).left
    (U.forgetAuxiliary.data.polarized.pullback (pullback.fst X.hom b)) (B.polarizedComparison hrigid)
    (Reduced.PolarizedRigidityDescent.reduced_polarized_rigidity_pullback U.forgetAuxiliary.data.polarized
      (U.prescribedRigid_on_schemes hrigid) (pullback.fst X.hom b)) T f e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
