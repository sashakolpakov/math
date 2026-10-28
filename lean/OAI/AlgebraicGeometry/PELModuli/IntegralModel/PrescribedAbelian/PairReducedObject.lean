import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairObject
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ObjectAfterBaseChange

/-! # Pair Reduced Object -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The constructed family supplies an actual integral PEL object on
the reduced arithmetic parameter, even when scalar change of the parent
parameter has nilpotents. All family data are its genuine pullbacks. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem PrescribedAbelian.PairReducedObject.reduction_isNoetherian {S : Scheme.{0}} (X : Over S) [IsNoetherian X.left] :
    IsNoetherian (Reduction.reduction X).left := by
  have : IsLocallyNoetherian (Reduction.reduction X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Reduction.reductionι X).left
  have : CompactSpace (Reduction.reduction X).left :=
    QuasiCompact.compactSpace_of_compactSpace (Reduction.reductionι X).left
  exact ⟨⟩

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left}

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.pelObjectAfterPullback {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)
    [IsLocallyNoetherian ((Over.pullback b).obj Q).left]
    {Y : Over S} (f : Y ⟶ (Over.pullback b).obj Q) [IsReduced Y.left] [IsNoetherian Y.left] :
    PEL.Has.IntegralPELObject P R iotaO N ((Over.map b).obj Y) := by
  have : IsReduced ((Over.map b).obj Y).left := inferInstanceAs (IsReduced Y.left)
  have : IsNoetherian ((Over.map b).obj Y).left := inferInstanceAs (IsNoetherian Y.left)
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact ObjectAfterBaseChange.integralPELObjectAfterBaseChange (X := (Over.map b).obj ((Over.pullback b).obj Q))
    (B.polarizedActionData hrigid) ((Over.pullback b).map π).left
    (B.rosati_local hrigid) (B.lieRanks hrigid) ((Over.map b).map f)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.reducedPELObjectOverOriginalBase {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)
    [IsNoetherian ((Over.pullback b).obj Q).left] :
    PEL.Has.IntegralPELObject P R iotaO N ((Over.map b).obj (Reduction.reduction ((Over.pullback b).obj Q))) := by
  have := PrescribedAbelian.PairReducedObject.reduction_isNoetherian ((Over.pullback b).obj Q)
  exact B.pelObjectAfterPullback hrigid (Reduction.reductionι ((Over.pullback b).obj Q))

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.reducedPELObject {R' : Type} [CommRing R'] (φ : R →+* R')
    (B : U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ)))
    (hrigid : U.PrescribedRigid)
    [IsNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left] :
    PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N
      (Reduction.reduction ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q)) :=
  (B.reducedPELObjectOverOriginalBase hrigid).changeCoefficients φ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
