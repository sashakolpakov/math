import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Pair Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual relative square of the universal abelian family, with
its two projections and multiplication. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairSpace : Over (Spec (.of R)) :=
  (Over.map X.hom).obj (U.forgetAuxiliary.data.polarized.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.abelian.scheme)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairFst : U.prescribedPairSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map (fst _ _)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairSnd : U.prescribedPairSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map (snd _ _)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairProjection : U.prescribedPairSpace ⟶ X :=
  U.prescribedPairFst ≫ U.prescribedProjection

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedMul : U.prescribedPairSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map (MonObj.mul : U.forgetAuxiliary.data.polarized.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairSnd_projection :
    U.prescribedPairSnd ≫ U.prescribedProjection = U.prescribedPairProjection :=
  Over.OverMorphism.ext pullback.condition.symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedMul_projection : U.prescribedMul ≫ U.prescribedProjection = U.prescribedPairProjection :=
  Over.OverMorphism.ext (MonObj.mul : U.forgetAuxiliary.data.polarized.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme).w

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPair_square : IsPullback U.prescribedPairFst U.prescribedPairSnd
    U.prescribedProjection U.prescribedProjection := by
  apply IsPullback.of_map (F := Over.forget (Spec (.of R)))
  · exact Over.OverMorphism.ext pullback.condition
  · exact IsPullback.of_hasPullback _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairSpace_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced U.prescribedPairSpace.left := by
  have : Smooth U.prescribedPairFst.left := MorphismProperty.of_isPullback
    ((U.prescribedPair_square).map (Over.forget _)).flip
    (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  have : Smooth U.prescribedPairProjection.left :=
    inferInstanceAs (Smooth (U.prescribedPairFst.left ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  exact AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource U.prescribedPairProjection.left

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
