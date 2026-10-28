import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace
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

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairSpace : Over (Spec (.of R)) :=
  (Over.map X.hom).obj (U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairFst : U.prescribedDualPairSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map (fst _ _)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairSnd : U.prescribedDualPairSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map (snd _ _)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairProjection : U.prescribedDualPairSpace ⟶ X :=
  U.prescribedDualPairFst ≫ U.prescribedDualProjection

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualMul : U.prescribedDualPairSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map (MonObj.mul : U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairSnd_projection :
    U.prescribedDualPairSnd ≫ U.prescribedDualProjection = U.prescribedDualPairProjection :=
  Over.OverMorphism.ext pullback.condition.symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualMul_projection : U.prescribedDualMul ≫ U.prescribedDualProjection = U.prescribedDualPairProjection :=
  Over.OverMorphism.ext (MonObj.mul : U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme).w

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPair_square : IsPullback U.prescribedDualPairFst U.prescribedDualPairSnd
    U.prescribedDualProjection U.prescribedDualProjection := by
  apply IsPullback.of_map (F := Over.forget (Spec (.of R)))
  · exact Over.OverMorphism.ext pullback.condition
  · exact IsPullback.of_hasPullback _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairSpace_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced U.prescribedDualPairSpace.left := by
  have : Smooth U.prescribedDualPairFst.left := MorphismProperty.of_isPullback
    ((U.prescribedDualPair_square).map (Over.forget _)).flip
    (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have : Smooth U.prescribedDualPairProjection.left :=
    inferInstanceAs (Smooth (U.prescribedDualPairFst.left ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  exact AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource U.prescribedDualPairProjection.left

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
