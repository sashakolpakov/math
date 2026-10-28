import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual universal dual-by-abelian product, its Poincare line,
and the given normalization along the abelian zero section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareSpace : Over (Spec (.of R)) :=
  (Over.map X.hom).obj (U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⊗
    U.forgetAuxiliary.data.polarized.abelian.scheme)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual : U.prescribedPoincareSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map (fst _ _)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareAbelian : U.prescribedPoincareSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map (snd _ _)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareProjection : U.prescribedPoincareSpace ⟶ X :=
  U.prescribedPoincareDual ≫ U.prescribedDualProjection

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareAbelian_projection :
    U.prescribedPoincareAbelian ≫ U.prescribedProjection = U.prescribedPoincareProjection :=
  Over.OverMorphism.ext pullback.condition.symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincare_square : IsPullback U.prescribedPoincareDual U.prescribedPoincareAbelian
    U.prescribedDualProjection U.prescribedProjection := by
  apply IsPullback.of_map (F := Over.forget (Spec (.of R)))
  · exact Over.OverMorphism.ext pullback.condition
  · exact IsPullback.of_hasPullback _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareSpace_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced U.prescribedPoincareSpace.left := by
  have : Smooth U.prescribedPoincareDual.left := MorphismProperty.of_isPullback
    (U.prescribedPoincare_square.map (Over.forget _)).flip
    (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom))
  have : Smooth U.prescribedPoincareProjection.left :=
    inferInstanceAs (Smooth (U.prescribedPoincareDual.left ≫
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  exact AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource U.prescribedPoincareProjection.left

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero : U.prescribedDualTotalSpace ⟶ U.prescribedPoincareSpace :=
  (Over.map X.hom).map (lift (𝟙 U.forgetAuxiliary.data.polarized.dual.abelian.scheme)
    (1 : U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⟶
      U.forgetAuxiliary.data.polarized.abelian.scheme))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero_dual : U.prescribedPoincareZero ≫ U.prescribedPoincareDual =
    𝟙 U.prescribedDualTotalSpace := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual
  rw [← (Over.map X.hom).map_comp, lift_fst, (Over.map X.hom).map_id]
  rfl

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle U.prescribedPoincareSpace.left :=
  U.forgetAuxiliary.data.polarized.dual.poincare

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareFrame :
    (U.prescribedPoincareLine.pullback U.prescribedPoincareZero.left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.prescribedDualTotalSpace.left :=
  Classical.choice U.forgetAuxiliary.data.polarized.dual.normalizedAtAbelianZero

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
