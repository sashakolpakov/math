import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Space
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.ZeroRelation

/-! # Dual Zero -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The second zero section of the actual universal Poincare product
and its given line-bundle trivialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero : U.prescribedTotalSpace ⟶ U.prescribedPoincareSpace :=
  (Over.map X.hom).map (lift (1 : U.forgetAuxiliary.data.polarized.abelian.scheme ⟶
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme) (𝟙 U.forgetAuxiliary.data.polarized.abelian.scheme))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero_abelian : U.prescribedPoincareDualZero ≫ U.prescribedPoincareAbelian =
    𝟙 U.prescribedTotalSpace := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareAbelian
  rw [← (Over.map X.hom).map_comp, lift_snd, (Over.map X.hom).map_id]
  rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero_dual : U.prescribedPoincareDualZero ≫ U.prescribedPoincareDual =
    U.prescribedProjection ≫ U.prescribedDualZero := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDual
  rw [← (Over.map X.hom).map_comp, lift_fst]
  apply Over.OverMorphism.ext
  rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZero_projection :
    U.prescribedPoincareDualZero ≫ U.prescribedPoincareProjection = U.prescribedProjection := by
  rw [← U.prescribedPoincareAbelian_projection, ← Category.assoc,
    U.prescribedPoincareDualZero_abelian, Category.id_comp]

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualFrame :
    (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.prescribedTotalSpace.left :=
  Classical.choice U.forgetAuxiliary.data.polarized.dual.normalizedAtDualZero

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
