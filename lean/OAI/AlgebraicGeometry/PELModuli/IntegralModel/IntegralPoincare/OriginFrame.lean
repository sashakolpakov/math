import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualZero
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

/-! # Origin Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Adjust the second Poincare frame by its actual scalar discrepancy
so that the two zero-section frames agree at the common origin. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincare_commonZero : U.prescribedZero ≫ U.prescribedPoincareDualZero =
    U.prescribedDualZero ≫ U.prescribedPoincareZero := by
  apply U.prescribedPoincare_square.hom_ext
  · rw [Category.assoc, U.prescribedPoincareDualZero_dual, ← Category.assoc,
      U.prescribedZero_projection, Category.id_comp, Category.assoc,
      U.prescribedPoincareZero_dual, Category.comp_id]
  · rw [Category.assoc, U.prescribedPoincareDualZero_abelian, Category.comp_id,
      Category.assoc, U.prescribedPoincareZero_abelian, ← Category.assoc,
      U.prescribedDualZero_projection, Category.id_comp]

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualOriginFrame :
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback U.prescribedZero.left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left :=
  LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
    U.prescribedPoincareDualZero.left U.prescribedZero.left U.prescribedDualZero.left
    (congrArg Over.Hom.left U.prescribedPoincare_commonZero)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareCompatibleDualFrame :
    (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.prescribedTotalSpace.left :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso U.prescribedProjection.left U.prescribedZero.left
    U.prescribedPoincareDualFrame U.prescribedPoincareDualOriginFrame (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.prescribedZero.left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareCompatibleDualFrame_origin :
    (Scheme.Modules.pullback U.prescribedZero.left).map U.prescribedPoincareCompatibleDualFrame.hom ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.prescribedZero.left).hom = U.prescribedPoincareDualOriginFrame.hom :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section U.prescribedProjection.left U.prescribedZero.left
    (congrArg Over.Hom.left U.prescribedZero_projection) U.prescribedPoincareDualFrame
    U.prescribedPoincareDualOriginFrame (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.prescribedZero.left)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
