import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroGroup
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme

/-! # Relative Difference Group -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric

noncomputable section

/-! The original normalized difference zero scheme is an actual group
scheme. Closure on every test scheme is proved from the genuine
translation stabilizer, with no supplied group-closure assumptions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeDifference_zeroIsSubgroup :
    RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.ZeroIsSubgroup (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) where
  one T := RelativeDifferenceZeroScheme.Geometric.relativeRigidifiedDifference_one A L T
  mul {T} a b ha hb := by
    let K := RelativeTranslationClasses.Geometric.relativeTranslationStabilizer A
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd T A.scheme).left))
    exact (RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L (a * b)).mpr
      (K.mul_mem ((RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L a).mp ha)
        ((RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L b).mp hb))
  inv {T} a ha := by
    let K := RelativeTranslationClasses.Geometric.relativeTranslationStabilizer A
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd T A.scheme).left))
    exact (RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L a⁻¹).mpr
      (K.inv_mem ((RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L a).mp ha))

variable [IsLocallyNoetherian S] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
local instance : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

def relativeDifferenceZeroGroup :
    RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.ZeroGroupData (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P :=
  RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroGroupData (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P
    (relativeDifference_zeroIsSubgroup A L)

theorem relativeDifferenceZeroInclusion_isMonHom :
    letI : GrpObj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) := (relativeDifferenceZeroGroup A L P).group
    IsMonHom (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
  (relativeDifferenceZeroGroup A L P).monHom

theorem relativeDifferenceZeroGroup_commutative :
    letI : GrpObj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) := (relativeDifferenceZeroGroup A L P).group
    IsCommMonObj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) := by
  let : GrpObj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) := (relativeDifferenceZeroGroup A L P).group
  let i := RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let : IsMonHom i := relativeDifferenceZeroInclusion_isMonHom A L P
  let : Mono i := RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  constructor
  apply (cancel_mono i).mp
  rw [Category.assoc, IsMonHom.mul_hom]
  rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric
