import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorCochainProduct
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorDifferential

/-! # Sector Support Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.SectorSupportDifferential.Dolbeault

noncomputable section

/-! Original projective twist differentials split into fixed-support additive differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped BigOperators

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] ProjectiveTwist.CechSectorDifferential.Dolbeault.laurentSectionFamily_addCommGroup ProjectiveTwist.CechSectorDifferential.Dolbeault.laurentSectorFamily_addCommGroup
  ProjectiveTwist.CechSectorDifferential.Dolbeault.laurentSectorFamily_addZero

local instance homogeneousSectorCoefficients_addCommGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (d : ℤ) : AddCommGroup ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d) := Submodule.addCommGroup _

local instance supportDifferentialAdd {ι : Type} [DecidableEq ι]
    (V : Type) [AddCommGroup V] (J : Finset ι) (q : ℕ) :
    Add (SupportedCochains.Cech.supportedCechCochains V J q) := by infer_instance

local instance supportDifferentialAddZero {ι : Type} [DecidableEq ι]
    (V : Type) [AddCommGroup V] (J : Finset ι) (q : ℕ) :
    AddZeroClass (SupportedCochains.Cech.supportedCechCochains V J q) := by infer_instance

def projectiveTwistCechSupportCoordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ) :
    ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q ≃+
      (∀ J : Finset (Fin (n + 1)), Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J) :=
  (ProjectiveTwist.CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q).trans (Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorCochainProduct (ι := Fin (n + 1)) d q)

theorem projectiveTwistCechSupportCoordinates_differential (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (J : Finset (Fin (n + 1))) :
    projectiveTwistCechSupportCoordinates n j d (q + 1)
        (((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
          q (q + 1) z) J =
      SupportedCochains.Cech.supportedCechDifferential (V := ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d)) J q
        (projectiveTwistCechSupportCoordinates n j d q z J) := by
  apply Subtype.ext
  funext t
  let L := HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap (Finset.univ.image t) d J
  have h := congrArg L (ProjectiveTwist.CechSectorDifferential.Dolbeault.projectiveTwistCechDifferential_sectors n j d q t z)
  exact h.trans ((map_sum L _ Finset.univ).trans (Finset.sum_congr rfl (fun k _ =>
    (map_zsmul L ((-1 : ℤ) ^ k.val) _).trans
      (congrArg (fun v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d => (-1 : ℤ) ^ k.val • v)
        (HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap_inclusion
          (CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n q (q + 1) t (SimplexCategory.δ k).toOrderHom)
          d J (ProjectiveTwist.CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q z (t ∘ (SimplexCategory.δ k).toOrderHom)))))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.SectorSupportDifferential.Dolbeault
