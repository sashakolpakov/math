import OAI.AlgebraicGeometry.Comparison.Betti.Projective.SectorSupportDifferential
import OAI.AlgebraicGeometry.Comparison.Betti.SectorProperSupportContraction

/-! # Cech Support Reduction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSupportReduction.Dolbeault

noncomputable section

/-! Every positive original projective twist cocycle reduces to its full negative support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

def projectiveTwistFullSupportPart (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q) :
    ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q :=
  (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).symm
    (SectorProperSupportContraction.Dolbeault.sectorFullSupportPart d q (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q z))

theorem projectiveTwistCechCycle_reduce_fullSupport (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X (q + 1))
    (hz : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
      (q + 1) (q + 2) z = 0) :
    ∃ b : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q,
      ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
        q (q + 1) b + projectiveTwistFullSupportPart n j d (q + 1) z = z := by
  let Z := SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1) z
  let B := SectorProperSupportContraction.Dolbeault.sectorProperSupportPrimitive d q Z
  let b := (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).symm B
  have hcycle (J : Finset (Fin (n + 1))) : SupportedCochains.Cech.supportedCechDifferential J (q + 1) (Z J) = 0 := by
    have hd := SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d (q + 1) z J
    have he := congrArg (fun a : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj
        (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X (q + 2) =>
      SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 2) a J) hz
    exact hd.symm.trans (he.trans (congrFun (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 2)).map_zero J))
  have hprimitive := SectorProperSupportContraction.Dolbeault.sectorProperSupportPrimitive_cycle d q Z hcycle
  refine ⟨b, ?_⟩
  apply (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1)).injective
  funext J
  have hb := congrFun ((SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).apply_symm_apply B) J
  have hp := congrFun ((SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1)).apply_symm_apply
    (SectorProperSupportContraction.Dolbeault.sectorFullSupportPart d (q + 1) Z)) J
  have hd := (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d q b J).trans
    (congrArg (SupportedCochains.Cech.supportedCechDifferential J q) hb)
  have ha := congrFun ((SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1)).map_add
    (((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d q (q + 1) b)
    (projectiveTwistFullSupportPart n j d (q + 1) z)) J
  exact ha.trans ((congrArg₂ (· + ·) hd hp).trans (hprimitive J))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSupportReduction.Dolbeault
