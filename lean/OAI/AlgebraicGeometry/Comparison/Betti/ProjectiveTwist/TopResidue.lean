import OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCycles
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing

/-! # Top Residue -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopResidue.Dolbeault

noncomputable section

/-! The full negative Laurent coefficient of an original projective twist cochain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

def projectiveTwistTopResidue (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X n →+
      ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d) where
  toFun z := (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n z Finset.univ).val id
  map_zero' := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d n
    (Finset.univ : Finset (Fin (n + 1))) => s.val id)
      (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n).map_zero Finset.univ)
  map_add' z w := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d n
    (Finset.univ : Finset (Fin (n + 1))) => s.val id)
      (congrFun ((Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n).map_add z w) Finset.univ)

theorem projectiveTwistTopResidue_boundary (q : ℕ) (j : Fin (q + 2)) (d : ℤ)
    (b : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).X q) :
    projectiveTwistTopResidue (q + 1) j d
      (((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
        (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).d q (q + 1) b) = 0 := by
  have h := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential (q + 1) j d q b Finset.univ
  have hzero : Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d q b Finset.univ = 0 :=
    SupportTopCochains.Cech.fullSupportCochain_zero_of_lt q (by simp) _
  have hd : SupportedCochains.Cech.supportedCechDifferential Finset.univ q
      (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d q b Finset.univ) = 0 :=
    (congrArg (SupportedCochains.Cech.supportedCechDifferential Finset.univ q) hzero).trans (map_zero _)
  exact congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d (q + 1)
    (Finset.univ : Finset (Fin (q + 2))) => s.val id) (h.trans hd)

theorem projectiveTwistFullSupportPart_eq_zero_of_residue (q : ℕ) (j : Fin (q + 2)) (d : ℤ)
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).X (q + 1))
    (hz : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).d (q + 1) (q + 2) z = 0)
    (hr : projectiveTwistTopResidue (q + 1) j d z = 0) :
    Projective.CechSupportReduction.Dolbeault.projectiveTwistFullSupportPart (q + 1) j d (q + 1) z = 0 := by
  have hfull : Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d (q + 1) z Finset.univ = 0 :=
    SupportTopCycles.Cech.fullSupportTopCycle_ext (q + 1) _ 0
      (CechVanishing.Dolbeault.projectiveTwistCechSupportCycle (q + 1) j d q z hz Finset.univ) (map_zero _) hr
  have hp : SectorProperSupportContraction.Dolbeault.sectorFullSupportPart d (q + 1)
      (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d (q + 1) z) = 0 := by
    funext J
    by_cases hJ : J = Finset.univ
    · subst J
      exact (ite_eq_left rfl).trans hfull
    · exact ite_eq_right hJ
  exact (congrArg (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d (q + 1)).symm hp).trans
    (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (q + 1) j d (q + 1)).symm.map_zero

theorem projectiveTwistTopCycle_boundary_iff (q : ℕ) (j : Fin (q + 2)) (d : ℤ)
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).X (q + 1))
    (hz : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).d (q + 1) (q + 2) z = 0) :
    (∃ b : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).X q,
      ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
        (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).d q (q + 1) b = z) ↔
      projectiveTwistTopResidue (q + 1) j d z = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact projectiveTwistTopResidue_boundary q j d b
  · intro hr
    obtain ⟨b, hb⟩ := Projective.CechSupportReduction.Dolbeault.projectiveTwistCechCycle_reduce_fullSupport (q + 1) j d q z hz
    have hp := projectiveTwistFullSupportPart_eq_zero_of_residue q j d z hz hr
    exact ⟨b, by simpa only [hp, add_zero] using hb⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopResidue.Dolbeault
