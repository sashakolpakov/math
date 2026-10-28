import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopResidue

/-! # Top Representatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopRepresentatives.Dolbeault

noncomputable section

/-! Every homogeneous full-negative coefficient has an original projective twist cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

def projectiveTwistTopRepresentative (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X n :=
  (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n).symm
    (Pi.single Finset.univ (SupportTopCycles.Cech.fullSupportTopCycleMap n v).val)

theorem projectiveTwistTopRepresentative_coordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d) :
    Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n (projectiveTwistTopRepresentative n j d v) =
      Pi.single Finset.univ (SupportTopCycles.Cech.fullSupportTopCycleMap n v).val :=
  (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d n).apply_symm_apply _

theorem projectiveTwistTopRepresentative_cycle (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d n (n + 1)
        (projectiveTwistTopRepresentative n j d v) = 0 := by
  apply (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (n + 1)).injective
  funext J
  have hd := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d n
    (projectiveTwistTopRepresentative n j d v) J
  have hc := congrFun (projectiveTwistTopRepresentative_coordinates n j d v) J
  let T : ∀ J : Finset (Fin (n + 1)), Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d n J :=
    Pi.single Finset.univ (SupportTopCycles.Cech.fullSupportTopCycleMap n v).val
  have hzero : SupportedCochains.Cech.supportedCechDifferential J n (T J) = 0 := by
    by_cases hJ : J = Finset.univ
    · subst J
      simpa only [T, Pi.single_eq_same, AddMonoidHom.mem_ker] using (SupportTopCycles.Cech.fullSupportTopCycleMap n v).property
    · simp only [T, Pi.single_eq_of_ne hJ, map_zero]
  exact hd.trans ((congrArg (SupportedCochains.Cech.supportedCechDifferential J n) hc).trans
    (hzero.trans (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (n + 1)).map_zero J).symm))

theorem projectiveTwistTopRepresentative_residue (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d) :
    TopResidue.Dolbeault.projectiveTwistTopResidue n j d (projectiveTwistTopRepresentative n j d v) = v := by
  have h := congrFun (projectiveTwistTopRepresentative_coordinates n j d v) Finset.univ
  have he := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d n
    (Finset.univ : Finset (Fin (n + 1))) => s.val id) h
  exact he.trans ((congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d n
    (Finset.univ : Finset (Fin (n + 1))) => s.val id) (Pi.single_eq_same _ _)).trans
      ((SupportTopCochains.Cech.fullSupportTopSorting_id n _).trans (SupportTopCycles.Cech.fullSupportTopSeed_id n v)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopRepresentatives.Dolbeault
