import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorMaps
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechDifferential

/-! # Cech Sector Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorDifferential.Dolbeault

noncomputable section

/-! The original projective twist Cech differential is the alternating sector-inclusion sum. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped BigOperators

local instance laurentSectionFamily_addCommGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) : AddCommGroup ↥(Laurent.SectorSum.Dolbeault.laurentSectorSectionFamilies s) := Submodule.addCommGroup _

local instance laurentSectorFamily_addCommGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (d : ℤ) : AddCommGroup ↥(HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d) := Submodule.addCommGroup _

local instance laurentSectorFamily_addZero {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (d : ℤ) : AddZero ↥(HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d) :=
  (laurentSectorFamily_addCommGroup s d).toAddZero

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistCechSectorEval (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q →+
      ↥(HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d) where
  toFun z := CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q z t
  map_zero' := by
    exact congrFun (map_zero (CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q)) t
  map_add' z w := by
    exact congrFun ((CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q).map_add z w) t

theorem projectiveTwistCechDifferential_sectors (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 2) → Fin (n + 1))
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q) :
    CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d (q + 1)
        (((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
          q (q + 1) z) t =
      ∑ k : Fin (q + 2), ((-1 : ℤ) ^ k.val •
        HomogeneousSectorSingle.Dolbeault.laurentHomogeneousFamilyInclusion
          (Projective.CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n q (q + 1) t (SimplexCategory.δ k).toOrderHom) d
          (CechSectorMaps.Dolbeault.projectiveTwistCechSectors n j d q z (t ∘ (SimplexCategory.δ k).toOrderHom)) :
            HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d) := by
  have h := AdditiveCechDifferential.additiveCechDifferential_eval (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
    (Projective.Intersections.Dolbeault.projectiveStandardCover n) (A := ↥(HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d))
    q (projectiveTwistCechSectorEval n j d (q + 1) t) z
  exact h.trans (Finset.sum_congr rfl (fun k _ => congrArg
    (fun A : HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d => (-1 : ℤ) ^ k.val • A)
    (CechSectorMaps.Dolbeault.projectiveTwistCechSectors_map n j d (SimplexCategory.δ k) t z)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorDifferential.Dolbeault
