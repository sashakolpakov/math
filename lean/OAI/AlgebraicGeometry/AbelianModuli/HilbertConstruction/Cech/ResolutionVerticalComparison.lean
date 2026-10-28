import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalComparison

/-! # Resolution Vertical Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionVerticalComparison.IntrinsicCech

noncomputable section

/-! Acyclic intersections give the actual Čech-to-total homology comparison in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

theorem cechInjectiveResolution_columnsExact
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hH : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) :
    TotalComplex.CycleNormalization.RowsExact (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).flip := by
  intro p q
  exact (HomologicalComplex.exactAt_iff'
    ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).flip.X p)
      q (q + 1) (q + 2) (by simp) (by simp)).1
    (AcyclicIntersectionColumns.IntrinsicCech.cechInjectiveResolution_columns_exactAt_succ U F hH p q)

theorem cechInjectiveResolutionVerticalEdge_quasiIsoAt_succ
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hH : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (n : ℕ) :
    QuasiIsoAt (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U F) (n + 1) := by
  apply TotalComplex.VerticalComparison.vertical_edge_quasiIsoAt
  · exact InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation_exact U F
  · intro p
    exact InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation_f_mono U F p
  · exact cechInjectiveResolution_columnsExact U F hH

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionVerticalComparison.IntrinsicCech
