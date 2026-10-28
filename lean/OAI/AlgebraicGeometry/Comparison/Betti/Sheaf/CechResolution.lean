import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.StalkQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero

/-! # Cech Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechResolution

noncomputable section

/-! The actual total Čech resolution of a nonnegative sheaf complex is a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

include hU

theorem sheafCechResolutionEdge_quasiIso : QuasiIso (CechAugmentation.sheafCechResolutionEdge U K) := by
  constructor
  intro n
  cases n with
  | zero =>
    exact TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero (CechAugmentation.sheafCechBicomplex U K) K
      (CechAugmentation.sheafCechComplexAugmentation U K)
      (fun q q' _ => CechAugmentation.sheafCechComplexAugmentation_comm U K q q')
      (CechAugmentation.sheafCechComplexAugmentation_comp_d U K)
      (CechExactRows.sheafCechComplexAugmentation_exact U hU K 0)
      (CechExactRows.sheafCechComplexAugmentation_mono U hU K)
  | succ n =>
    exact (StalkQuasiIso.Cech.sheafQuasiIsoAt_iff_stalk (CechAugmentation.sheafCechResolutionEdge U K) (n + 1)).mpr
      (fun x => CechStalk.sheafCechResolutionEdge_stalk_quasiIsoAt_succ U hU K x n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechResolution
