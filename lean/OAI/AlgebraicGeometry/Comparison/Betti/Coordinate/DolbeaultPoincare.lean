import OAI.AlgebraicGeometry.Comparison.Betti.HigherPolydiscIteration
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

/-! # Dolbeault Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.DolbeaultPoincare

noncomputable section

/-! Local higher-degree Dolbeault exactness with the correct primitive
bidegree on arbitrary finite-coordinate open domains. -/

open _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coordinateDolbeaultPoincare_higher (O : Opens (ι → ℂ))
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm O (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : O) :
    ∃ W : Opens (ι → ℂ), x.val ∈ W ∧ ∃ hW : W ≤ O,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W (n + 1), DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hW a := by
  obtain ⟨U, hxU, hUO⟩ := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.exists_coordinatePolydisc_neighborhood O x
  let ar := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hUO a
  have har : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) ar = 0 := by
    change DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hUO a) = 0
    rw [← DivisorClass.Chern.DolbeaultZeroKernelMap.openDolbeaultD_restrict hUO a, ha, map_zero]
  have harp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) ar := DivisorClass.Chern.Open.DolbeaultPrime.openFormHasBidegree_restrict hUO hpure
  obtain ⟨V, hVU, hxV, t, htp, ht⟩ :=
    HigherPolydiscIteration.Dolbeault.exists_polydisc_higherForm_dolbeault_primitive U n p q hn ar har harp ⟨x, hxU⟩
  refine ⟨DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V, hxV, (HigherPolydiscIteration.Dolbeault.coordinatePolydisc_mono U V hVU).trans hUO, t, htp, ?_⟩
  exact ht.trans (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans hUO (HigherPolydiscIteration.Dolbeault.coordinatePolydisc_mono U V hVU) a)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.DolbeaultPoincare
