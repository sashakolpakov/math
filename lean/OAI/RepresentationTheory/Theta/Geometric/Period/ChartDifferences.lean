import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold

/-! # Chart Differences -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Local period lifts differ by continuous lattice-valued functions. -/

open _root_.Topology
open scoped Classical

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

theorem Torus.Data.CM.ProjectivePeriodData.periodChart_difference_mem (i j z : Φ.periodTorus)
    (hi : z ∈ (Φ.periodChart i).source) (hj : z ∈ (Φ.periodChart j).source) :
    Φ.periodChart j z - Φ.periodChart i z ∈ Φ.periodIntegerLattice := by
  change Φ.periodChart j z - Φ.periodChart i z ∈ Φ.periodIntegerLattice.toAddSubgroup
  apply (QuotientAddGroup.eq_zero_iff _).mp
  rw [QuotientAddGroup.mk_sub]
  have hei : (QuotientAddGroup.mk (Φ.periodChart i z) : Φ.periodTorus) = z := by
    rw [← Φ.periodChart_symm i]
    exact (Φ.periodChart i).left_inv hi
  have hej : (QuotientAddGroup.mk (Φ.periodChart j z) : Φ.periodTorus) = z := by
    rw [← Φ.periodChart_symm j]
    exact (Φ.periodChart j).left_inv hj
  rw [hei, hej, sub_self]

def Torus.Data.CM.ProjectivePeriodData.periodChartDifference (i j z : Φ.periodTorus) : Φ.periodIntegerLattice :=
  if h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source then
    ⟨Φ.periodChart j z - Φ.periodChart i z, Φ.periodChart_difference_mem i j z h.1 h.2⟩
  else 0

theorem Torus.Data.CM.ProjectivePeriodData.periodChartDifference_val (i j z : Φ.periodTorus)
    (h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source) :
    (Φ.periodChartDifference i j z).val = Φ.periodChart j z - Φ.periodChart i z := by
  simp only [Torus.Data.CM.ProjectivePeriodData.periodChartDifference, dite_eq_left h]

theorem Torus.Data.CM.ProjectivePeriodData.periodChartDifference_self (i z : Φ.periodTorus) : Φ.periodChartDifference i i z = 0 := by
  by_cases h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart i).source
  · apply Subtype.ext
    rw [Φ.periodChartDifference_val i i z h, sub_self]
    rfl
  · simp only [Torus.Data.CM.ProjectivePeriodData.periodChartDifference, dite_eq_right h]

theorem Torus.Data.CM.ProjectivePeriodData.periodChartDifference_add (i j k z : Φ.periodTorus)
    (h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source ∩ (Φ.periodChart k).source) :
    Φ.periodChartDifference j k z + Φ.periodChartDifference i j z = Φ.periodChartDifference i k z := by
  apply Subtype.ext
  change (Φ.periodChartDifference j k z).val + (Φ.periodChartDifference i j z).val = _
  rw [Φ.periodChartDifference_val j k z ⟨h.1.2, h.2⟩,
    Φ.periodChartDifference_val i j z h.1, Φ.periodChartDifference_val i k z ⟨h.1.1, h.2⟩]
  abel

theorem Torus.Data.CM.ProjectivePeriodData.periodChartDifference_continuousOn (i j : Φ.periodTorus) :
    ContinuousOn (Φ.periodChartDifference i j) ((Φ.periodChart i).source ∩ (Φ.periodChart j).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  have hi : ContinuousOn (Φ.periodChart i) ((Φ.periodChart i).source ∩ (Φ.periodChart j).source) :=
    (Φ.periodChart i).continuousOn.mono Set.inter_subset_left
  have hj : ContinuousOn (Φ.periodChart j) ((Φ.periodChart i).source ∩ (Φ.periodChart j).source) :=
    (Φ.periodChart j).continuousOn.mono Set.inter_subset_right
  exact (hj.domRestrict.sub hi.domRestrict).congr
    (fun z => (Φ.periodChartDifference_val i j z.val z.property).symm)

end

end OAI.RepresentationTheory.Theta.Geometric
