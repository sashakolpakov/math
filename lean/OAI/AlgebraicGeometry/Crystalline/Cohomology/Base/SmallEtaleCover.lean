import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts

/-! # Small Etale Cover -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover

noncomputable section

/-! A small finite indexing of the actual model coordinate cover, retaining its original charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]

abbrev Index : Type := Fin (Fintype.card (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X))

def originalIndex (i : Index R X) : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X :=
  (Fintype.equivFin (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)).symm i

def opens (i : Index R X) : X.left.affineOpens :=
  ⟨ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X (originalIndex R X i),
    ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X (originalIndex R X i)⟩

theorem covers (x : X.left) : ∃ i : Index R X, x ∈ (opens R X i).val := by
  have hx : x ∈ ⨆ i, ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i := by
    rw [ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(Fintype.equivFin (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)) i, ?_⟩
  simpa only [opens, originalIndex, Equiv.symm_apply_apply] using hi

theorem cover : (⨆ i, (opens R X i).val) = ⊤ := by
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr (covers R X x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover
