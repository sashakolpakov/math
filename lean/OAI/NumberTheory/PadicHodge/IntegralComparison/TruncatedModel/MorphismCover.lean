import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution

/-! # Morphism Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover

noncomputable section

/-! A finite family of compatible affine pairs covers the source and refines both original model coordinate covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] (u : X₁ ⟶ X₂)
local instance sourceCompact : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace X₁.hom

def refinement := AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement.FiniteAffineMapRefinement.ofCompact u.left
  (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₂) (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₁)
  (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₂) (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₁)
abbrev Index : Type := Fin (Fintype.card (refinement p k n u).Index)
def nativeIndex (i : MorphismCover.Index p k n u) : (refinement p k n u).Index := (Fintype.equivFin (refinement p k n u).Index).symm i

def sourceIndex (i : MorphismCover.Index p k n u) : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X₁ :=
  (Fintype.equivFin (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₁)) ((refinement p k n u).index (nativeIndex p k n u i)).2
def targetIndex (i : MorphismCover.Index p k n u) : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X₂ :=
  (Fintype.equivFin (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₂)) ((refinement p k n u).index (nativeIndex p k n u i)).1

def opens (i : MorphismCover.Index p k n u) : X₁.left.affineOpens :=
  ⟨(refinement p k n u).opens (nativeIndex p k n u i), (refinement p k n u).affine (nativeIndex p k n u i)⟩

omit [Fintype k] [CharP k p] in
theorem le_source (i : MorphismCover.Index p k n u) : (MorphismCover.opens p k n u i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X₁ (sourceIndex p k n u i)).val := by
  simpa only [MorphismCover.opens, AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens, AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex, sourceIndex, refinement,
    Equiv.symm_apply_apply] using
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement.FiniteAffineMapRefinement.le_target u.left _ _ (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₂)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₁) (nativeIndex p k n u i))

omit [Fintype k] [CharP k p] in
theorem le_preimage (i : MorphismCover.Index p k n u) : (MorphismCover.opens p k n u i).val ≤
    u.left ⁻¹ᵁ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X₂ (targetIndex p k n u i)).val := by
  simpa only [MorphismCover.opens, AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens, AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex, targetIndex, refinement,
    Equiv.symm_apply_apply] using
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement.FiniteAffineMapRefinement.le_source u.left _ _ (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₂)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover (Truncated.Witt.Ring p k n) X₁) (nativeIndex p k n u i))

def pairs (i : MorphismCover.Index p k n u) : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left :=
  ⟨(MorphismCover.opens p k n u i, AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X₂ (targetIndex p k n u i)), le_preimage p k n u i⟩

omit [Fintype k] [CharP k p] in
theorem cover : (⨆ i, (MorphismCover.opens p k n u i).val) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ ⨆ i, (refinement p k n u).opens i := by rw [(refinement p k n u).cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨(Fintype.equivFin (refinement p k n u).Index) i, ?_⟩
  simpa only [MorphismCover.opens, nativeIndex, Equiv.symm_apply_apply] using hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover
