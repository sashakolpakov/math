import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SmoothPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Cone Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeDimension

noncomputable section

/-! The native dimension of the projective cone is the dimension
of its base support plus the relative dimension of the ambient projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem dimension {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ConeSupport.support L hL η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) =
      (n - m) + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Cone.SmoothPullback.baseSupport η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) := by
  let f := Cone.SmoothPullback.base L η
  let r := (n - m) + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Cone.SmoothPullback.baseSupport η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
  let : SmoothOfRelativeDimension r f := Cone.SmoothPullback.relativeDimension L hL η
  obtain ⟨x, hx⟩ := Cone.SmoothPullback.generic_in_range L hL η
  obtain ⟨U, hxU, hU, hs⟩ := Grading.SmoothIntegralNeighborhood.exists_open f r x
  let := hU
  let := hs
  let : NoetherianSpace (U : Scheme) := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let j : (U : Scheme) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := U.ι ≫ Cone.SmoothPullback.inclusion L η
  have hr : Set.range j ⊆ (ConeSupport.support L hL η : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
    rintro _ ⟨z, rfl⟩
    exact Cone.SmoothPullback.range_subset L hL η ⟨U.ι z, rfl⟩
  have hη : ConeSupport.genericPoint L hL η ∈ Set.range j := ⟨⟨x, hxU⟩, hx⟩
  have he : CycleClass.Geometric.StratumClosure.integralImageClosure j = ConeSupport.support L hL η := by
    apply IrreducibleCloseds.ext
    apply Set.Subset.antisymm
    · exact closure_minimal hr (ConeSupport.support L hL η).isClosed
    · exact closure_mono (Set.singleton_subset_iff.mpr hη)
  have hd := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure j (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  rw [he] at hd
  have hj : j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = U.ι ≫ f := by
    dsimp only [j]
    rw [Category.assoc, Cone.SmoothPullback.over_base]
  rw [hj] at hd
  exact hd.symm.trans (Grading.integral_dimension_of_relativeDimension (U.ι ≫ f) r)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeDimension
