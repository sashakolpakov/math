import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedSectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonzero line-bundle section on a reduced scheme locally of finite type over an algebraically closed field is a frame at an actual rational point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Line.Bundles.LineBundle.exists_rational_frame_of_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsReduced X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ IsIso (Ample.LineBundles.pullbackSection x s) := by
  obtain ⟨y, hy⟩ := L.exists_nonvanishing_of_ne_zero s hs
  let U := Ample.LineBundles.sectionNonvanishing s
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨a, ha⟩ := ClosedRationalPoints.nonempty_locallyFiniteType_exists_section (U.ι ≫ p)
  refine ⟨a ≫ U.ι, (Category.assoc a U.ι p).trans ha, ?_⟩
  have : IsIso (Ample.LineBundles.pullbackSection a (Ample.LineBundles.pullbackSection U.ι s)) := inferInstance
  exact (Section.Nonvanishing.isIso_pullbackSection_comp_iff U.ι a s).mp inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
