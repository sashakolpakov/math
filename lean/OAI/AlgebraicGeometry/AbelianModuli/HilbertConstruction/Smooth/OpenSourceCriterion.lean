import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Open Source Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.OpenSourceCriterion

noncomputable section

/-! An open subscheme contained in the source smooth locus is smooth over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_open_source_of_le_smoothLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : U ≤ f.smoothLocus) : Smooth (U.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_le_iff.mp
  intro x _
  exact hU x.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.OpenSourceCriterion
