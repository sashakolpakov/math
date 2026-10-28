import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredSmoothFibers

/-! # Fiber Cartesian Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberCartesianComparison

noncomputable section

/-! Smoothness of corresponding fibers is equivalent in every Cartesian square, by extension and reflection over the residue fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_fiber_iff_of_isPullback
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) (t : T) :
    Smooth (p.fiberToSpecResidueField t) ↔ Smooth (f.fiberToSpecResidueField (c t)) := by
  constructor
  · intro hp
    have : Smooth (p.fiberToSpecResidueField t) := hp
    have : Flat (Spec.map (c.residueFieldMap t)) := FieldExtensionReflection.fieldSpecMap_flat (c.residueFieldMap t)
    have : Surjective (Spec.map (c.residueFieldMap t)) := FieldExtensionReflection.fieldSpecMap_surjective (c.residueFieldMap t)
    exact FpqcReflection.smooth_of_isPullback_fpqc _ (p.fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (c t)) (Spec.map (c.residueFieldMap t))
      (isPullback_fiberToSpecResidueField_of_isPullback h t)
  · intro hf
    exact MorphismProperty.of_isPullback (P := @Smooth)
      (isPullback_fiberToSpecResidueField_of_isPullback h t) hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberCartesianComparison
