import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.AlgebraicGeometry.Fiber

/-! # Recovered Smooth Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredSmoothFibers

noncomputable section

/-! A smooth Cartesian recovery forces the original fibers at all recovered base points to be smooth. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem smooth_fiber_of_smooth_baseChange
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) [Smooth p] (t : T) : Smooth (f.fiberToSpecResidueField (c t)) := by
  have : Smooth (p.fiberToSpecResidueField t) :=
    inferInstanceAs (Smooth (pullback.snd p (T.fromSpecResidueField t)))
  have : Flat (Spec.map (c.residueFieldMap t)) := HilbertConstruction.Smooth.FieldExtensionReflection.fieldSpecMap_flat (c.residueFieldMap t)
  have : Surjective (Spec.map (c.residueFieldMap t)) := HilbertConstruction.Smooth.FieldExtensionReflection.fieldSpecMap_surjective (c.residueFieldMap t)
  exact HilbertConstruction.Smooth.FpqcReflection.smooth_of_isPullback_fpqc _ (p.fiberToSpecResidueField t)
    (f.fiberToSpecResidueField (c t)) (Spec.map (c.residueFieldMap t))
    (isPullback_fiberToSpecResidueField_of_isPullback h t)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredSmoothFibers
