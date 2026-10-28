import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle

/-! # Frame Pullback Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.FramePullbackUnit

noncomputable section

/-! The units used in the fixed-fiber logarithmic cocycle are exactly
the pullbacks of the original family frame transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R))) {I : Type} (U : I → X.left.Opens)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions U)

theorem fixedFiberFrameReducedUnit_original
    (V : X.left.affineOpens) (i j : I) (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) :
    Units.map (RegularSections.fixedFiberRegularSectionEquiv R k X V).toMonoidHom
      (LineLogCocycle.fixedFiberFrameReducedUnit R k X U D V i j hi hj) =
    Units.map ((CoordinateProjection.fixedFamilyProjection R k X).app V.1).hom.toMonoidHom
      (D.value V.1 i j hi hj) := by
  apply Units.ext
  change RegularSections.fixedFiberRegularSectionEquiv R k X V
    ((1 : k) ⊗ₜ[R] (Family.FrameCoordinateUnits.familyFrameCoordinateUnit R X U D V i j hi hj).val) =
      (CoordinateProjection.fixedFamilyProjection R k X).app V.1 (D.value V.1 i j hi hj).val
  rw [SectionPullback.fixedFiberRegularSectionEquiv_includeRight]
  change (CoordinateProjection.fixedFamilyProjection R k X).app V.1
    (Family.FrameCoordinateUnits.familyAffineSectionEquiv R X V
      ((Family.FrameCoordinateUnits.familyAffineSectionEquiv R X V).symm (D.value V.1 i j hi hj).val)) = _
  rw [RingEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.FramePullbackUnit
