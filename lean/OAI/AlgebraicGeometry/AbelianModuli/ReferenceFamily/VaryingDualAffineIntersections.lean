import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Varying Dual Affine Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualAffineIntersections

noncomputable section

/-! Affine intersections of a separated varying dual-number family,
and their actual reduced affine opens, require no product assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k)))) [IsSeparated X.hom]

theorem varyingDualFamily_affineDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from X.left)) := by
  have : IsSeparated (terminal.from (Spec (.of (DualNumber k)))) := inferInstance
  have h : IsSeparated (X.hom ≫ terminal.from (Spec (.of (DualNumber k)))) := inferInstance
  have he : X.hom ≫ terminal.from (Spec (.of (DualNumber k))) = terminal.from X.left :=
    Subsingleton.elim _ _
  have : IsSeparated (terminal.from X.left) := he ▸ h
  infer_instance

theorem varyingDualFamily_affineIntersection (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := varyingDualFamily_affineDiagonal k X
  exact hU.inf hV

theorem varyingDualFamily_finiteAffineIntersection {ι : Sort*} [Finite ι] [Nonempty ι]
    (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) : IsAffineOpen (⨅ i, U i) := by
  have := varyingDualFamily_affineDiagonal k X
  exact IsAffineOpen.iInf hU

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualAffineIntersections
