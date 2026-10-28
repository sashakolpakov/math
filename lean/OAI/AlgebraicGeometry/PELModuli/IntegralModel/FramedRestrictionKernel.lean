import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import Mathlib.Algebra.GroupWithZero.Action.Units

/-! # Framed Restriction Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedRestrictionKernel

noncomputable section

/-! Vanishing under a structure-module map is independent of an
invertible change of source frame, over arbitrary base rings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
universe u
variable {X : Scheme.{u}} {M P : X.Modules}

theorem structureMap_frame_zero_iff (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (r : Γ(X, ⊤)) :
    q.app ⊤ (e.hom.app ⊤ r) = 0 ↔ q.app ⊤ r = 0 := by
  have hu : IsUnit (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X e.hom) :=
    (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff e.hom).mp inferInstance
  rw [AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app]
  change q.app ⊤ (r * AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X e.hom) = 0 ↔ _
  rw [mul_comm r]
  change q.app ⊤ (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X e.hom • r) = 0 ↔ _
  rw [q.app_smul]
  exact hu.smul_eq_zero

theorem restriction_kernel_frame_independent (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (e d : P ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (x : Γ(P, ⊤)) :
    q.app ⊤ (e.hom.app ⊤ x) = 0 ↔ q.app ⊤ (d.hom.app ⊤ x) = 0 := by
  let a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X := d.symm ≪≫ e
  have he : e.hom = d.hom ≫ a.hom := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [he]
  exact structureMap_frame_zero_iff q a (d.hom.app ⊤ x)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedRestrictionKernel
