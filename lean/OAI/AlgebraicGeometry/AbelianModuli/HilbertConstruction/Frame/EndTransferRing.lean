import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransfer

/-! # End Transfer Ring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransferRing

noncomputable section

/-! Transfer along rank-one frames respects the endomorphism ring operations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

def frameTransferEndRingHom (e : Line.Bundles.structureModule X ≅ M) (d : Line.Bundles.structureModule X ≅ N) :
    End M →+* End N where
  toFun := EndTransfer.frameTransferEnd e d
  map_one' := by
    change EndTransfer.frameTransferEnd e d (𝟙 M) = 𝟙 N
    simp only [EndTransfer.frameTransferEnd, LineBundle.EndScalars.framedEndScalar, Category.id_comp, Iso.hom_inv_id,
      Iso.inv_hom_id]
  map_mul' φ ψ := by
    change EndTransfer.frameTransferEnd e d (ψ ≫ φ) = EndTransfer.frameTransferEnd e d ψ ≫ EndTransfer.frameTransferEnd e d φ
    simp only [EndTransfer.frameTransferEnd, LineBundle.EndScalars.framedEndScalar, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  map_zero' := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    simp [EndTransfer.frameTransferEnd, LineBundle.EndScalars.framedEndScalar]
  map_add' φ ψ := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    change d.hom.app U (e.inv.app U
      (φ.app U (e.hom.app U (d.inv.app U x)) + ψ.app U (e.hom.app U (d.inv.app U x)))) =
        d.hom.app U (e.inv.app U (φ.app U (e.hom.app U (d.inv.app U x)))) +
          d.hom.app U (e.inv.app U (ψ.app U (e.hom.app U (d.inv.app U x))))
    rw [map_add, map_add]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransferRing
