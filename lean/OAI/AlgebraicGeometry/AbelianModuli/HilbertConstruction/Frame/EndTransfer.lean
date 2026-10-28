import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndScalars

/-! # End Transfer -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransfer

noncomputable section

/-! Transfer a rank-one endomorphism to another framed rank-one module, independently of both frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M N P Q : X.Modules}

def frameTransferEnd (e : Line.Bundles.structureModule X ≅ M) (d : Line.Bundles.structureModule X ≅ N) (φ : End M) :
    End N := d.inv ≫ LineBundle.EndScalars.framedEndScalar e φ ≫ d.hom

theorem framedEndScalar_unframe (d : Line.Bundles.structureModule X ≅ N) (a : End (Line.Bundles.structureModule X)) :
    LineBundle.EndScalars.framedEndScalar d (d.inv ≫ a ≫ d.hom) = a := by
  simp only [LineBundle.EndScalars.framedEndScalar, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem frameTransferEnd_independent (e e' : Line.Bundles.structureModule X ≅ M)
    (d d' : Line.Bundles.structureModule X ≅ N) (φ : End M) :
    frameTransferEnd e d φ = frameTransferEnd e' d' φ := by
  apply LineBundle.EndScalars.framedEndScalar_injective d'
  calc
    _ = LineBundle.EndScalars.framedEndScalar d (frameTransferEnd e d φ) :=
      LineBundle.EndScalars.framedEndScalar_independent d' d _
    _ = LineBundle.EndScalars.framedEndScalar e φ := framedEndScalar_unframe d _
    _ = LineBundle.EndScalars.framedEndScalar e' φ := LineBundle.EndScalars.framedEndScalar_independent e e' φ
    _ = _ := (framedEndScalar_unframe d' _).symm

theorem frameTransferEnd_transport (e : Line.Bundles.structureModule X ≅ M) (d : Line.Bundles.structureModule X ≅ N)
    (c : M ≅ P) (b : N ≅ Q) (φ : End M) :
    frameTransferEnd (e ≪≫ c) (d ≪≫ b) (c.inv ≫ φ ≫ c.hom) =
      b.inv ≫ frameTransferEnd e d φ ≫ b.hom := by
  simp only [frameTransferEnd, LineBundle.EndScalars.framedEndScalar, Iso.trans_hom, Iso.trans_inv, Category.assoc,
    Iso.hom_inv_id_assoc]

theorem frameTransferEnd_pullback (f : Y ⟶ X) (e : Line.Bundles.structureModule X ≅ M)
    (d : Line.Bundles.structureModule X ≅ N) (φ : End M) :
    frameTransferEnd (LineBundle.EndScalars.pulledBackFrame f e) (LineBundle.EndScalars.pulledBackFrame f d)
      ((Scheme.Modules.pullback f).map φ) = (Scheme.Modules.pullback f).map (frameTransferEnd e d φ) := by
  unfold frameTransferEnd
  rw [LineBundle.EndScalars.framedEndScalar_pullback]
  simp only [LineBundle.EndScalars.pulledBackFrame, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransfer
