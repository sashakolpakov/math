import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

/-! # Frame Ratio Multiplication -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication

noncomputable section

/-!
# Bilinear multiplication multiplies the actual unit ratios of frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The unit ratio acts on one frame to give the other frame. -/
theorem frameRatio_action (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) :
    s.hom.app ⊤ (1 : Γ(X, ⊤)) =
      (Line.FrameUnits.frameRatio s t : Γ(X, ⊤)) • t.hom.app ⊤ (1 : Γ(X, ⊤)) := by
  have h := congrArg (fun a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M => a.app ⊤ (1 : Γ(X, ⊤)))
    (show (s.hom ≫ t.inv) ≫ t.hom = s.hom by simp only [Category.assoc, t.inv_hom_id, Category.comp_id])
  exact h.symm.trans (Line.FrameUnits.unit_hom_app t.hom ⊤ (Line.FrameUnits.frameRatio s t))

/-- The ratios of product frames are products of the input ratios. -/
theorem frameRatio_product (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (s s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t t' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N)
    (r r' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (hr : β.app ⊤ (s.hom.app ⊤ (1 : Γ(X, ⊤))) (t.hom.app ⊤ (1 : Γ(X, ⊤))) =
      r.hom.app ⊤ (1 : Γ(X, ⊤)))
    (hr' : β.app ⊤ (s'.hom.app ⊤ (1 : Γ(X, ⊤))) (t'.hom.app ⊤ (1 : Γ(X, ⊤))) =
      r'.hom.app ⊤ (1 : Γ(X, ⊤))) :
    Line.FrameUnits.frameRatio r r' = Line.FrameUnits.frameRatio s s' * Line.FrameUnits.frameRatio t t' := by
  apply Units.ext
  change (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp r'.inv ⊤) (r.hom.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [← hr, frameRatio_action s s', frameRatio_action t t']
  simp only [map_smul, LinearMap.smul_apply, hr', smul_smul]
  have h := congrArg (fun a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X => a.app ⊤ (1 : Γ(X, ⊤)))
    r'.hom_inv_id
  change r'.inv.app ⊤ (r'.hom.app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) at h
  erw [h]
  change ((Line.FrameUnits.frameRatio t t' : Γ(X, ⊤)) * (Line.FrameUnits.frameRatio s s' : Γ(X, ⊤))) * 1 =
    (Line.FrameUnits.frameRatio s s' : Γ(X, ⊤)) * (Line.FrameUnits.frameRatio t t' : Γ(X, ⊤))
  rw [mul_one, mul_comm]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication
