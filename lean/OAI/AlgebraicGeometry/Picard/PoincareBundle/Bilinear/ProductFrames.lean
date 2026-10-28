import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication

/-! # Product Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames

noncomputable section

/-!
# Actual products of line frames and uniqueness of an invertible idempotent frame
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- An invertible bilinear map takes two actual frames to a frame of the output line. -/
def productFrame (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P :=
  t ≪≫ asIso (Contraction.contractLeft β s.hom)

/-- The product frame is precisely the bilinear product on every open set. -/
theorem productFrame_app (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (U : X.Opens) :
    (productFrame β s t).hom.app U (1 : Γ(X, U)) =
      β.app U (s.hom.app U (1 : Γ(X, U))) (t.hom.app U (1 : Γ(X, U))) :=
  Contraction.contractLeft_app β s.hom U (t.hom.app U (1 : Γ(X, U)))

/-- Two invertible idempotent frames of the same bilinear line multiplication coincide. -/
theorem idempotent_frame_unique (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M M M)
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M)
    (hs : β.app ⊤ (s.hom.app ⊤ (1 : Γ(X, ⊤))) (s.hom.app ⊤ (1 : Γ(X, ⊤))) =
      s.hom.app ⊤ (1 : Γ(X, ⊤)))
    (ht : β.app ⊤ (t.hom.app ⊤ (1 : Γ(X, ⊤))) (t.hom.app ⊤ (1 : Γ(X, ⊤))) =
      t.hom.app ⊤ (1 : Γ(X, ⊤))) : s = t := by
  have h := FrameRatioMultiplication.frameRatio_product β s t s t s t hs ht
  apply (Line.FrameUnits.frameRatio_eq_one_iff s t).mp
  exact (mul_left_cancel ((mul_one (Line.FrameUnits.frameRatio s t)).trans h)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
