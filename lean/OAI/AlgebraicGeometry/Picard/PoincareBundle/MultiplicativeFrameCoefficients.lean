import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

/-! # Multiplicative Frame Coefficients -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients

noncomputable section

/-! The regular unit coefficients of multiplication in chosen line frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The invertible coefficient of a bilinear product in three actual sheaf frames. -/
def coefficient (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (Bilinear.BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P) :
    Γ(X, ⊤)ˣ := Line.FrameUnits.frameRatio (Bilinear.ProductFrames.productFrame β s t) v

/-- The coefficient gives the bilinear product of the two frame sections. -/
theorem coefficient_action (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (Bilinear.BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P) :
    β.app ⊤ (s.hom.app ⊤ (1 : Γ(X, ⊤))) (t.hom.app ⊤ (1 : Γ(X, ⊤))) =
      (coefficient β s t v : Γ(X, ⊤)) • v.hom.app ⊤ (1 : Γ(X, ⊤)) := by
  rw [← Bilinear.ProductFrames.productFrame_app]
  exact FrameRatioMultiplication.frameRatio_action (Bilinear.ProductFrames.productFrame β s t) v

/-- Equality after multiplying a frame section detects equality of regular functions. -/
theorem scalar_eq_of_frame {M : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M)
    {a b : Γ(X, ⊤)}
    (h : a • s.hom.app ⊤ (1 : Γ(X, ⊤)) = b • s.hom.app ⊤ (1 : Γ(X, ⊤))) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (s.hom.app ⊤)).injective
  exact (Line.FrameUnits.unit_hom_app s.hom ⊤ a).trans (h.trans (Line.FrameUnits.unit_hom_app s.hom ⊤ b).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients
