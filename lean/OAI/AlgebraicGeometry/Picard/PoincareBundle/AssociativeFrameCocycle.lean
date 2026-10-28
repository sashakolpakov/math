import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients

/-! # Associative Frame Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AssociativeFrameCocycle

noncomputable section

/-! Associativity of actual bilinear line multiplication gives the scalar two-cocycle law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients

variable {X : Scheme.{u}} {K L M N P Q : X.Modules}
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K L M) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L N P)
  (δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K P Q) (ε : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N Q)
  [IsIso (Bilinear.BilinearPullback.toHom β)] [IsIso (Bilinear.BilinearPullback.toHom γ)]
  [IsIso (Bilinear.BilinearPullback.toHom δ)] [IsIso (Bilinear.BilinearPullback.toHom ε)]
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ K) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ L) (r : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N)
  (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (w : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ Q)

/-- No reducedness is used: the equality holds in the ring of regular functions itself. -/
theorem coefficient_cocycle
    (hassoc : ∀ (a : Γ(K, ⊤)) (b : Γ(L, ⊤)) (c : Γ(N, ⊤)),
      δ.app ⊤ a (γ.app ⊤ b c) = ε.app ⊤ (β.app ⊤ a b) c) :
    MultiplicativeFrameCoefficients.coefficient δ s w z * MultiplicativeFrameCoefficients.coefficient γ t r w = MultiplicativeFrameCoefficients.coefficient ε v r z * MultiplicativeFrameCoefficients.coefficient β s t v := by
  apply Units.ext
  apply MultiplicativeFrameCoefficients.scalar_eq_of_frame z
  have h := hassoc (s.hom.app ⊤ (1 : Γ(X, ⊤))) (t.hom.app ⊤ (1 : Γ(X, ⊤))) (r.hom.app ⊤ (1 : Γ(X, ⊤)))
  rw [MultiplicativeFrameCoefficients.coefficient_action γ t r w, MultiplicativeFrameCoefficients.coefficient_action β s t v] at h
  have hr := (δ.app ⊤ (s.hom.app ⊤ (1 : Γ(X, ⊤)))).map_smul
    (MultiplicativeFrameCoefficients.coefficient γ t r w : Γ(X, ⊤)) (w.hom.app ⊤ (1 : Γ(X, ⊤)))
  have hl := LinearMap.congr_fun ((ε.app ⊤).map_smul
    (MultiplicativeFrameCoefficients.coefficient β s t v : Γ(X, ⊤)) (v.hom.app ⊤ (1 : Γ(X, ⊤)))) (r.hom.app ⊤ (1 : Γ(X, ⊤)))
  erw [hr, hl] at h
  erw [LinearMap.smul_apply, MultiplicativeFrameCoefficients.coefficient_action δ s w z,
    MultiplicativeFrameCoefficients.coefficient_action ε v r z, smul_smul, smul_smul] at h
  simpa only [Units.val_mul, mul_comm] using h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AssociativeFrameCocycle
