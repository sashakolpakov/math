import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullback

/-! # Trilinear Composition Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearCompositionPullback.Construction

noncomputable section

/-! Pulling back either actual composite of two bilinear line maps
agrees with composing their geometric pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N P MN NP Q : Y.Modules}

set_option backward.isDefEq.respectTransparency false in
theorem lineBilinearComposeLeft_pullback
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (hMN : Picard.PoincareBundle.Line.Bundles.IsLine MN) (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q) :
    TrilinearPullback.Construction.lineTrilinearPullback f hM hN hP (TrilinearProducts.Construction.lineBilinearComposeLeft b c) =
      TrilinearProducts.Construction.lineBilinearComposeLeft (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN b) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hMN hP c) := by
  apply TrilinearPullbackDetection.Construction.trilinear_eq_of_pullback_units f M N P hM hN hP
  intro U m n p
  simp only [TrilinearPullback.Construction.lineTrilinearPullback_app_units, TrilinearProducts.Construction.lineBilinearComposeLeft_app, TrilinearPullbackDetection.Construction.bilinearPullback_app_units]

set_option backward.isDefEq.respectTransparency false in
theorem lineBilinearComposeRight_pullback
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (hNP : Picard.PoincareBundle.Line.Bundles.IsLine NP) (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N P NP) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M NP Q) :
    TrilinearPullback.Construction.lineTrilinearPullback f hM hN hP (TrilinearProducts.Construction.lineBilinearComposeRight b c) =
      TrilinearProducts.Construction.lineBilinearComposeRight (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hN hP b) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hNP c) := by
  apply TrilinearPullbackDetection.Construction.trilinear_eq_of_pullback_units f M N P hM hN hP
  intro U m n p
  simp only [TrilinearPullback.Construction.lineTrilinearPullback_app_units, TrilinearProducts.Construction.lineBilinearComposeRight_app, TrilinearPullbackDetection.Construction.bilinearPullback_app_units]

theorem lineTrilinearToHom_composeLeft (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q) :
    TrilinearPullback.Construction.lineTrilinearToHom (TrilinearProducts.Construction.lineBilinearComposeLeft b c) = Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (𝟙 P) ≫ Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c := by
  rw [TrilinearPullback.Construction.lineTrilinearToHom, ← TrilinearProducts.Construction.lineBilinearComposeLeft_tensor b c, Equiv.symm_apply_apply]

instance lineTrilinearToHom_composeLeft_isIso
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q) [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)] :
    IsIso (TrilinearPullback.Construction.lineTrilinearToHom (TrilinearProducts.Construction.lineBilinearComposeLeft b c)) := by
  rw [lineTrilinearToHom_composeLeft]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearCompositionPullback.Construction
